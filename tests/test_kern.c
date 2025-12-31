#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

#include "exokernel.h"
#include "fs_server.h"
#include "ipc.h"
#include "libvm.h"
#include "proc_manager.h"

/**
 * @brief Drain one message from the kernel request queue and validate its type.
 *
 * The microkernel stubs enqueue requests on @p kern_ipc_queue before deferring
 * to their fallback implementations.  Test code consumes the request to ensure
 * that the IPC path is exercised even when no user-space server is listening.
 *
 * @param expected Type of message anticipated on the queue.
 * @param captured Optional pointer that receives the dequeued message.
 * @return true when a message of the expected type is observed; false
 *         otherwise.
 */
static bool dequeue_expected(enum ipc_msg_type expected,
                             struct ipc_message *captured) {
    struct ipc_message msg = {0};
    if (ipc_queue_recv(&kern_ipc_queue, &msg) != EXO_IPC_OK)
        return false;
    if (msg.type != (uint32_t)expected)
        return false;
    if (captured != NULL)
        *captured = msg;
    return true;
}

/** Ensure no stale messages linger on the shared kernel queue. */
static void discard_residual_messages(void) {
    struct ipc_message msg;
    while (ipc_queue_recv(&kern_ipc_queue, &msg) == EXO_IPC_OK) {
        /* Intentionally empty: drop unexpected or outdated traffic. */
    }
}

int main(void) {
    /*
     * The scheduler normally allocates mailboxes and IPC queues during boot.
     * The test harness runs in isolation, so bootstrap both facilities here.
     */
    ipc_queue_init(&kern_ipc_queue);
    ipc_mailbox_init();

    struct ipc_mailbox *self = ipc_mailbox_current();
    if (self == NULL) {
        fputs("ipc_mailbox_current() failed to allocate a mailbox\n", stderr);
        return EXIT_FAILURE;
    }

    struct ipc_message unused;
    if (ipc_queue_recv(&self->queue, &unused) != EXO_IPC_EMPTY) {
        fputs("expected the process mailbox queue to start empty\n", stderr);
        return EXIT_FAILURE;
    }

    /*
     * Exercise kern_open(): even without a file server, the stub must
     * enqueue an IPC request and fall back to the in-process fs_open().
     */
    int fd = kern_open("README.md", O_RDONLY);
    if (fd < 0) {
        perror("kern_open");
        return EXIT_FAILURE;
    }
    close(fd);

    struct ipc_message open_msg;
    if (!dequeue_expected(IPC_MSG_OPEN, &open_msg)) {
        fputs("kern_open() did not emit the expected IPC message\n", stderr);
        return EXIT_FAILURE;
    }

    /*
     * Exercise kern_vm_fault(): the mock VM library always succeeds, so the
     * stub should return true after logging the faulting address.
     */
    int sentinel = 0;
    if (!kern_vm_fault(&sentinel)) {
        fputs("kern_vm_fault() reported failure despite the mock handler\n",
              stderr);
        return EXIT_FAILURE;
    }

    struct ipc_message vm_msg;
    if (!dequeue_expected(IPC_MSG_VM_FAULT, &vm_msg)) {
        fputs("kern_vm_fault() did not enqueue its IPC request\n", stderr);
        return EXIT_FAILURE;
    }
    if (vm_msg.a != (uintptr_t)&sentinel) {
        fputs("kern_vm_fault() reported an unexpected fault address\n",
              stderr);
        return EXIT_FAILURE;
    }

    /*
     * Exercise kern_fork(): the process manager stub calls fork().
     * The parent waits for the child to exit cleanly.
     */
    pid_t child = kern_fork();
    if (child < 0) {
        perror("kern_fork");
        return EXIT_FAILURE;
    }
    if (child == 0) {
        /* Child process: exit immediately to signal success to the parent. */
        _exit(EXIT_SUCCESS);
    }

    int status = 0;
    if (waitpid(child, &status, 0) < 0) {
        perror("waitpid");
        return EXIT_FAILURE;
    }
    if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_SUCCESS) {
        fputs("child spawned by kern_fork() did not exit cleanly\n", stderr);
        return EXIT_FAILURE;
    }

    if (!dequeue_expected(IPC_MSG_PROC_FORK, NULL)) {
        fputs("kern_fork() failed to log its IPC notification\n", stderr);
        return EXIT_FAILURE;
    }

    discard_residual_messages();

    puts("all ok");
    return EXIT_SUCCESS;
}
