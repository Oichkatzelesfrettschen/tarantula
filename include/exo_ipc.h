#ifndef EXO_IPC_H
#define EXO_IPC_H

/* Status codes for exokernel IPC operations */
typedef enum {
    EXO_IPC_OK = 0,
    EXO_IPC_EMPTY,
    EXO_IPC_FULL,
    EXO_IPC_TIMEOUT,
    EXO_IPC_ERROR
} exo_ipc_status;

#endif /* EXO_IPC_H */
