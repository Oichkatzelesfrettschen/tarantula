#include "spinlock.hpp"
#include <array>
#include <thread>
#include <iostream>

SpinLock g_lock;
int counter = 0;

void worker()
{
    for (int i = 0; i < 1000; ++i)
        with_lock(g_lock, [] { ++counter; });
}

int main()
{
    {
        std::array<std::jthread, 4> threads;
        for (auto& t : threads)
            t = std::jthread(worker);
    } // threads join here
    if (counter != 4000) {
        std::cout << "spinlock failed\n";
        return 1;
    }
    std::cout << "spinlock ok\n";
    return 0;
}
