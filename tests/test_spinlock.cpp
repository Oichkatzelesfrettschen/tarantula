#include "spinlock.hpp"
#include <thread>
#include <vector>
#include <iostream>

SpinLock g_lock;
int counter = 0;

void worker()
{
    for(int i=0;i<1000;i++)
        with_lock(g_lock, []{ ++counter; });
}

int main()
{
    std::vector<std::thread> threads;
    for(int i=0;i<4;i++)
        threads.emplace_back(worker);
    for(auto& t : threads)
        t.join();
    if(counter != 4000) {
        std::cout << "spinlock failed\n";
        return 1;
    }
    std::cout << "spinlock ok\n";
    return 0;
}
