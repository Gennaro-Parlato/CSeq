#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
int __VERIFIER_nondet_int();
volatile int x;
void* thr1(void* arg) {
    __VERIFIER_assert(x <= 50);
    return 0;
}
void* thr2(void* arg) {
    int t;
    t = x;
    x = t + 1;
    return 0;
}
int main(int argc, char* argv[]) {
    pthread_t t1, t2;
    int i;
    x = 0;
    pthread_create(&t1, 0, thr1, 0);
    for (i = 0; i < 50; i++) {
 pthread_create(&t2, 0, thr2, 0);
    }
    return 0;
}
