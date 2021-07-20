#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
int __VERIFIER_nondet_int(void);
void ldv_assert(int expression) { if (!expression) { ERROR: {reach_error();abort();}}; return; }
pthread_t t1;
pthread_mutex_t mutex;
int pdev;
void *thread1(void *arg) {
   pthread_mutex_lock(&mutex);
   pdev = 6;
   pthread_mutex_unlock(&mutex);
   return 0;
}
int module_init() {
   pthread_mutex_init(&mutex, ((void *)0));
   pdev = 1;
   ldv_assert(pdev==1);
   if(__VERIFIER_nondet_int()) {
      pthread_create(&t1, ((void *)0), thread1, ((void *)0));
      return 0;
   }
   pdev = 3;
   ldv_assert(pdev==3);
   pthread_mutex_destroy(&mutex);
   return -1;
}
void module_exit() {
   void *status;
   pdev = 4;
   ldv_assert(pdev==4);
   pthread_join(t1, &status);
   pthread_mutex_destroy(&mutex);
   pdev = 5;
   ldv_assert(pdev==5);
}
int main(void) {
    if(module_init()!=0) goto module_exit;
    module_exit();
module_exit:
    return 0;
}
