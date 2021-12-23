#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
void assume_abort_if_not(int cond) { 
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
volatile int x;
volatile int n;
pthread_mutex_t mut = { { 0, 0, 0, 0, 0, { { 0, 0 } } } };
void* thr1(void* arg) {
  __VERIFIER_assert(x <= n);
}
void* thr2(void* arg) {
  int t;
  int k = __VERIFIER_nondet_uint();
  assume_abort_if_not(k >= (10/2) && k <= 10);
  pthread_mutex_lock(&mut);
  t = x;
  if (k == n) {
    x = t + 1;
  }
  pthread_mutex_unlock(&mut);
}
int main(int argc, char* argv[]) {
  pthread_t t1, t2;
  x = 0;
  n = __VERIFIER_nondet_uint();
  assume_abort_if_not(n >= (10/2) && n < 10);
  pthread_create(&t1, 0, thr1, 0);
  for (int i = 0; i < n; i++) {
    pthread_create(&t2, 0, thr2, 0);
  }
  return 0;
}
