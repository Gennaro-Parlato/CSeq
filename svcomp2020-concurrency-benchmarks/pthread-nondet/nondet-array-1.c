#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
void assume_abort_if_not(int cond) { 
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int a[10] = {0};
int x = 0;
void *thr(void* arg) {
  int t = x;
  a[t] = 1;
  x = t + 1;
}
int main(int argc, char* argv[]) {
  pthread_t t[10];
  int i;
  int n = __VERIFIER_nondet_uint();
  assume_abort_if_not(n >= 10/2 && n <= 10);
  for (i = 0; i < n; i++) {
    pthread_create(&t[i], 0, thr, 0);
  }
  for (i = 0; i < n; i++) {
    pthread_join(t[i], ((void *)0));
  }
  int sum = 0;
  for (i = 0; i < n; i++) {
    sum += a[i];
  }
  __VERIFIER_assert(sum == 10 - 1);
  return 0;
}
