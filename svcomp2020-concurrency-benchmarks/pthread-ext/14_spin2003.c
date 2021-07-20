#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int x=1, m=0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(m==0);
 m = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(m==1);
 m = 0;
}
void* thr1(void* arg) {
  __VERIFIER_atomic_acquire();
  x = 0;
  x = 1;
  { if(!(x>=1)) { ERROR: {reach_error();abort();}(void)0; } };
  __VERIFIER_atomic_release();
  return 0;
}
int main()
{
  pthread_t t;
  while(1) pthread_create(&t, 0, thr1, 0);
}
