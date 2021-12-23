#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int g0 = 0,g1 = 0,x = 0;
_Bool lock = 0;
int mutex = 0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(mutex==0);
 mutex = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(mutex==1);
 mutex = 0;
}
void* thr3(void* arg)
{
  __VERIFIER_atomic_acquire();
  if(__VERIFIER_nondet_int())
  {
    g0=0;
    g1=0;
    lock=0;
  }
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_acquire();
  if(lock)
  {
    x=1;
    { if(!(g0==1 && g1==1)) { ERROR: {reach_error();abort();}(void)0; } };
  }
  __VERIFIER_atomic_release();
  return 0;
}
void* thr2(void* arg)
{
  { while(1) { __VERIFIER_atomic_acquire(); { if(!(g0==g1)) { ERROR: {reach_error();abort();}(void)0; } }; __VERIFIER_atomic_release(); }};
  return 0;
}
void* thr1(void* arg)
{
  __VERIFIER_atomic_acquire();
  g0=1,g1=1;
  __VERIFIER_atomic_release();
  lock=1;
  return 0;
}
int main() {
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr2, 0);
  while(1)
  {
    pthread_create(&t, 0, thr3, 0);
  }
}
