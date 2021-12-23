#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int mutex;
int res;
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
typedef int (*FuncType)(int, int);
inline int f1(int a, int b)
{
  return a+b+1;
}
inline int f2(int x, int y)
{
  return x-y+2;
}
void* thr2(void* arg)
{
  FuncType pf;
  if( __VERIFIER_nondet_int() )
    pf = f1;
  else
    pf = f2;
  __VERIFIER_atomic_acquire();
  res = pf(4,3);
  __VERIFIER_atomic_release();
  return 0;
}
void* thr1(void* arg)
{
  while(1)
  {
    { if(!(res < 10)) { ERROR: {reach_error();abort();}(void)0; } };
  }
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  while(1)
  {
    pthread_create(&t, 0, thr2, 0);
  }
}
