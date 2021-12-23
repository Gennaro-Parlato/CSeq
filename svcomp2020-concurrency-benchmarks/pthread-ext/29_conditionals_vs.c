#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int m = 0;
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
void* thr1(void* arg)
{
 int x;
 int y;
 x = __VERIFIER_nondet_int();
 y = __VERIFIER_nondet_int();
 int z;
 __VERIFIER_atomic_acquire();
 if(x == y)
 {
  z = 0;
 } else {
  z = 1;
 }
 if(z == 0)
 {
  { if(!(x == y)) { goto ERROR; } };
 } else {
  { if(!(x != y)) { ERROR: {reach_error();abort();}(void)0; } };
 }
 __VERIFIER_atomic_release();
 return 0;
}
int main()
{
  pthread_t t;
 while(1)
 {
   pthread_create(&t, 0, thr1, 0);
 }
}
