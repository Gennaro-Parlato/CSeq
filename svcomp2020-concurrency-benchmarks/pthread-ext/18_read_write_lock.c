#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int w=0, r=0, x, y;
void __VERIFIER_atomic_w()
{
    assume_abort_if_not(w==0);
    assume_abort_if_not(r==0);
    w = 1;
}
void* thr1(void* arg) {
  __VERIFIER_atomic_w();
  x = 3;
  w = 0;
  return 0;
}
void __VERIFIER_atomic_r()
{
    assume_abort_if_not(w==0);
    r = r+1;
}
void* thr2(void* arg) {
  __VERIFIER_atomic_r();
  y = x;
  { if(!(y == x)) { ERROR: {reach_error();abort();}(void)0; } };
  r = r-1;
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  thr2(0);
  return 0;
}
