#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile unsigned value, m = 0;
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
void * thr1(void* arg) {
 unsigned v = 0;
 __VERIFIER_atomic_acquire();
 if(value == 0u-1) {
  __VERIFIER_atomic_release();
  return 0;
 }else{
  v = value;
  value = v + 1;
  __VERIFIER_atomic_release();
  { if(!(value > v)) { ERROR: {reach_error();abort();}(void)0; } };
  return 0;
 }
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
