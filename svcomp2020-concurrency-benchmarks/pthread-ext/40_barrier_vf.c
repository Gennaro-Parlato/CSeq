#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile unsigned int count = 0;
_Bool MTX = 0;
__thread _Bool COND = 0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(MTX==0);
 MTX = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(MTX==1);
 MTX = 0;
}
void Barrier2() {
  __VERIFIER_atomic_acquire();
  count++;
  if (count == 3) {
    (COND = 1);
    count = 0; }
  else
    { __VERIFIER_atomic_release(); assume_abort_if_not(COND); COND = 0; __VERIFIER_atomic_acquire(); };
  __VERIFIER_atomic_release(); }
void* thr1(void* arg){
  Barrier2();
  { if(!(0)) { ERROR: {reach_error();abort();}(void)0; } };
  return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
