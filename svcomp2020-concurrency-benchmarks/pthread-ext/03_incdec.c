#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile unsigned value = 0, m = 0;
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
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;
inline unsigned inc() {
 unsigned inc_v = 0;
 __VERIFIER_atomic_acquire();
 if(value == 0u-1) {
  __VERIFIER_atomic_release();
  return 0;
 }else{
  inc_v = value;
  inc_flag = 1, value = inc_v + 1;
  __VERIFIER_atomic_release();
  {__VERIFIER_atomic_acquire();{ if(!(dec_flag || value > inc_v)) { ERROR: {reach_error();abort();}(void)0; } };__VERIFIER_atomic_release();};
  return inc_v + 1;
 }
}
inline unsigned dec() {
 unsigned dec_v;
 __VERIFIER_atomic_acquire();
 if(value == 0) {
  __VERIFIER_atomic_release();
  return 0u-1;
 }else{
  dec_v = value;
  dec_flag = 1, value = dec_v - 1;
  __VERIFIER_atomic_release();
  {__VERIFIER_atomic_acquire();{ if(!(inc_flag || value < dec_v)) { ERROR: {reach_error();abort();}(void)0; } };__VERIFIER_atomic_release();};
  return dec_v - 1;
 }
}
void* thr1(void* arg){
 int r = __VERIFIER_nondet_int();
 if(r){ inc(); }
 else{ dec(); }
  return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
