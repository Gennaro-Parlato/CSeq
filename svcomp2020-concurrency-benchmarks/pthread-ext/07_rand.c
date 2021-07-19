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
volatile int seed;
inline int PseudoRandomUsingAtomic_nextInt(int n) {
 int read, nexts, nextInt_return;
 __VERIFIER_atomic_acquire();
 read = seed;
 do
 {
  nexts = __VERIFIER_nondet_int();
 }
 while(nexts == read || nexts == 0);
 { if(!(nexts != read)) { ERROR: {reach_error();abort();}(void)0; } };
 seed = nexts;
 __VERIFIER_atomic_release();
 nextInt_return = nexts % n;
 return nextInt_return;
}
inline void PseudoRandomUsingAtomic_monitor(){
 while(1)
 {
  { if(!(seed != 0)) { ERROR: {reach_error();abort();}(void)0; } };
 }
}
inline void PseudoRandomUsingAtomic_constructor(int init){
 seed = init;
}
inline void PseudoRandomUsingAtomic__threadmain(){
 int myrand;
 myrand = PseudoRandomUsingAtomic_nextInt(10);
 { if(!(myrand <= 10)) { ERROR: {reach_error();abort();}(void)0; } };
}
volatile int state = 0;
void* thr1(void* arg)
{
 __VERIFIER_atomic_acquire();
 switch(state)
 {
 case 0:
  PseudoRandomUsingAtomic_constructor(1);
  state = 1;
  __VERIFIER_atomic_release();
  PseudoRandomUsingAtomic_monitor();
  break;
 case 1:
  __VERIFIER_atomic_release();
  PseudoRandomUsingAtomic__threadmain();
  break;
 }
  return 0;
}
int main()
{
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
