#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

inline int calculateNext(int s2){
 int calculateNext_return;
 do
 {
  calculateNext_return = __VERIFIER_nondet_int();
 }
 while(calculateNext_return == s2 || calculateNext_return == 0);
 return calculateNext_return;
}
volatile int seed, m=0;
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
void __VERIFIER_atomic_CAS(
  volatile int *v,
  int e,
  int u,
  int *r)
{
 if(*v == e)
 {
  *v = u, *r = 1;
 }
 else
 {
  *r = 0;
 }
}
inline int PseudoRandomUsingAtomic_nextInt(int n)
{
 int read, nexts, casret, nextInt_return;
 while(1) {
  read = seed;
  nexts = calculateNext(read);
  { if(!(nexts != read)) { ERROR: {reach_error();abort();}(void)0; } };
  __VERIFIER_atomic_CAS(&seed,read,nexts,&casret);
  if(casret == 1){
   nextInt_return = nexts % n;
   break;
  }
 }
 return nextInt_return;
}
inline void PseudoRandomUsingAtomic_monitor()
{
 while(1)
 {
  { if(!(seed != 0)) { ERROR: {reach_error();abort();}(void)0; } };
 }
}
inline void PseudoRandomUsingAtomic_constructor(int init)
{
 seed = init;
}
inline void PseudoRandomUsingAtomic__threadmain()
{
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
