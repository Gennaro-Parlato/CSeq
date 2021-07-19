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
inline int calculateNext(int s2){
 int cnex;
 do cnex = __VERIFIER_nondet_int();
 while(cnex == s2 || cnex == 0);
 return cnex;
}
int seed = 1;
inline int PseudoRandomUsingAtomic_nextInt() {
 int read, nexts, nextInt_return;
 { if(!(seed != 0)) { ERROR: {reach_error();abort();}(void)0; } };
 __VERIFIER_atomic_acquire();
 read = seed;
 nexts = calculateNext(read);
 seed = nexts;
 __VERIFIER_atomic_release();
 nextInt_return = ((10>=nexts)?(nexts):(10));
 return nextInt_return;
}
void* thr1(void* arg){
  PseudoRandomUsingAtomic_nextInt();
  return 0;
}
int main()
{
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
