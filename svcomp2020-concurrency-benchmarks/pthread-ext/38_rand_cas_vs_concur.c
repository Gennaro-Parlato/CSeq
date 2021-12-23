#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

inline int nC(int s2){
 int nC_return;
 do
 {
  nC_return = __VERIFIER_nondet_int();
 }
 while(nC_return == s2 || nC_return == 0);
 return nC_return;
}
int seed = 1;
void __VERIFIER_atomic_CAS(
  int *v,
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
inline int PseudoRandomUsingAtomic_nex()
{
 int nex, nexts, casret, nex_return;
 while(1) {
  nex = seed;
  nexts = nC(nex);
  __VERIFIER_atomic_CAS(&seed,nex,nexts,&casret);
  if(casret == 1){
   nex_return = ((10>=nexts)?(nexts):(10));
   break;
  }
 }
 return nex_return;
}
void* thr1(void* arg){
  { if(!(PseudoRandomUsingAtomic_nex() <= 10)) { ERROR: {reach_error();abort();}(void)0; } };
  return 0;
}
int main()
{
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
