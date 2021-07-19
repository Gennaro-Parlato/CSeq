#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void __VERIFIER_atomic_CAS(
  volatile unsigned *v,
  unsigned e,
  unsigned u,
  unsigned *r)
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
volatile unsigned value;
void* thr1(void* arg) {
 unsigned v,vn,casret;
 do {
  v = value;
  if(v == 0u-1) {
   return 0;
  }
  vn = v + 1;
  __VERIFIER_atomic_CAS(&value,v,vn,&casret);
 }
 while (casret==0);
 { if(!(value > v)) { ERROR: {reach_error();abort();}(void)0; } };
 return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
