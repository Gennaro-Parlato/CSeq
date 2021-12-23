#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile int max = 0x80000000;
int storage[2*3];
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
inline void findMax(int offset){
 int i;
 int e;
 int c;
 int cret;
 for(i = offset; i < offset+2; i++) {
  e = storage[i];
  while(1){
   c = max;
   if(e > c){
    __VERIFIER_atomic_CAS(&max,c,e,&cret);
    if(cret){
     break;
    }
   }else{
    break;
   }
  }
  { if(!(e <= max)) { ERROR: {reach_error();abort();}(void)0; } };
 }
}
void* thr1(void* arg) {
 int offset=__VERIFIER_nondet_int();
 assume_abort_if_not(offset % 2 == 0 && offset >= 0 && offset < 2*3);
 findMax(offset);
  return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
