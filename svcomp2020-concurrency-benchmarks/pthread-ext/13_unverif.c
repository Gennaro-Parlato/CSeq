#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

unsigned int r = 0;
unsigned int s = 0;
void __VERIFIER_atomic_inc_r()
{
  assume_abort_if_not(r!=-1);
  r = r + 1;
}
void* thr1(void* arg){
  unsigned int l = 0;
  __VERIFIER_atomic_inc_r();
  if(r == 1){
    L3: s = s + 1;
    l = l + 1;
    { if(!(s == l)) { ERROR: {reach_error();abort();}(void)0; } };
    goto L3;
  }
  return 0;
}
int main(){
  pthread_t t;
  while(1){
    pthread_create(&t, 0, thr1, 0);
  }
}
