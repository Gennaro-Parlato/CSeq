#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile int max = 0x80000000, m = 0;
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
int storage[2*3];
inline void findMax(int offset)
{
 int i;
 int e;
 for(i = offset; i < offset+2; i++) {
  e = storage[i];
  __VERIFIER_atomic_acquire();
  {
   if(e > max) {
    max = e;
   }
  }
  __VERIFIER_atomic_release();
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
