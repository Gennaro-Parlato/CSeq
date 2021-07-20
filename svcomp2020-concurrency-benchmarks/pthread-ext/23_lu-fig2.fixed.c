#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int mThread=0;
int start_main=0;
int mStartLock=0;
int __COUNT__ =0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(mStartLock==0);
 mStartLock = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(mStartLock==1);
 mStartLock = 0;
}
void __VERIFIER_atomic_thr1(int PR_CreateThread__RES)
{
      if( __COUNT__ == 0 ) {
 mThread = PR_CreateThread__RES;
 __COUNT__ = __COUNT__ + 1;
      } else { { if(!(0)) { ERROR: {reach_error();abort();}(void)0; } }; }
}
void* thr1(void* arg) {
  int PR_CreateThread__RES = 1;
  __VERIFIER_atomic_acquire();
  start_main=1;
  __VERIFIER_atomic_thr1(PR_CreateThread__RES);
  __VERIFIER_atomic_release();
  return 0;
}
void __VERIFIER_atomic_thr2(int self)
{
      if( __COUNT__ == 1 ) {
 __COUNT__ = __COUNT__ + 1;
      } else { { if(!(0)) { ERROR: {reach_error();abort();}(void)0; } }; }
}
void* thr2(void* arg) {
  int self = mThread;
  while (start_main==0);
  __VERIFIER_atomic_acquire();
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_thr2(self);
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  thr2(0);
  return 0;
}
