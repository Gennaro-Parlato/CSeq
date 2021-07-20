#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile int lock = 0;
void __VERIFIER_atomic_TAS(
  volatile int *v,
  volatile int *o)
{
 *o = *v;
 *v = 1;
}
inline void acquire_lock(){
 unsigned int delay;
 int cond;
 delay = 1;
 __VERIFIER_atomic_TAS(&lock,&cond);
 while(cond == 1){
  if(delay*2 > delay)
   delay *= 2;
  __VERIFIER_atomic_TAS(&lock,&cond);
 }
 { if(!(cond != lock)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void release_lock(){
 { if(!(lock != 0)) { ERROR: {reach_error();abort();}(void)0; } };
 lock = 0;
}
int c = 0;
void* thr1(void *arg){
 while(1){
  acquire_lock();
  c++; { if(!(c == 1)) { ERROR: {reach_error();abort();}(void)0; } }; c--;
  release_lock();
 }
  return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
