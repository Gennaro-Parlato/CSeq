#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int count = 0;
void __VERIFIER_atomic_acquire(int * m)
{
 assume_abort_if_not(*m==0);
 *m = 1;
}
void __VERIFIER_atomic_release(int * m)
{
 assume_abort_if_not(*m==1);
 *m = 0;
}
void __VERIFIER_atomic_inc()
{
  count++;
}
void __VERIFIER_atomic_dec()
{
  count--;
}
int mutexa = 0;
int mutexb = 0;
inline void my_thread1()
{
  __VERIFIER_atomic_acquire(&mutexa);
  __VERIFIER_atomic_inc();
  __VERIFIER_atomic_dec();
  __VERIFIER_atomic_release(&mutexa);
}
inline void my_thread2()
{
  __VERIFIER_atomic_acquire(&mutexb);
  __VERIFIER_atomic_dec();
  __VERIFIER_atomic_inc();
  __VERIFIER_atomic_release(&mutexb);
}
void* thr1(void* arg)
{
  while(1)
  {
    __VERIFIER_atomic_acquire(&mutexa);
    { if(!(count >= -1)) { goto ERROR; } };
    __VERIFIER_atomic_release(&mutexa);
    __VERIFIER_atomic_acquire(&mutexb);
    { if(!(count <= 1)) { ERROR: {reach_error();abort();}(void)0; } };
    __VERIFIER_atomic_release(&mutexb);
  }
  return 0;
}
void* thr2(void* arg)
{
  if(__VERIFIER_nondet_int())
    my_thread1();
  else
    my_thread2();
  return 0;
}
int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  while(1)
  {
      pthread_create(&t, 0, thr2, 0);
  }
}
