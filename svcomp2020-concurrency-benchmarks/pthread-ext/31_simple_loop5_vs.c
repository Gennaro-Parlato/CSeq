#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int a = 1;
int b = 2;
int c = 3;
int temp;
int mutex;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(mutex==0);
 mutex = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(mutex==1);
 mutex = 0;
}
void* thr2(void* arg)
{
  for(;;){
    __VERIFIER_atomic_acquire();
    temp = a;
    a = b;
    b = c;
    c = temp;
    __VERIFIER_atomic_release();
  }
  return 0;
}
void* thr1(void* arg)
{
  while(1)
  {
    __VERIFIER_atomic_acquire();
    { if(!(a != b)) { ERROR: {reach_error();abort();}(void)0; } };
    __VERIFIER_atomic_release();
  }
  return 0;
}
int main() {
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  while(1)
  {
    pthread_create(&t, 0, thr2, 0);
  }
}
