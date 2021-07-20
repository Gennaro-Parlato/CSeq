#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void * P0(void *arg);
void * P1(void *arg);
void fence();
void isync();
void lwfence();
int __unbuffered_cnt;
int __unbuffered_cnt = 0;
int __unbuffered_p0_EAX;
int __unbuffered_p0_EAX = 0;
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
int y;
int y = 0;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  y = 2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p0_EAX = x;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P1(void *arg)
{
  __VERIFIER_atomic_begin();
  x = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  y = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void fence()
{
}
void isync()
{
}
void lwfence()
{
}
int main()
{
  pthread_t t2573;
  pthread_create(&t2573, ((void *)0), P0, ((void *)0));
  pthread_t t2574;
  pthread_create(&t2574, ((void *)0), P1, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 2;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  main$tmp_guard1 = !(y == 2 && __unbuffered_p0_EAX == 0);
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}
