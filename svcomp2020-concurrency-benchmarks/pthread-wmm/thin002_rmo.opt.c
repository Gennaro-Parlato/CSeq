#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void * P0(void *arg);
void * P1(void *arg);
void * P2(void *arg);
void * P3(void *arg);
void fence();
void isync();
void lwfence();
int __unbuffered_cnt;
int __unbuffered_cnt = 0;
int __unbuffered_p0_EAX;
int __unbuffered_p0_EAX = 0;
_Bool __unbuffered_p0_EAX$flush_delayed;
int __unbuffered_p0_EAX$mem_tmp;
_Bool __unbuffered_p0_EAX$r_buff0_thd0;
_Bool __unbuffered_p0_EAX$r_buff0_thd1;
_Bool __unbuffered_p0_EAX$r_buff0_thd2;
_Bool __unbuffered_p0_EAX$r_buff0_thd3;
_Bool __unbuffered_p0_EAX$r_buff0_thd4;
_Bool __unbuffered_p0_EAX$r_buff1_thd0;
_Bool __unbuffered_p0_EAX$r_buff1_thd1;
_Bool __unbuffered_p0_EAX$r_buff1_thd2;
_Bool __unbuffered_p0_EAX$r_buff1_thd3;
_Bool __unbuffered_p0_EAX$r_buff1_thd4;
_Bool __unbuffered_p0_EAX$read_delayed;
int *__unbuffered_p0_EAX$read_delayed_var;
int __unbuffered_p0_EAX$w_buff0;
_Bool __unbuffered_p0_EAX$w_buff0_used;
int __unbuffered_p0_EAX$w_buff1;
_Bool __unbuffered_p0_EAX$w_buff1_used;
int __unbuffered_p1_EAX;
int __unbuffered_p1_EAX = 0;
int __unbuffered_p2_EAX;
int __unbuffered_p2_EAX = 0;
int __unbuffered_p3_EAX;
int __unbuffered_p3_EAX = 0;
int a;
int a = 0;
_Bool a$flush_delayed;
int a$mem_tmp;
_Bool a$r_buff0_thd0;
_Bool a$r_buff0_thd1;
_Bool a$r_buff0_thd2;
_Bool a$r_buff0_thd3;
_Bool a$r_buff0_thd4;
_Bool a$r_buff1_thd0;
_Bool a$r_buff1_thd1;
_Bool a$r_buff1_thd2;
_Bool a$r_buff1_thd3;
_Bool a$r_buff1_thd4;
_Bool a$read_delayed;
int *a$read_delayed_var;
int a$w_buff0;
_Bool a$w_buff0_used;
int a$w_buff1;
_Bool a$w_buff1_used;
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
int y;
int y = 0;
int z;
int z = 0;
_Bool weak$$choice0;
_Bool weak$$choice1;
_Bool weak$$choice2;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  a$flush_delayed = weak$$choice2;
  a$mem_tmp = a;
  a = !a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a : (a$w_buff0_used && a$r_buff0_thd1 ? a$w_buff0 : a$w_buff1);
  a$w_buff0 = weak$$choice2 ? a$w_buff0 : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$w_buff0 : (a$w_buff0_used && a$r_buff0_thd1 ? a$w_buff0 : a$w_buff0));
  a$w_buff1 = weak$$choice2 ? a$w_buff1 : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$w_buff1 : (a$w_buff0_used && a$r_buff0_thd1 ? a$w_buff1 : a$w_buff1));
  a$w_buff0_used = weak$$choice2 ? a$w_buff0_used : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$w_buff0_used : (a$w_buff0_used && a$r_buff0_thd1 ? (_Bool)0 : a$w_buff0_used));
  a$w_buff1_used = weak$$choice2 ? a$w_buff1_used : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$w_buff1_used : (a$w_buff0_used && a$r_buff0_thd1 ? (_Bool)0 : (_Bool)0));
  a$r_buff0_thd1 = weak$$choice2 ? a$r_buff0_thd1 : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$r_buff0_thd1 : (a$w_buff0_used && a$r_buff0_thd1 ? (_Bool)0 : a$r_buff0_thd1));
  a$r_buff1_thd1 = weak$$choice2 ? a$r_buff1_thd1 : (!a$w_buff0_used || !a$r_buff0_thd1 && !a$w_buff1_used || !a$r_buff0_thd1 && !a$r_buff1_thd1 ? a$r_buff1_thd1 : (a$w_buff0_used && a$r_buff0_thd1 ? (_Bool)0 : (_Bool)0));
  __unbuffered_p0_EAX$read_delayed = (_Bool)1;
  __unbuffered_p0_EAX$read_delayed_var = &a;
  __unbuffered_p0_EAX = a;
  a = a$flush_delayed ? a$mem_tmp : a;
  a$flush_delayed = (_Bool)0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  x = 1;
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
  __unbuffered_p1_EAX = x;
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
void * P2(void *arg)
{
  __VERIFIER_atomic_begin();
  __unbuffered_p2_EAX = y;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  z = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P3(void *arg)
{
  __VERIFIER_atomic_begin();
  __unbuffered_p3_EAX = z;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  a = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  a = a$w_buff0_used && a$r_buff0_thd4 ? a$w_buff0 : (a$w_buff1_used && a$r_buff1_thd4 ? a$w_buff1 : a);
  a$w_buff0_used = a$w_buff0_used && a$r_buff0_thd4 ? (_Bool)0 : a$w_buff0_used;
  a$w_buff1_used = a$w_buff0_used && a$r_buff0_thd4 || a$w_buff1_used && a$r_buff1_thd4 ? (_Bool)0 : a$w_buff1_used;
  a$r_buff0_thd4 = a$w_buff0_used && a$r_buff0_thd4 ? (_Bool)0 : a$r_buff0_thd4;
  a$r_buff1_thd4 = a$w_buff0_used && a$r_buff0_thd4 || a$w_buff1_used && a$r_buff1_thd4 ? (_Bool)0 : a$r_buff1_thd4;
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
  pthread_t t2725;
  pthread_create(&t2725, ((void *)0), P0, ((void *)0));
  pthread_t t2726;
  pthread_create(&t2726, ((void *)0), P1, ((void *)0));
  pthread_t t2727;
  pthread_create(&t2727, ((void *)0), P2, ((void *)0));
  pthread_t t2728;
  pthread_create(&t2728, ((void *)0), P3, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 4;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  a = a$w_buff0_used && a$r_buff0_thd0 ? a$w_buff0 : (a$w_buff1_used && a$r_buff1_thd0 ? a$w_buff1 : a);
  a$w_buff0_used = a$w_buff0_used && a$r_buff0_thd0 ? (_Bool)0 : a$w_buff0_used;
  a$w_buff1_used = a$w_buff0_used && a$r_buff0_thd0 || a$w_buff1_used && a$r_buff1_thd0 ? (_Bool)0 : a$w_buff1_used;
  a$r_buff0_thd0 = a$w_buff0_used && a$r_buff0_thd0 ? (_Bool)0 : a$r_buff0_thd0;
  a$r_buff1_thd0 = a$w_buff0_used && a$r_buff0_thd0 || a$w_buff1_used && a$r_buff1_thd0 ? (_Bool)0 : a$r_buff1_thd0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice1 = __VERIFIER_nondet_bool();
  __unbuffered_p0_EAX = __unbuffered_p0_EAX$read_delayed ? (weak$$choice1 ? *__unbuffered_p0_EAX$read_delayed_var : __unbuffered_p0_EAX) : __unbuffered_p0_EAX;
  main$tmp_guard1 = !(__unbuffered_p0_EAX == 1 && __unbuffered_p1_EAX == 1 && __unbuffered_p2_EAX == 1 && __unbuffered_p3_EAX == 1);
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}