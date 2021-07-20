#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void * P0(void *arg);
void * P1(void *arg);
void * P2(void *arg);
void fence();
void isync();
void lwfence();
int __unbuffered_cnt;
int __unbuffered_cnt = 0;
int __unbuffered_p0_EAX;
int __unbuffered_p0_EAX = 0;
int __unbuffered_p2_EAX;
int __unbuffered_p2_EAX = 0;
_Bool __unbuffered_p2_EAX$flush_delayed;
int __unbuffered_p2_EAX$mem_tmp;
_Bool __unbuffered_p2_EAX$r_buff0_thd0;
_Bool __unbuffered_p2_EAX$r_buff0_thd1;
_Bool __unbuffered_p2_EAX$r_buff0_thd2;
_Bool __unbuffered_p2_EAX$r_buff0_thd3;
_Bool __unbuffered_p2_EAX$r_buff1_thd0;
_Bool __unbuffered_p2_EAX$r_buff1_thd1;
_Bool __unbuffered_p2_EAX$r_buff1_thd2;
_Bool __unbuffered_p2_EAX$r_buff1_thd3;
_Bool __unbuffered_p2_EAX$read_delayed;
int *__unbuffered_p2_EAX$read_delayed_var;
int __unbuffered_p2_EAX$w_buff0;
_Bool __unbuffered_p2_EAX$w_buff0_used;
int __unbuffered_p2_EAX$w_buff1;
_Bool __unbuffered_p2_EAX$w_buff1_used;
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
_Bool x$flush_delayed;
int x$mem_tmp;
_Bool x$r_buff0_thd0;
_Bool x$r_buff0_thd1;
_Bool x$r_buff0_thd2;
_Bool x$r_buff0_thd3;
_Bool x$r_buff1_thd0;
_Bool x$r_buff1_thd1;
_Bool x$r_buff1_thd2;
_Bool x$r_buff1_thd3;
_Bool x$read_delayed;
int *x$read_delayed_var;
int x$w_buff0;
_Bool x$w_buff0_used;
int x$w_buff1;
_Bool x$w_buff1_used;
int y;
int y = 0;
_Bool weak$$choice0;
_Bool weak$$choice1;
_Bool weak$$choice2;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  y = 2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  x$flush_delayed = weak$$choice2;
  x$mem_tmp = x;
  x = !x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x : (x$w_buff0_used && x$r_buff0_thd1 ? x$w_buff0 : x$w_buff1);
  x$w_buff0 = weak$$choice2 ? x$w_buff0 : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$w_buff0 : (x$w_buff0_used && x$r_buff0_thd1 ? x$w_buff0 : x$w_buff0));
  x$w_buff1 = weak$$choice2 ? x$w_buff1 : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$w_buff1 : (x$w_buff0_used && x$r_buff0_thd1 ? x$w_buff1 : x$w_buff1));
  x$w_buff0_used = weak$$choice2 ? x$w_buff0_used : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$w_buff0_used : (x$w_buff0_used && x$r_buff0_thd1 ? (_Bool)0 : x$w_buff0_used));
  x$w_buff1_used = weak$$choice2 ? x$w_buff1_used : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$w_buff1_used : (x$w_buff0_used && x$r_buff0_thd1 ? (_Bool)0 : (_Bool)0));
  x$r_buff0_thd1 = weak$$choice2 ? x$r_buff0_thd1 : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$r_buff0_thd1 : (x$w_buff0_used && x$r_buff0_thd1 ? (_Bool)0 : x$r_buff0_thd1));
  x$r_buff1_thd1 = weak$$choice2 ? x$r_buff1_thd1 : (!x$w_buff0_used || !x$r_buff0_thd1 && !x$w_buff1_used || !x$r_buff0_thd1 && !x$r_buff1_thd1 ? x$r_buff1_thd1 : (x$w_buff0_used && x$r_buff0_thd1 ? (_Bool)0 : (_Bool)0));
  __unbuffered_p0_EAX = x;
  x = x$flush_delayed ? x$mem_tmp : x;
  x$flush_delayed = (_Bool)0;
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
  x = x$w_buff0_used && x$r_buff0_thd2 ? x$w_buff0 : (x$w_buff1_used && x$r_buff1_thd2 ? x$w_buff1 : x);
  x$w_buff0_used = x$w_buff0_used && x$r_buff0_thd2 ? (_Bool)0 : x$w_buff0_used;
  x$w_buff1_used = x$w_buff0_used && x$r_buff0_thd2 || x$w_buff1_used && x$r_buff1_thd2 ? (_Bool)0 : x$w_buff1_used;
  x$r_buff0_thd2 = x$w_buff0_used && x$r_buff0_thd2 ? (_Bool)0 : x$r_buff0_thd2;
  x$r_buff1_thd2 = x$w_buff0_used && x$r_buff0_thd2 || x$w_buff1_used && x$r_buff1_thd2 ? (_Bool)0 : x$r_buff1_thd2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P2(void *arg)
{
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  x$flush_delayed = weak$$choice2;
  x$mem_tmp = x;
  x = !x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x : (x$w_buff0_used && x$r_buff0_thd3 ? x$w_buff0 : x$w_buff1);
  x$w_buff0 = weak$$choice2 ? x$w_buff0 : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$w_buff0 : (x$w_buff0_used && x$r_buff0_thd3 ? x$w_buff0 : x$w_buff0));
  x$w_buff1 = weak$$choice2 ? x$w_buff1 : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$w_buff1 : (x$w_buff0_used && x$r_buff0_thd3 ? x$w_buff1 : x$w_buff1));
  x$w_buff0_used = weak$$choice2 ? x$w_buff0_used : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$w_buff0_used : (x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : x$w_buff0_used));
  x$w_buff1_used = weak$$choice2 ? x$w_buff1_used : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$w_buff1_used : (x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : (_Bool)0));
  x$r_buff0_thd3 = weak$$choice2 ? x$r_buff0_thd3 : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$r_buff0_thd3 : (x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : x$r_buff0_thd3));
  x$r_buff1_thd3 = weak$$choice2 ? x$r_buff1_thd3 : (!x$w_buff0_used || !x$r_buff0_thd3 && !x$w_buff1_used || !x$r_buff0_thd3 && !x$r_buff1_thd3 ? x$r_buff1_thd3 : (x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : (_Bool)0));
  __unbuffered_p2_EAX$read_delayed = (_Bool)1;
  __unbuffered_p2_EAX$read_delayed_var = &x;
  __unbuffered_p2_EAX = x;
  x = x$flush_delayed ? x$mem_tmp : x;
  x$flush_delayed = (_Bool)0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  y = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  x = x$w_buff0_used && x$r_buff0_thd3 ? x$w_buff0 : (x$w_buff1_used && x$r_buff1_thd3 ? x$w_buff1 : x);
  x$w_buff0_used = x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : x$w_buff0_used;
  x$w_buff1_used = x$w_buff0_used && x$r_buff0_thd3 || x$w_buff1_used && x$r_buff1_thd3 ? (_Bool)0 : x$w_buff1_used;
  x$r_buff0_thd3 = x$w_buff0_used && x$r_buff0_thd3 ? (_Bool)0 : x$r_buff0_thd3;
  x$r_buff1_thd3 = x$w_buff0_used && x$r_buff0_thd3 || x$w_buff1_used && x$r_buff1_thd3 ? (_Bool)0 : x$r_buff1_thd3;
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
  pthread_t t2269;
  pthread_create(&t2269, ((void *)0), P0, ((void *)0));
  pthread_t t2270;
  pthread_create(&t2270, ((void *)0), P1, ((void *)0));
  pthread_t t2271;
  pthread_create(&t2271, ((void *)0), P2, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 3;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  x = x$w_buff0_used && x$r_buff0_thd0 ? x$w_buff0 : (x$w_buff1_used && x$r_buff1_thd0 ? x$w_buff1 : x);
  x$w_buff0_used = x$w_buff0_used && x$r_buff0_thd0 ? (_Bool)0 : x$w_buff0_used;
  x$w_buff1_used = x$w_buff0_used && x$r_buff0_thd0 || x$w_buff1_used && x$r_buff1_thd0 ? (_Bool)0 : x$w_buff1_used;
  x$r_buff0_thd0 = x$w_buff0_used && x$r_buff0_thd0 ? (_Bool)0 : x$r_buff0_thd0;
  x$r_buff1_thd0 = x$w_buff0_used && x$r_buff0_thd0 || x$w_buff1_used && x$r_buff1_thd0 ? (_Bool)0 : x$r_buff1_thd0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice1 = __VERIFIER_nondet_bool();
  __unbuffered_p2_EAX = __unbuffered_p2_EAX$read_delayed ? (weak$$choice1 ? *__unbuffered_p2_EAX$read_delayed_var : __unbuffered_p2_EAX) : __unbuffered_p2_EAX;
  main$tmp_guard1 = !(y == 2 && __unbuffered_p0_EAX == 0 && __unbuffered_p2_EAX == 1);
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}
