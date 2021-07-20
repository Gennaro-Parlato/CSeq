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
int __unbuffered_p2_EAX;
int __unbuffered_p2_EAX = 0;
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
int y;
int y = 0;
_Bool y$flush_delayed;
int y$mem_tmp;
_Bool y$r_buff0_thd0;
_Bool y$r_buff0_thd1;
_Bool y$r_buff0_thd2;
_Bool y$r_buff0_thd3;
_Bool y$r_buff0_thd4;
_Bool y$r_buff1_thd0;
_Bool y$r_buff1_thd1;
_Bool y$r_buff1_thd2;
_Bool y$r_buff1_thd3;
_Bool y$r_buff1_thd4;
_Bool y$read_delayed;
int *y$read_delayed_var;
int y$w_buff0;
_Bool y$w_buff0_used;
int y$w_buff1;
_Bool y$w_buff1_used;
_Bool weak$$choice0;
_Bool weak$$choice1;
_Bool weak$$choice2;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  y$flush_delayed = weak$$choice2;
  y$mem_tmp = y;
  weak$$choice1 = __VERIFIER_nondet_bool();
  y = !y$w_buff0_used ? y : (y$w_buff0_used && y$r_buff0_thd1 ? y$w_buff0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (weak$$choice0 ? y : (weak$$choice1 ? y$w_buff0 : y$w_buff1)) : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (weak$$choice0 ? y$w_buff1 : y$w_buff0) : (weak$$choice0 ? y$w_buff0 : y))));
  y$w_buff0 = weak$$choice2 ? y$w_buff0 : (!y$w_buff0_used ? y$w_buff0 : (y$w_buff0_used && y$r_buff0_thd1 ? y$w_buff0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? y$w_buff0 : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? y$w_buff0 : y$w_buff0))));
  y$w_buff1 = weak$$choice2 ? y$w_buff1 : (!y$w_buff0_used ? y$w_buff1 : (y$w_buff0_used && y$r_buff0_thd1 ? y$w_buff1 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? y$w_buff1 : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? y$w_buff1 : y$w_buff1))));
  y$w_buff0_used = weak$$choice2 ? y$w_buff0_used : (!y$w_buff0_used ? y$w_buff0_used : (y$w_buff0_used && y$r_buff0_thd1 ? (_Bool)0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? weak$$choice0 || !weak$$choice1 : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? weak$$choice0 : weak$$choice0))));
  y$w_buff1_used = weak$$choice2 ? y$w_buff1_used : (!y$w_buff0_used ? y$w_buff1_used : (y$w_buff0_used && y$r_buff0_thd1 ? (_Bool)0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? weak$$choice0 : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  y$r_buff0_thd1 = weak$$choice2 ? y$r_buff0_thd1 : (!y$w_buff0_used ? y$r_buff0_thd1 : (y$w_buff0_used && y$r_buff0_thd1 ? (_Bool)0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? y$r_buff0_thd1 : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  y$r_buff1_thd1 = weak$$choice2 ? y$r_buff1_thd1 : (!y$w_buff0_used ? y$r_buff1_thd1 : (y$w_buff0_used && y$r_buff0_thd1 ? (_Bool)0 : (y$w_buff0_used && !y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (weak$$choice0 ? y$r_buff1_thd1 : (_Bool)0) : (y$w_buff0_used && y$r_buff1_thd1 && y$w_buff1_used && !y$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  __unbuffered_p0_EAX$read_delayed = (_Bool)1;
  __unbuffered_p0_EAX$read_delayed_var = &y;
  __unbuffered_p0_EAX = y;
  y = y$flush_delayed ? y$mem_tmp : y;
  y$flush_delayed = (_Bool)0;
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
  x = 2;
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
  __unbuffered_p2_EAX = x;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  y = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  y = y$w_buff0_used && y$r_buff0_thd3 ? y$w_buff0 : (y$w_buff1_used && y$r_buff1_thd3 ? y$w_buff1 : y);
  y$w_buff0_used = y$w_buff0_used && y$r_buff0_thd3 ? (_Bool)0 : y$w_buff0_used;
  y$w_buff1_used = y$w_buff0_used && y$r_buff0_thd3 || y$w_buff1_used && y$r_buff1_thd3 ? (_Bool)0 : y$w_buff1_used;
  y$r_buff0_thd3 = y$w_buff0_used && y$r_buff0_thd3 ? (_Bool)0 : y$r_buff0_thd3;
  y$r_buff1_thd3 = y$w_buff0_used && y$r_buff0_thd3 || y$w_buff1_used && y$r_buff1_thd3 ? (_Bool)0 : y$r_buff1_thd3;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P3(void *arg)
{
  __VERIFIER_atomic_begin();
  y = 2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  y = y$w_buff0_used && y$r_buff0_thd4 ? y$w_buff0 : (y$w_buff1_used && y$r_buff1_thd4 ? y$w_buff1 : y);
  y$w_buff0_used = y$w_buff0_used && y$r_buff0_thd4 ? (_Bool)0 : y$w_buff0_used;
  y$w_buff1_used = y$w_buff0_used && y$r_buff0_thd4 || y$w_buff1_used && y$r_buff1_thd4 ? (_Bool)0 : y$w_buff1_used;
  y$r_buff0_thd4 = y$w_buff0_used && y$r_buff0_thd4 ? (_Bool)0 : y$r_buff0_thd4;
  y$r_buff1_thd4 = y$w_buff0_used && y$r_buff0_thd4 || y$w_buff1_used && y$r_buff1_thd4 ? (_Bool)0 : y$r_buff1_thd4;
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
  pthread_t t2145;
  pthread_create(&t2145, ((void *)0), P0, ((void *)0));
  pthread_t t2146;
  pthread_create(&t2146, ((void *)0), P1, ((void *)0));
  pthread_t t2147;
  pthread_create(&t2147, ((void *)0), P2, ((void *)0));
  pthread_t t2148;
  pthread_create(&t2148, ((void *)0), P3, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 4;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  y = y$w_buff0_used && y$r_buff0_thd0 ? y$w_buff0 : (y$w_buff1_used && y$r_buff1_thd0 ? y$w_buff1 : y);
  y$w_buff0_used = y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : y$w_buff0_used;
  y$w_buff1_used = y$w_buff0_used && y$r_buff0_thd0 || y$w_buff1_used && y$r_buff1_thd0 ? (_Bool)0 : y$w_buff1_used;
  y$r_buff0_thd0 = y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : y$r_buff0_thd0;
  y$r_buff1_thd0 = y$w_buff0_used && y$r_buff0_thd0 || y$w_buff1_used && y$r_buff1_thd0 ? (_Bool)0 : y$r_buff1_thd0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  y$flush_delayed = weak$$choice2;
  y$mem_tmp = y;
  y = !y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y : (y$w_buff0_used && y$r_buff0_thd0 ? y$w_buff0 : y$w_buff1);
  y$w_buff0 = weak$$choice2 ? y$w_buff0 : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$w_buff0 : (y$w_buff0_used && y$r_buff0_thd0 ? y$w_buff0 : y$w_buff0));
  y$w_buff1 = weak$$choice2 ? y$w_buff1 : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$w_buff1 : (y$w_buff0_used && y$r_buff0_thd0 ? y$w_buff1 : y$w_buff1));
  y$w_buff0_used = weak$$choice2 ? y$w_buff0_used : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$w_buff0_used : (y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : y$w_buff0_used));
  y$w_buff1_used = weak$$choice2 ? y$w_buff1_used : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$w_buff1_used : (y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : (_Bool)0));
  y$r_buff0_thd0 = weak$$choice2 ? y$r_buff0_thd0 : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$r_buff0_thd0 : (y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : y$r_buff0_thd0));
  y$r_buff1_thd0 = weak$$choice2 ? y$r_buff1_thd0 : (!y$w_buff0_used || !y$r_buff0_thd0 && !y$w_buff1_used || !y$r_buff0_thd0 && !y$r_buff1_thd0 ? y$r_buff1_thd0 : (y$w_buff0_used && y$r_buff0_thd0 ? (_Bool)0 : (_Bool)0));
  weak$$choice1 = __VERIFIER_nondet_bool();
  __unbuffered_p0_EAX = __unbuffered_p0_EAX$read_delayed ? (weak$$choice1 ? *__unbuffered_p0_EAX$read_delayed_var : __unbuffered_p0_EAX) : __unbuffered_p0_EAX;
  main$tmp_guard1 = !(x == 2 && y == 2 && __unbuffered_p0_EAX == 2 && __unbuffered_p2_EAX == 2);
  y = y$flush_delayed ? y$mem_tmp : y;
  y$flush_delayed = (_Bool)0;
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}
