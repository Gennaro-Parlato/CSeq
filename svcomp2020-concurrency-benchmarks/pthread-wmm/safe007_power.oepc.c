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
_Bool __unbuffered_p0_EAX$flush_delayed;
int __unbuffered_p0_EAX$mem_tmp;
_Bool __unbuffered_p0_EAX$r_buff0_thd0;
_Bool __unbuffered_p0_EAX$r_buff0_thd1;
_Bool __unbuffered_p0_EAX$r_buff0_thd2;
_Bool __unbuffered_p0_EAX$r_buff0_thd3;
_Bool __unbuffered_p0_EAX$r_buff1_thd0;
_Bool __unbuffered_p0_EAX$r_buff1_thd1;
_Bool __unbuffered_p0_EAX$r_buff1_thd2;
_Bool __unbuffered_p0_EAX$r_buff1_thd3;
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
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
int y;
int y = 0;
int z;
int z = 0;
_Bool z$flush_delayed;
int z$mem_tmp;
_Bool z$r_buff0_thd0;
_Bool z$r_buff0_thd1;
_Bool z$r_buff0_thd2;
_Bool z$r_buff0_thd3;
_Bool z$r_buff1_thd0;
_Bool z$r_buff1_thd1;
_Bool z$r_buff1_thd2;
_Bool z$r_buff1_thd3;
_Bool z$read_delayed;
int *z$read_delayed_var;
int z$w_buff0;
_Bool z$w_buff0_used;
int z$w_buff1;
_Bool z$w_buff1_used;
_Bool weak$$choice0;
_Bool weak$$choice1;
_Bool weak$$choice2;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  z$flush_delayed = weak$$choice2;
  z$mem_tmp = z;
  weak$$choice1 = __VERIFIER_nondet_bool();
  z = !z$w_buff0_used ? z : (z$w_buff0_used && z$r_buff0_thd1 ? z$w_buff0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (weak$$choice0 ? z : (weak$$choice1 ? z$w_buff0 : z$w_buff1)) : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (weak$$choice0 ? z$w_buff1 : z$w_buff0) : (weak$$choice0 ? z$w_buff0 : z))));
  z$w_buff0 = weak$$choice2 ? z$w_buff0 : (!z$w_buff0_used ? z$w_buff0 : (z$w_buff0_used && z$r_buff0_thd1 ? z$w_buff0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? z$w_buff0 : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? z$w_buff0 : z$w_buff0))));
  z$w_buff1 = weak$$choice2 ? z$w_buff1 : (!z$w_buff0_used ? z$w_buff1 : (z$w_buff0_used && z$r_buff0_thd1 ? z$w_buff1 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? z$w_buff1 : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? z$w_buff1 : z$w_buff1))));
  z$w_buff0_used = weak$$choice2 ? z$w_buff0_used : (!z$w_buff0_used ? z$w_buff0_used : (z$w_buff0_used && z$r_buff0_thd1 ? (_Bool)0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? weak$$choice0 || !weak$$choice1 : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? weak$$choice0 : weak$$choice0))));
  z$w_buff1_used = weak$$choice2 ? z$w_buff1_used : (!z$w_buff0_used ? z$w_buff1_used : (z$w_buff0_used && z$r_buff0_thd1 ? (_Bool)0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? weak$$choice0 : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  z$r_buff0_thd1 = weak$$choice2 ? z$r_buff0_thd1 : (!z$w_buff0_used ? z$r_buff0_thd1 : (z$w_buff0_used && z$r_buff0_thd1 ? (_Bool)0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? z$r_buff0_thd1 : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  z$r_buff1_thd1 = weak$$choice2 ? z$r_buff1_thd1 : (!z$w_buff0_used ? z$r_buff1_thd1 : (z$w_buff0_used && z$r_buff0_thd1 ? (_Bool)0 : (z$w_buff0_used && !z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (weak$$choice0 ? z$r_buff1_thd1 : (_Bool)0) : (z$w_buff0_used && z$r_buff1_thd1 && z$w_buff1_used && !z$r_buff0_thd1 ? (_Bool)0 : (_Bool)0))));
  __unbuffered_p0_EAX$read_delayed = (_Bool)1;
  __unbuffered_p0_EAX$read_delayed_var = &z;
  __unbuffered_p0_EAX = z;
  z = z$flush_delayed ? z$mem_tmp : z;
  z$flush_delayed = (_Bool)0;
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
  z = z$w_buff0_used && z$r_buff0_thd3 ? z$w_buff0 : (z$w_buff1_used && z$r_buff1_thd3 ? z$w_buff1 : z);
  z$w_buff0_used = z$w_buff0_used && z$r_buff0_thd3 ? (_Bool)0 : z$w_buff0_used;
  z$w_buff1_used = z$w_buff0_used && z$r_buff0_thd3 || z$w_buff1_used && z$r_buff1_thd3 ? (_Bool)0 : z$w_buff1_used;
  z$r_buff0_thd3 = z$w_buff0_used && z$r_buff0_thd3 ? (_Bool)0 : z$r_buff0_thd3;
  z$r_buff1_thd3 = z$w_buff0_used && z$r_buff0_thd3 || z$w_buff1_used && z$r_buff1_thd3 ? (_Bool)0 : z$r_buff1_thd3;
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
  pthread_t t1937;
  pthread_create(&t1937, ((void *)0), P0, ((void *)0));
  pthread_t t1938;
  pthread_create(&t1938, ((void *)0), P1, ((void *)0));
  pthread_t t1939;
  pthread_create(&t1939, ((void *)0), P2, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 3;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  z = z$w_buff0_used && z$r_buff0_thd0 ? z$w_buff0 : (z$w_buff1_used && z$r_buff1_thd0 ? z$w_buff1 : z);
  z$w_buff0_used = z$w_buff0_used && z$r_buff0_thd0 ? (_Bool)0 : z$w_buff0_used;
  z$w_buff1_used = z$w_buff0_used && z$r_buff0_thd0 || z$w_buff1_used && z$r_buff1_thd0 ? (_Bool)0 : z$w_buff1_used;
  z$r_buff0_thd0 = z$w_buff0_used && z$r_buff0_thd0 ? (_Bool)0 : z$r_buff0_thd0;
  z$r_buff1_thd0 = z$w_buff0_used && z$r_buff0_thd0 || z$w_buff1_used && z$r_buff1_thd0 ? (_Bool)0 : z$r_buff1_thd0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice1 = __VERIFIER_nondet_bool();
  __unbuffered_p0_EAX = __unbuffered_p0_EAX$read_delayed ? (weak$$choice1 ? *__unbuffered_p0_EAX$read_delayed_var : __unbuffered_p0_EAX) : __unbuffered_p0_EAX;
  main$tmp_guard1 = !(__unbuffered_p0_EAX == 1 && __unbuffered_p1_EAX == 1 && __unbuffered_p2_EAX == 1);
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}
