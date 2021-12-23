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
int __unbuffered_p2_EAX;
int __unbuffered_p2_EAX = 0;
int __unbuffered_p3_EAX;
int __unbuffered_p3_EAX = 0;
int __unbuffered_p3_EBX;
int __unbuffered_p3_EBX = 0;
int a;
int a = 0;
int b;
int b = 0;
_Bool b$flush_delayed;
int b$mem_tmp;
_Bool b$r_buff0_thd0;
_Bool b$r_buff0_thd1;
_Bool b$r_buff0_thd2;
_Bool b$r_buff0_thd3;
_Bool b$r_buff0_thd4;
_Bool b$r_buff1_thd0;
_Bool b$r_buff1_thd1;
_Bool b$r_buff1_thd2;
_Bool b$r_buff1_thd3;
_Bool b$r_buff1_thd4;
_Bool b$read_delayed;
int *b$read_delayed_var;
int b$w_buff0;
_Bool b$w_buff0_used;
int b$w_buff1;
_Bool b$w_buff1_used;
_Bool main$tmp_guard0;
_Bool main$tmp_guard1;
int x;
int x = 0;
int y;
int y = 0;
int z;
int z = 0;
_Bool weak$$choice0;
_Bool weak$$choice2;
void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  b$w_buff1 = b$w_buff0;
  b$w_buff0 = 1;
  b$w_buff1_used = b$w_buff0_used;
  b$w_buff0_used = (_Bool)1;
  __VERIFIER_assert(!(b$w_buff1_used && b$w_buff0_used));
  b$r_buff1_thd0 = b$r_buff0_thd0;
  b$r_buff1_thd1 = b$r_buff0_thd1;
  b$r_buff1_thd2 = b$r_buff0_thd2;
  b$r_buff1_thd3 = b$r_buff0_thd3;
  b$r_buff1_thd4 = b$r_buff0_thd4;
  b$r_buff0_thd1 = (_Bool)1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p0_EAX = x;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  b = b$w_buff0_used && b$r_buff0_thd1 ? b$w_buff0 : (b$w_buff1_used && b$r_buff1_thd1 ? b$w_buff1 : b);
  b$w_buff0_used = b$w_buff0_used && b$r_buff0_thd1 ? (_Bool)0 : b$w_buff0_used;
  b$w_buff1_used = b$w_buff0_used && b$r_buff0_thd1 || b$w_buff1_used && b$r_buff1_thd1 ? (_Bool)0 : b$w_buff1_used;
  b$r_buff0_thd1 = b$w_buff0_used && b$r_buff0_thd1 ? (_Bool)0 : b$r_buff0_thd1;
  b$r_buff1_thd1 = b$w_buff0_used && b$r_buff0_thd1 || b$w_buff1_used && b$r_buff1_thd1 ? (_Bool)0 : b$r_buff1_thd1;
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
  b = b$w_buff0_used && b$r_buff0_thd2 ? b$w_buff0 : (b$w_buff1_used && b$r_buff1_thd2 ? b$w_buff1 : b);
  b$w_buff0_used = b$w_buff0_used && b$r_buff0_thd2 ? (_Bool)0 : b$w_buff0_used;
  b$w_buff1_used = b$w_buff0_used && b$r_buff0_thd2 || b$w_buff1_used && b$r_buff1_thd2 ? (_Bool)0 : b$w_buff1_used;
  b$r_buff0_thd2 = b$w_buff0_used && b$r_buff0_thd2 ? (_Bool)0 : b$r_buff0_thd2;
  b$r_buff1_thd2 = b$w_buff0_used && b$r_buff0_thd2 || b$w_buff1_used && b$r_buff1_thd2 ? (_Bool)0 : b$r_buff1_thd2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P2(void *arg)
{
  __VERIFIER_atomic_begin();
  y = 2;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p2_EAX = z;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  b = b$w_buff0_used && b$r_buff0_thd3 ? b$w_buff0 : (b$w_buff1_used && b$r_buff1_thd3 ? b$w_buff1 : b);
  b$w_buff0_used = b$w_buff0_used && b$r_buff0_thd3 ? (_Bool)0 : b$w_buff0_used;
  b$w_buff1_used = b$w_buff0_used && b$r_buff0_thd3 || b$w_buff1_used && b$r_buff1_thd3 ? (_Bool)0 : b$w_buff1_used;
  b$r_buff0_thd3 = b$w_buff0_used && b$r_buff0_thd3 ? (_Bool)0 : b$r_buff0_thd3;
  b$r_buff1_thd3 = b$w_buff0_used && b$r_buff0_thd3 || b$w_buff1_used && b$r_buff1_thd3 ? (_Bool)0 : b$r_buff1_thd3;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}
void * P3(void *arg)
{
  __VERIFIER_atomic_begin();
  z = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  a = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p3_EAX = a;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  weak$$choice0 = __VERIFIER_nondet_bool();
  weak$$choice2 = __VERIFIER_nondet_bool();
  b$flush_delayed = weak$$choice2;
  b$mem_tmp = b;
  b = !b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b : (b$w_buff0_used && b$r_buff0_thd4 ? b$w_buff0 : b$w_buff1);
  b$w_buff0 = weak$$choice2 ? b$w_buff0 : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$w_buff0 : (b$w_buff0_used && b$r_buff0_thd4 ? b$w_buff0 : b$w_buff0));
  b$w_buff1 = weak$$choice2 ? b$w_buff1 : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$w_buff1 : (b$w_buff0_used && b$r_buff0_thd4 ? b$w_buff1 : b$w_buff1));
  b$w_buff0_used = weak$$choice2 ? b$w_buff0_used : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$w_buff0_used : (b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : b$w_buff0_used));
  b$w_buff1_used = weak$$choice2 ? b$w_buff1_used : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$w_buff1_used : (b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : (_Bool)0));
  b$r_buff0_thd4 = weak$$choice2 ? b$r_buff0_thd4 : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$r_buff0_thd4 : (b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : b$r_buff0_thd4));
  b$r_buff1_thd4 = weak$$choice2 ? b$r_buff1_thd4 : (!b$w_buff0_used || !b$r_buff0_thd4 && !b$w_buff1_used || !b$r_buff0_thd4 && !b$r_buff1_thd4 ? b$r_buff1_thd4 : (b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : (_Bool)0));
  __unbuffered_p3_EBX = b;
  b = b$flush_delayed ? b$mem_tmp : b;
  b$flush_delayed = (_Bool)0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  b = b$w_buff0_used && b$r_buff0_thd4 ? b$w_buff0 : (b$w_buff1_used && b$r_buff1_thd4 ? b$w_buff1 : b);
  b$w_buff0_used = b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : b$w_buff0_used;
  b$w_buff1_used = b$w_buff0_used && b$r_buff0_thd4 || b$w_buff1_used && b$r_buff1_thd4 ? (_Bool)0 : b$w_buff1_used;
  b$r_buff0_thd4 = b$w_buff0_used && b$r_buff0_thd4 ? (_Bool)0 : b$r_buff0_thd4;
  b$r_buff1_thd4 = b$w_buff0_used && b$r_buff0_thd4 || b$w_buff1_used && b$r_buff1_thd4 ? (_Bool)0 : b$r_buff1_thd4;
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
  pthread_t t1025;
  pthread_create(&t1025, ((void *)0), P0, ((void *)0));
  pthread_t t1026;
  pthread_create(&t1026, ((void *)0), P1, ((void *)0));
  pthread_t t1027;
  pthread_create(&t1027, ((void *)0), P2, ((void *)0));
  pthread_t t1028;
  pthread_create(&t1028, ((void *)0), P3, ((void *)0));
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 4;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  b = b$w_buff0_used && b$r_buff0_thd0 ? b$w_buff0 : (b$w_buff1_used && b$r_buff1_thd0 ? b$w_buff1 : b);
  b$w_buff0_used = b$w_buff0_used && b$r_buff0_thd0 ? (_Bool)0 : b$w_buff0_used;
  b$w_buff1_used = b$w_buff0_used && b$r_buff0_thd0 || b$w_buff1_used && b$r_buff1_thd0 ? (_Bool)0 : b$w_buff1_used;
  b$r_buff0_thd0 = b$w_buff0_used && b$r_buff0_thd0 ? (_Bool)0 : b$r_buff0_thd0;
  b$r_buff1_thd0 = b$w_buff0_used && b$r_buff0_thd0 || b$w_buff1_used && b$r_buff1_thd0 ? (_Bool)0 : b$r_buff1_thd0;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  main$tmp_guard1 = !(y == 2 && __unbuffered_p0_EAX == 0 && __unbuffered_p2_EAX == 0 && __unbuffered_p3_EAX == 1 && __unbuffered_p3_EBX == 0);
  __VERIFIER_atomic_end();
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}
