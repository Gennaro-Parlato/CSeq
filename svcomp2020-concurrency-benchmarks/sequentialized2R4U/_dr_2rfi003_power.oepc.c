/*
 *  generated by CSeq [ 0000 / 0000 ]
 * 
 *  instance version    {}
 *
 *  2020-02-27 11:03:50
 *
 *  params:
 *    -l datarace, -i /home/salvatore/ShadowMemory/svcomp2020-concurrency-benchmarks/pthread-wmm/rfi003_power.oepc.i, --rounds 2, --unwind 4, --local-vars 2, --seq , --svcomp , --debug , --paths , 
 *
 */
#define __cs_MUTEX_INITIALIZER -1
#define __cs_COND_INITIALIZER -1
#define __cs_RWLOCK_INITIALIZER -1
#define __cs_BARRIER_SERIAL_THREAD 0
#define __cs_CANCEL_ASYNCHRONOUS 0
#define __cs_CANCEL_ENABLE 0
#define __cs_CANCEL_DEFERRED 0
#define __cs_CANCEL_DISABLE 0
#define __cs_CANCELED 0
#define __cs_CREATE_DETACHED 0
#define __cs_CREATE_JOINABLE 0
#define __cs_EXPLICIT_SCHED 0
#define __cs_INHERIT_SCHED 0
#define __cs_MUTEX_DEFAULT 0
#define __cs_MUTEX_ERRORCHECK 0
#define __cs_MUTEX_NORMAL 0
#define __cs_MUTEX_RECURSIVE 0
#define __cs_MUTEX_ROBUST 0
#define __cs_MUTEX_STALLED 0
#define __cs_ONCE_INIT 0
#define __cs_PRIO_INHERIT 0
#define __cs_PRIO_NONE 0
#define __cs_PRIO_PROTECT 0
#define __cs_PROCESS_SHARED 0
#define __cs_PROCESS_PRIVATE 0
#define __cs_SCOPE_PROCESS 0
#define __cs_SCOPE_SYSTEM 0
#include <stdio.h>
#include <stdlib.h>
// From SVCOMP benchmark with paths
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
int __VERIFIER_nondet_int();
int nondet_int();
unsigned int __VERIFIER_nondet_uint();
unsigned int nondet_uint();
_Bool __VERIFIER_nondet_bool();
_Bool nondet_bool();
char __VERIFIER_nondet_char();
char nondet_char();
unsigned char __VERIFIER_nondet_uchar();
unsigned char nondet_uchar();

#define THREADS 2
#define ROUNDS 2
#define STOP_VOID(A) return;
#define STOP_NONVOID(A) return 0;
#define IF(T,A,B) if ((__cs_pc[T] > A) || (A >= __cs_pc_cs[T])) goto B; 

                                        unsigned __CPROVER_bitvector[1] __cs_active_thread[3] = {1};
                                        unsigned __CPROVER_bitvector[3] __cs_pc[3];
                                        unsigned __CPROVER_bitvector[4] __cs_pc_cs[3];
                                        unsigned __CPROVER_bitvector[2] __cs_last_thread;
                                        unsigned __CPROVER_bitvector[3] __cs_thread_lines[3] = {7, 5, 6};
                                        void *malloc(unsigned long int);
                                        void *__cs_safe_malloc(unsigned int __cs_size)
                                        {
                                                  void *__cs_ptr = (malloc(__cs_size));
                                                  return __cs_ptr;
                                        }
                                        void __CSEQ_message(char *__cs_message)
                                        {
                                                  ;
                                        }
                                        typedef int __cs_t;
                                        void *__cs_threadargs[3];
                                        void *__cs_thread_joinargs[3];
                                        int __cs_create(__cs_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_thread_function)(void *), void *__cs_arg, int __cs_threadID)
                                        {
                                                  if (__cs_threadID > THREADS)
                                                            return 0;
                                                  *__cs_new_thread_id = __cs_threadID;
                                                  __cs_active_thread[__cs_threadID] = 1;
                                                  __cs_threadargs[__cs_threadID] = __cs_arg;
                                                  __CSEQ_message("thread spawned");
                                                  return 0;
                                        }
                                        int __cs_join(__cs_t __cs_id, void **__cs_value_ptr)
                                        {
                                                  __CPROVER_assume(__cs_pc[__cs_id] == __cs_thread_lines[__cs_id]);
                                                  *__cs_value_ptr = __cs_thread_joinargs[__cs_id];
                                                  return 0;
                                        }
                                        int __cs_exit(void *__cs_value_ptr, unsigned int __cs_thread_index)
                                        {
                                                  __cs_thread_joinargs[__cs_thread_index] = __cs_value_ptr;
                                                  return 0;
                                        }
                                        int __cs_self(void)
                                        {
                                                  return 1;
                                        }
                                        typedef int __cs_mutex_t;
                                        int __cs_mutex_init(__cs_mutex_t *__cs_m, int __cs_val)
                                        {
                                                  *__cs_m = -1;
                                                  return 0;
                                        }
                                        int __cs_mutex_destroy(__cs_mutex_t *__cs_mutex_to_destroy)
                                        {
                                                  __CPROVER_assume((*__cs_mutex_to_destroy) != 0);
                                                  __CPROVER_assume((*__cs_mutex_to_destroy) != (-2));
                                                  __CPROVER_assume((*__cs_mutex_to_destroy) == (-1));
                                                  *__cs_mutex_to_destroy = -2;
                                                  __CSEQ_message("lock destroyed");
                                                  return 0;
                                        }
                                        int __cs_mutex_lock(__cs_mutex_t *__cs_mutex_to_lock, unsigned __CPROVER_bitvector[2] __cs_thread_index)
                                        {
                                                  __CPROVER_assume((*__cs_mutex_to_lock) != 0);
                                                  __CPROVER_assume((*__cs_mutex_to_lock) != (-2));
                                                  __CPROVER_assume((*__cs_mutex_to_lock) == (-1));
                                                  *__cs_mutex_to_lock = __cs_thread_index + 1;
                                                  __CSEQ_message("lock acquired");
                                                  return 0;
                                        }
                                        int __cs_mutex_unlock(__cs_mutex_t *__cs_mutex_to_unlock, unsigned __CPROVER_bitvector[2] __cs_thread_index)
                                        {
                                                  __CPROVER_assume((*__cs_mutex_to_unlock) != 0);
                                                  __CPROVER_assume((*__cs_mutex_to_unlock) != (-2));
                                                  __CPROVER_assume((*__cs_mutex_to_unlock) == (__cs_thread_index + 1));
                                                  *__cs_mutex_to_unlock = -1;
                                                  __CSEQ_message("lock released");
                                                  return 0;
                                        }
                                        typedef int __cs_cond_t;
                                        int __cs_cond_init(__cs_cond_t *__cs_cond_to_init, void *__cs_attr)
                                        {
                                                  *__cs_cond_to_init = -1;
                                                  return 0;
                                        }
                                        int __cs_cond_destroy(__cs_cond_t *__cs_cond_to_destroy)
                                        {
                                                  *__cs_cond_to_destroy = -2;
                                                  return 0;
                                        }
                                        int __cs_cond_wait_1(__cs_cond_t *__cs_cond_to_wait_for, __cs_mutex_t *__cs_m, unsigned int __cs_thread_index)
                                        {
                                                  __CPROVER_assume((*__cs_cond_to_wait_for) != 0);
                                                  __CPROVER_assume((*__cs_cond_to_wait_for) != (-2));
                                                  __cs_mutex_unlock(__cs_m, __cs_thread_index);
                                                  return 0;
                                        }
                                        int __cs_cond_wait_2(__cs_cond_t *__cs_cond_to_wait_for, __cs_mutex_t *__cs_m, unsigned int __cs_thread_index)
                                        {
                                                  __CPROVER_assume((*__cs_cond_to_wait_for) == 1);
                                                  __cs_mutex_lock(__cs_m, __cs_thread_index);
                                                  return 0;
                                        }
                                        int __cs_cond_signal(__cs_cond_t *__cs_cond_to_signal)
                                        {
                                                  *__cs_cond_to_signal = 1;
                                                  __CSEQ_message("conditional variable signal");
                                                  return 0;
                                        }
                                        int __cs_cond_broadcast(__cs_cond_t *__cs_cond_to_broadcast)
                                        {
                                                  *__cs_cond_to_broadcast = 1;
                                                  __CSEQ_message("conditional variable broadcast");
                                                  return 0;
                                        }
                                        typedef struct __cs_barrier_t
                                        {
                                                  unsigned int init;
                                                  unsigned int current;
                                        } __cs_barrier_t;
                                        int __cs_barrier_init(__cs_barrier_t *__cs_barrier_to_init, void *__cs_attr, unsigned int count)
                                        {
                                                  __CPROVER_assume(count > 0);
                                                  __cs_barrier_to_init->current = count;
                                                  __cs_barrier_to_init->init = count;
                                                  return 0;
                                        }
                                        int __cs_barrier_destroy(__cs_barrier_t *__cs_barrier_to_destroy)
                                        {
                                                  __cs_barrier_to_destroy->init = -1;
                                                  __cs_barrier_to_destroy->current = -1;
                                                  return 0;
                                        }
                                        int __cs_barrier_wait_1(__cs_barrier_t *__cs_barrier_to_wait)
                                        {
                                                  __CPROVER_assume(__cs_barrier_to_wait->init > 0);
                                                  __cs_barrier_to_wait->current--;
                                                  return 0;
                                        }
                                        int __cs_barrier_wait_2(__cs_barrier_t *__cs_barrier_to_wait)
                                        {
                                                  __CPROVER_assume(__cs_barrier_to_wait->init > 0);
                                                  __CPROVER_assume(__cs_barrier_to_wait->current == 0);
                                                  __cs_barrier_to_wait->current = __cs_barrier_to_wait->init;
                                                  return 0;
                                        }
                                        typedef int __cs_attr_t;
                                        struct sched_param
                                        {
                                                  signed int sched_priority;
                                        };
                                        int __cs_attr_init(__cs_attr_t *t)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_destroy(__cs_attr_t *t)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getdetachstate(const __cs_attr_t *t, int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getguardsize(const __cs_attr_t *t, unsigned int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getinheritsched(const __cs_attr_t *t, int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getschedparam(const __cs_attr_t *t, struct sched_param *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getschedpolicy(const __cs_attr_t *t, int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getscope(const __cs_attr_t *t, int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getstackaddr(const __cs_attr_t *t, void **s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_getstacksize(const __cs_attr_t *t, unsigned int *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setdetachstate(__cs_attr_t *t, int s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setguardsize(__cs_attr_t *t, unsigned int s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setinheritsched(__cs_attr_t *t, int s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setschedparam(__cs_attr_t *t, const struct sched_param *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setschedpolicy(__cs_attr_t *t, int s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setscope(__cs_attr_t *t, int s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setstackaddr(__cs_attr_t *t, void *s)
                                        {
                                                  return 0;
                                        }
                                        int __cs_attr_setstacksize(__cs_attr_t *t, unsigned int s)
                                        {
                                                  return 0;
                                        }
                                        typedef int __cs_key_t;
                                        int __cs_key_create(__cs_key_t *key)
                                        {
                                                  static int currentkey = (0);
                                                  *key = currentkey++;
                                                  return 0;
                                        }
                                        _Bool __cs_dataraceDetectionStarted = (0);
                                        _Bool __cs_dataraceSecondThread = (0);
                                        _Bool __cs_dataraceNotDetected = (1);
                                        _Bool __cs_dataraceContinue = (1);
                                        void *P0_0(void *__cs_param__arg);
                                        void *P1_0(void *__cs_param__arg);
                                        void fence();
                                        void isync();
                                        void lwfence();
                                        int __unbuffered_cnt;
                                        int __unbuffered_cnt = (0);
                                        int __unbuffered_p0_EAX;
                                        int __unbuffered_p0_EAX = (0);
                                        int __unbuffered_p1_EAX;
                                        int __unbuffered_p1_EAX = (0);
                                        int __unbuffered_p1_EBX;
                                        int __unbuffered_p1_EBX = (0);
                                        _Bool main$tmp_guard0;
                                        _Bool main$tmp_guard1;
                                        int x;
                                        int x = (0);
                                        _Bool x$flush_delayed;
                                        int x$mem_tmp;
                                        _Bool x$r_buff0_thd0;
                                        _Bool x$r_buff0_thd1;
                                        _Bool x$r_buff0_thd2;
                                        _Bool x$r_buff1_thd0;
                                        _Bool x$r_buff1_thd1;
                                        _Bool x$r_buff1_thd2;
                                        _Bool x$read_delayed;
                                        int *x$read_delayed_var;
                                        int x$w_buff0;
                                        _Bool x$w_buff0_used;
                                        int x$w_buff1;
                                        _Bool x$w_buff1_used;
                                        int y;
                                        int y = (0);
                                        _Bool weak$$choice0;
                                        _Bool weak$$choice2;
                                        void *P0_0(void *__cs_param_P0_arg)
                                        {
tP0_0_0:
IF(1,0,tP0_0_1)
                                                  ;
                                                  y = 2;
                                                  ;
tP0_0_1:
IF(1,1,tP0_0_2)
                                                  ;
                                                  ;
tP0_0_2:
IF(1,2,tP0_0_3)
                                                  ;
                                                  weak$$choice0 = nondet_bool();
                                                  weak$$choice2 = nondet_bool();
                                                  x$flush_delayed = weak$$choice2;
                                                  x$mem_tmp = x;
                                                  x = (((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x) : ((x$w_buff0_used && x$r_buff0_thd1) ? (x$w_buff0) : (x$w_buff1));
                                                  x$w_buff0 = (weak$$choice2) ? (x$w_buff0) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$w_buff0) : ((x$w_buff0_used && x$r_buff0_thd1) ? (x$w_buff0) : (x$w_buff0)));
                                                  x$w_buff1 = (weak$$choice2) ? (x$w_buff1) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$w_buff1) : ((x$w_buff0_used && x$r_buff0_thd1) ? (x$w_buff1) : (x$w_buff1)));
                                                  x$w_buff0_used = (weak$$choice2) ? (x$w_buff0_used) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$w_buff0_used) : ((x$w_buff0_used && x$r_buff0_thd1) ? ((_Bool) 0) : (x$w_buff0_used)));
                                                  x$w_buff1_used = (weak$$choice2) ? (x$w_buff1_used) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$w_buff1_used) : ((x$w_buff0_used && x$r_buff0_thd1) ? ((_Bool) 0) : ((_Bool) 0)));
                                                  x$r_buff0_thd1 = (weak$$choice2) ? (x$r_buff0_thd1) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$r_buff0_thd1) : ((x$w_buff0_used && x$r_buff0_thd1) ? ((_Bool) 0) : (x$r_buff0_thd1)));
                                                  x$r_buff1_thd1 = (weak$$choice2) ? (x$r_buff1_thd1) : ((((!x$w_buff0_used) || ((!x$r_buff0_thd1) && (!x$w_buff1_used))) || ((!x$r_buff0_thd1) && (!x$r_buff1_thd1))) ? (x$r_buff1_thd1) : ((x$w_buff0_used && x$r_buff0_thd1) ? ((_Bool) 0) : ((_Bool) 0)));
                                                  __unbuffered_p0_EAX = x;
                                                  x = (x$flush_delayed) ? (x$mem_tmp) : (x);
                                                  x$flush_delayed = (_Bool) 0;
                                                  ;
tP0_0_3:
IF(1,3,tP0_0_4)
                                                  ;
                                                  ;
tP0_0_4:
IF(1,4,tP0_0_5)
                                                  ;
                                                  __unbuffered_cnt = __unbuffered_cnt + 1;
                                                  ;
                                                  goto __exit_P0;
                                                  ;
                                                  __exit_P0:
                                                  __CPROVER_assume(__cs_pc_cs[1] >= 5);
                                                  ;
                                                  ;
tP0_0_5: 
                                                  __cs_exit(0, 1);
                                        }
                                        void *P1_0(void *__cs_param_P1_arg)
                                        {
tP1_0_0:
IF(2,0,tP1_0_1)
                                                  ;
                                                  x$w_buff1 = x$w_buff0;
                                                  x$w_buff0 = 1;
                                                  x$w_buff1_used = x$w_buff0_used;
                                                  x$w_buff0_used = (_Bool) 1;
                                                  __CPROVER_assume(!(x$w_buff1_used && x$w_buff0_used));
                                                  x$r_buff1_thd0 = x$r_buff0_thd0;
                                                  x$r_buff1_thd1 = x$r_buff0_thd1;
                                                  x$r_buff1_thd2 = x$r_buff0_thd2;
                                                  x$r_buff0_thd2 = (_Bool) 1;
                                                  ;
tP1_0_1:
IF(2,1,tP1_0_2)
                                                  ;
                                                  y = 1;
                                                  ;
tP1_0_2:
IF(2,2,tP1_0_3)
                                                  ;
                                                  __unbuffered_p1_EAX = y;
                                                  ;
tP1_0_3:
IF(2,3,tP1_0_4)
                                                  ;
                                                  __unbuffered_p1_EBX = y;
                                                  ;
tP1_0_4:
IF(2,4,tP1_0_5)
                                                  ;
                                                  x = (x$w_buff0_used && x$r_buff0_thd2) ? (x$w_buff0) : ((x$w_buff1_used && x$r_buff1_thd2) ? (x$w_buff1) : (x));
                                                  x$w_buff0_used = (x$w_buff0_used && x$r_buff0_thd2) ? ((_Bool) 0) : (x$w_buff0_used);
                                                  x$w_buff1_used = ((x$w_buff0_used && x$r_buff0_thd2) || (x$w_buff1_used && x$r_buff1_thd2)) ? ((_Bool) 0) : (x$w_buff1_used);
                                                  x$r_buff0_thd2 = (x$w_buff0_used && x$r_buff0_thd2) ? ((_Bool) 0) : (x$r_buff0_thd2);
                                                  x$r_buff1_thd2 = ((x$w_buff0_used && x$r_buff0_thd2) || (x$w_buff1_used && x$r_buff1_thd2)) ? ((_Bool) 0) : (x$r_buff1_thd2);
                                                  ;
tP1_0_5:
IF(2,5,tP1_0_6)
                                                  ;
                                                  __unbuffered_cnt = __unbuffered_cnt + 1;
                                                  ;
                                                  goto __exit_P1;
                                                  ;
                                                  __exit_P1:
                                                  __CPROVER_assume(__cs_pc_cs[2] >= 6);
                                                  ;
                                                  ;
tP1_0_6: 
                                                  __cs_exit(0, 2);
                                        }
                                        int __cs_main_thread(void)
                                        {
IF(0,0,tmain_1)
                                                  static __cs_t __cs_nondet_main_t1633;
                                                  __cs_create(&__cs_nondet_main_t1633, 0, P0_0, 0, 1);
                                                  static __cs_t __cs_nondet_main_t1634;
tmain_1:
IF(0,1,tmain_2)
                                                  __cs_create(&__cs_nondet_main_t1634, 0, P1_0, 0, 2);
tmain_2:
IF(0,2,tmain_3)
                                                  ;
                                                  main$tmp_guard0 = __unbuffered_cnt == 2;
                                                  ;
tmain_3:
IF(0,3,tmain_4)
                                                  if (((3 == __cs_pc[0]) && __cs_dataraceSecondThread) && __CPROVER_get_field(&main$tmp_guard0, "dr_write"))
                                                            __cs_dataraceNotDetected = 0;
                                                  assume_abort_if_not(main$tmp_guard0);
tmain_4:
IF(0,4,tmain_5)
                                                  ;
                                                  x = (x$w_buff0_used && x$r_buff0_thd0) ? (x$w_buff0) : ((x$w_buff1_used && x$r_buff1_thd0) ? (x$w_buff1) : (x));
                                                  x$w_buff0_used = (x$w_buff0_used && x$r_buff0_thd0) ? ((_Bool) 0) : (x$w_buff0_used);
                                                  x$w_buff1_used = ((x$w_buff0_used && x$r_buff0_thd0) || (x$w_buff1_used && x$r_buff1_thd0)) ? ((_Bool) 0) : (x$w_buff1_used);
                                                  x$r_buff0_thd0 = (x$w_buff0_used && x$r_buff0_thd0) ? ((_Bool) 0) : (x$r_buff0_thd0);
                                                  x$r_buff1_thd0 = ((x$w_buff0_used && x$r_buff0_thd0) || (x$w_buff1_used && x$r_buff1_thd0)) ? ((_Bool) 0) : (x$r_buff1_thd0);
                                                  ;
tmain_5:
IF(0,5,tmain_6)
                                                  ;
                                                  main$tmp_guard1 = !((((y == 2) && (__unbuffered_p0_EAX == 0)) && (__unbuffered_p1_EAX == 1)) && (__unbuffered_p1_EBX == 1));
                                                  ;
tmain_6:
IF(0,6,tmain_7)
                                                  if (((6 == __cs_pc[0]) && __cs_dataraceSecondThread) && __CPROVER_get_field(&main$tmp_guard1, "dr_write"))
                                                            __cs_dataraceNotDetected = 0;
                                                  __CPROVER_assume(main$tmp_guard1);
                                                  goto __exit_main;
                                                  ;
                                                  __exit_main:
                                                  __CPROVER_assume(__cs_pc_cs[0] >= 7);
                                                  ;
                                                  ;
tmain_7: 
                                                  __cs_exit(0, 0);
                                        }
                                        int main(void)
                                        {
                                                  __CPROVER_field_decl_global("dr_write", (_Bool) 0);
                                                  unsigned __CPROVER_bitvector[3] __cs_dr_ts;
                                                  __CPROVER_assume(__cs_dr_ts <= 5);
/* round  0 */
/* main */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t0_r0;
                                                  __cs_pc_cs[0] = __cs_tmp_t0_r0;
                                                  __CPROVER_assume(__cs_pc_cs[0] > 0);
                                                  __CPROVER_assume(__cs_pc_cs[0] <= 7);
                                                  if (__cs_dr_ts == 0)
                                                            __cs_dataraceDetectionStarted = 1;
                                                  __cs_main_thread();
                                                  if (__cs_dataraceDetectionStarted)
                                                            __cs_dataraceSecondThread = 1;
                                                  __cs_pc[0] = __cs_pc_cs[0];
/* P0_0 */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t1_r0;
                                                  if (__cs_dataraceContinue & __cs_active_thread[1])
                                                  {
                                                            __cs_pc_cs[1] = __cs_tmp_t1_r0;
                                                            __CPROVER_assume(__cs_pc_cs[1] <= 5);
                                                            if (__cs_dr_ts == 1)
                                                                      __cs_dataraceDetectionStarted = 1;
                                                            P0_0(__cs_threadargs[1]);
                                                            if (__cs_dataraceSecondThread & (__cs_tmp_t1_r0 > __cs_pc[1]))
                                                                      __cs_dataraceContinue = 0;
                                                            if (__cs_dataraceDetectionStarted)
                                                                      __cs_dataraceSecondThread = 1;
                                                            __cs_pc[1] = __cs_pc_cs[1];
                                                  }
/* P1_0 */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t2_r0;
                                                  if (__cs_dataraceContinue & __cs_active_thread[2])
                                                  {
                                                            __cs_pc_cs[2] = __cs_tmp_t2_r0;
                                                            __CPROVER_assume(__cs_pc_cs[2] <= 6);
                                                            if (__cs_dr_ts == 2)
                                                                      __cs_dataraceDetectionStarted = 1;
                                                            P1_0(__cs_threadargs[2]);
                                                            if (__cs_dataraceSecondThread & (__cs_tmp_t2_r0 > __cs_pc[2]))
                                                                      __cs_dataraceContinue = 0;
                                                            if (__cs_dataraceDetectionStarted)
                                                                      __cs_dataraceSecondThread = 1;
                                                            __cs_pc[2] = __cs_pc_cs[2];
                                                  }
/* round  1 */
/* main */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t0_r1;
                                                  if (((__cs_dr_ts > 0) & __cs_dataraceContinue) & __cs_active_thread[0])
                                                  {
                                                            __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r1;
                                                            __CPROVER_assume(__cs_pc_cs[0] >= __cs_pc[0]);
                                                            __CPROVER_assume(__cs_pc_cs[0] <= 7);
                                                            if (__cs_dr_ts == 3)
                                                                      __cs_dataraceDetectionStarted = 1;
                                                            __cs_main_thread();
                                                            if (__cs_dataraceSecondThread & (__cs_tmp_t0_r1 > __cs_pc[0]))
                                                                      __cs_dataraceContinue = 0;
                                                            if (__cs_dataraceDetectionStarted)
                                                                      __cs_dataraceSecondThread = 1;
                                                            __cs_pc[0] = __cs_pc_cs[0];
                                                  }
/* P0_0 */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t1_r1;
                                                  if (((__cs_dr_ts > 1) & __cs_dataraceContinue) & __cs_active_thread[1])
                                                  {
                                                            __cs_pc_cs[1] = __cs_pc[1] + __cs_tmp_t1_r1;
                                                            __CPROVER_assume(__cs_pc_cs[1] >= __cs_pc[1]);
                                                            __CPROVER_assume(__cs_pc_cs[1] <= 5);
                                                            if (__cs_dr_ts == 4)
                                                                      __cs_dataraceDetectionStarted = 1;
                                                            P0_0(__cs_threadargs[1]);
                                                            if (__cs_dataraceSecondThread & (__cs_tmp_t1_r1 > __cs_pc[1]))
                                                                      __cs_dataraceContinue = 0;
                                                            if (__cs_dataraceDetectionStarted)
                                                                      __cs_dataraceSecondThread = 1;
                                                            __cs_pc[1] = __cs_pc_cs[1];
                                                  }
/* P1_0 */
                                                  unsigned __CPROVER_bitvector[3] __cs_tmp_t2_r1;
                                                  if (((__cs_dr_ts > 2) & __cs_dataraceContinue) & __cs_active_thread[2])
                                                  {
                                                            __cs_pc_cs[2] = __cs_pc[2] + __cs_tmp_t2_r1;
                                                            __CPROVER_assume(__cs_pc_cs[2] >= __cs_pc[2]);
                                                            __CPROVER_assume(__cs_pc_cs[2] <= 6);
                                                            if (__cs_dr_ts == 5)
                                                                      __cs_dataraceDetectionStarted = 1;
                                                            P1_0(__cs_threadargs[2]);
                                                            if (__cs_dataraceSecondThread & (__cs_tmp_t2_r1 > __cs_pc[2]))
                                                                      __cs_dataraceContinue = 0;
                                                            if (__cs_dataraceDetectionStarted)
                                                                      __cs_dataraceSecondThread = 1;
                                                            __cs_pc[2] = __cs_pc_cs[2];
                                                  }
                                                  __CPROVER_assert(__cs_dataraceNotDetected, "Data race failure");
                                                  return 0;
                                        }
                                        
