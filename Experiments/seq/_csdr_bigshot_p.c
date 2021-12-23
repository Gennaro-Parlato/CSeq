/*
 *  generated by CSeq [ 0000 / 0000 ]
 * 
 *  instance version    {"thread1_0": [[1, 1]], "thread2_0": [[1, 3]], "main": [[1, 5]]}
 *
 *  2021-07-01 10:16:25
 *
 *  params:
 *    -i /home/salvatore/ShadowMemory/svcomp2020-concurrency-benchmarks/pthread/bigshot_p.i, --rounds 3, --unwind 4, --seq , --dr , --debug , 
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
#define ROUNDS 3
#define STOP_VOID(A) return;
#define STOP_NONVOID(A) return 0;
#define IF(T,A,B) if ((__cs_pc[T] > A) | (A >= __cs_pc_cs[T])) goto B;
#define SMSIZE 5
                                        unsigned __CPROVER_bitvector[1] __cs_active_thread[3] = {};
                                        unsigned __CPROVER_bitvector[3] __cs_pc[3];
                                        unsigned __CPROVER_bitvector[4] __cs_pc_cs[3];
                                        unsigned __CPROVER_bitvector[2] __cs_last_thread;
                                        unsigned __CPROVER_bitvector[3] __cs_thread_lines[3] = {1, 3, 5};
                                        void *__cs_safe_malloc(unsigned int __cs_size)
                                        {
                                        void *__cs_ptr = (malloc(__cs_size));
                                        return __cs_ptr;
                                        }
                                        void __cs_init_scalar(void *__cs_var, unsigned int __cs_size)
                                        {
                                        if (__cs_size == (sizeof(int)))
                                        *((int *) __cs_var) = nondet_int();
                                                else
                                                {
                                        __cs_var = malloc(__cs_size);
                                                }
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
                                        __CPROVER_assert((*__cs_mutex_to_destroy) != 0, "attempt to destroy an uninitialized mutex");
                                        __CPROVER_assert((*__cs_mutex_to_destroy) != (-2), "attempt to destroy a previously destroyed mutex");
                                        __CPROVER_assert((*__cs_mutex_to_destroy) == (-1), "attempt to destroy a locked mutex");
                                        *__cs_mutex_to_destroy = -2;
                                        __CSEQ_message("lock destroyed");
                                        return 0;
                                        }
                                        int __cs_mutex_lock(__cs_mutex_t *__cs_mutex_to_lock, unsigned __CPROVER_bitvector[2] __cs_thread_index)
                                        {
                                        __CPROVER_assert((*__cs_mutex_to_lock) != 0, "attempt to lock an uninitialized mutex");
                                        __CPROVER_assert((*__cs_mutex_to_lock) != (-2), "attempt to lock a destroyed mutex");
                                        __CPROVER_assume((*__cs_mutex_to_lock) == (-1));
                                        *__cs_mutex_to_lock = __cs_thread_index + 1;
                                        __CSEQ_message("lock acquired");
                                        return 0;
                                        }
                                        int __cs_mutex_unlock(__cs_mutex_t *__cs_mutex_to_unlock, unsigned __CPROVER_bitvector[2] __cs_thread_index)
                                        {
                                        __CPROVER_assert((*__cs_mutex_to_unlock) != 0, "attempt to unlock an uninitialized mutex");
                                        __CPROVER_assert((*__cs_mutex_to_unlock) != (-2), "attempt to unlock a destroyed mutex");
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
                                        __CPROVER_assert((*__cs_cond_to_wait_for) != 0, "attempt to use an uninitialized conditional variable");
                                        __CPROVER_assert((*__cs_cond_to_wait_for) != (-2), "attempt to use a destroyed conditional variable");
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
                                        __CPROVER_assert(count > 0, "count must be greater than 0");
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
                                        __CPROVER_assert(__cs_barrier_to_wait->init > 0, "attempt to use an uninitialized barrier variable");
                                        __cs_barrier_to_wait->current--;
                                        return 0;
                                        }
                                        int __cs_barrier_wait_2(__cs_barrier_t *__cs_barrier_to_wait)
                                        {
                                        __CPROVER_assert(__cs_barrier_to_wait->init > 0, "attempt to use an uninitialized barrier variable");
                                        __CPROVER_assume(__cs_barrier_to_wait->current == 0);
                                        __cs_barrier_to_wait->current = __cs_barrier_to_wait->init;
                                        return 0;
                                        }
                                        typedef int __cs_attr_t;
                                        struct sched_param
                                        {
                                        int sched_priority;
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
                                        void *__cs_getspecific(__cs_key_t key)
                                        {
                                                return (void *) 0;
                                        }
                                        int __cs__setspecific(__cs_key_t key, const void *value)
                                        {
                                                return 0;
                                        }
                                        int __cs_key_create(__cs_key_t *key)
                                        {
                                                return 0;
                                        }
                                        _Bool __cs_dataraceDetectionStarted = (0);
                                        _Bool __cs_dataraceSecondThread = (0);
                                        _Bool __cs_dataraceNotDetected = (1);
                                        _Bool __cs_dataraceContinue = (1);
                                        _Bool __cs_dataraceActiveVP1 = (0);
                                        _Bool __cs_dataraceActiveVP2 = (0);
                                        char *v;
                                        void *thread1_0(void *__cs_param_thread1_arg)
                                        {
IF(0,0,tthread1_0_1)
                                                __cs_dataraceActiveVP1 = 0 == (__cs_pc_cs[0] - 1);
                                        __cs_dataraceActiveVP2 = 0 == __cs_pc[0];
                                        ((__cs_dataraceActiveVP1 && __cs_dataraceDetectionStarted) && (!__cs_dataraceSecondThread)) && __CPROVER_set_field(&v, "dr_write", 1), (__cs_dataraceActiveVP2 && __cs_dataraceSecondThread) && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && (!__CPROVER_get_field(&v, "dr_write"))), v = calloc(8, sizeof(char));
                                        goto __exit_thread1;
                                                ;
                                        __exit_thread1:
                                                __CPROVER_assume(__cs_pc_cs[0] >= 1);
                                        ;
                                                ;
tthread1_0_1: 
                                        __cs_exit(0, 0);
                                        }
                                        void *thread2_0(void *__cs_param_thread2_arg)
                                        {
IF(1,0,tthread2_0_1)
                                                __cs_dataraceActiveVP1 = 0 == (__cs_pc_cs[1] - 1);
                                        __cs_dataraceActiveVP2 = 0 == __cs_pc[1];
                                        ;
                                                ;
                                        static _Bool __cs_nondet_thread2___cs_tmp_if_cond_1;
tthread2_0_1:
IF(1,1,tthread2_0_2)
                                                __cs_dataraceActiveVP1 = 1 == (__cs_pc_cs[1] - 1);
                                        __cs_dataraceActiveVP2 = 1 == __cs_pc[1];
                                        ((__cs_dataraceActiveVP1 && __cs_dataraceDetectionStarted) && (!__cs_dataraceSecondThread)) && __CPROVER_set_field(&__cs_nondet_thread2___cs_tmp_if_cond_1, "dr_write", 1), (__cs_dataraceActiveVP2 && __cs_dataraceSecondThread) && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && (!__CPROVER_get_field(&__cs_nondet_thread2___cs_tmp_if_cond_1, "dr_write"))), __cs_nondet_thread2___cs_tmp_if_cond_1 = v;
                                        if ((__cs_dataraceActiveVP2 && __cs_dataraceSecondThread) && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && (!__CPROVER_get_field(&__cs_nondet_thread2___cs_tmp_if_cond_1, "dr_write"))), __cs_nondet_thread2___cs_tmp_if_cond_1)
                                                {
tthread2_0_2:
IF(1,2,tthread2_0_3)
                                        strcpy(v, "Bigshot");
                                                }
                                        __CPROVER_assume(__cs_pc_cs[1] >= 3);
                                        ;
                                        goto __exit_thread2;
                                                ;
                                        __exit_thread2:
                                                __CPROVER_assume(__cs_pc_cs[1] >= 3);
                                        ;
                                                ;
tthread2_0_3: 
                                        __cs_exit(0, 1);
                                        }
                                        int main_thread(void)
                                        {
IF(2,0,tmain_thread_1)
                                                __cs_dataraceActiveVP1 = 0 == (__cs_pc_cs[2] - 1);
                                        __cs_dataraceActiveVP2 = 0 == __cs_pc[2];
                                        static __cs_t __cs_nondet_main_t1;
                                        static __cs_t __cs_nondet_main_t2;
                                        __cs_create(&__cs_nondet_main_t1, 0, thread1_0, 0, 0);
tmain_thread_1:
IF(2,1,tmain_thread_2)
                                        __cs_create(&__cs_nondet_main_t2, 0, thread2_0, 0, 1);
tmain_thread_2:
IF(2,2,tmain_thread_3)
                                                __cs_dataraceActiveVP2 = 2 == __cs_pc[2];
                                        __cs_join(((__cs_dataraceActiveVP2 && __cs_dataraceSecondThread) && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && (!__CPROVER_get_field(&__cs_nondet_main_t1, "dr_write"))), __cs_nondet_main_t1), 0);
tmain_thread_3:
IF(2,3,tmain_thread_4)
                                                __cs_dataraceActiveVP2 = 3 == __cs_pc[2];
                                        __cs_join(((__cs_dataraceActiveVP2 && __cs_dataraceSecondThread) && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && (!__CPROVER_get_field(&__cs_nondet_main_t2, "dr_write"))), __cs_nondet_main_t2), 0);
tmain_thread_4:
IF(2,4,tmain_thread_5)
                                                __cs_dataraceActiveVP2 = 4 == __cs_pc[2];
                                        __CPROVER_assume((!v) || (v[0] == 'B'));
                                        goto __exit_main;
                                                ;
                                        __exit_main:
                                                __CPROVER_assume(__cs_pc_cs[2] >= 5);
                                        ;
                                                ;
tmain_thread_5: 
                                        __cs_exit(0, 2);
                                        }
                                        int main(void)
                                        {
                                        __CPROVER_field_decl_global("dr_write", (_Bool) 0);
                                        __CPROVER_field_decl_local("dr_write", (_Bool) 0);
                                        unsigned __CPROVER_bitvector[3] __cs_dr_ts;
                                        __CPROVER_assume(__cs_dr_ts <= 7);
/* round  0 */
/* main */
                                        __cs_active_thread[2] = 1;
                                        unsigned __CPROVER_bitvector[3] __cs_tmp_t2_r0;
                                        __cs_pc_cs[2] = __cs_tmp_t2_r0;
                                        __CPROVER_assume(__cs_pc_cs[2] > 0);
                                        __CPROVER_assume(__cs_pc_cs[2] <= 5);
                                        if (__cs_dr_ts == 0)
                                                        __cs_dataraceDetectionStarted = 1;
                                        main_thread();
                                        if (__cs_dataraceDetectionStarted)
                                                        __cs_dataraceSecondThread = 1;
                                        __cs_pc[2] = __cs_pc_cs[2];
/* thread1_0 */
                                        unsigned __CPROVER_bitvector[1] __cs_tmp_t0_r0;
                                        if (__cs_dataraceContinue & __cs_active_thread[0])
                                                {
                                        __cs_pc_cs[0] = __cs_tmp_t0_r0;
                                        __CPROVER_assume(__cs_pc_cs[0] <= 1);
                                        if (__cs_dr_ts == 1)
                                                                __cs_dataraceDetectionStarted = 1;
                                        thread1_0(__cs_threadargs[0]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t0_r0 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[0] = __cs_pc_cs[0];
                                                }
/* thread2_0 */
                                        unsigned __CPROVER_bitvector[2] __cs_tmp_t1_r0;
                                        if (__cs_dataraceContinue & __cs_active_thread[1])
                                                {
                                        __cs_pc_cs[1] = __cs_tmp_t1_r0;
                                        __CPROVER_assume(__cs_pc_cs[1] <= 3);
                                        if (__cs_dr_ts == 2)
                                                                __cs_dataraceDetectionStarted = 1;
                                        thread2_0(__cs_threadargs[1]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t1_r0 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[1] = __cs_pc_cs[1];
                                                }
/* round  1 */
/* main */
                                        unsigned __CPROVER_bitvector[3] __cs_tmp_t2_r1;
                                        if (((__cs_dr_ts > 0) & __cs_dataraceContinue) & __cs_active_thread[2])
                                                {
                                        __cs_pc_cs[2] = __cs_pc[2] + __cs_tmp_t2_r1;
                                        __CPROVER_assume(__cs_pc_cs[2] >= __cs_pc[2]);
                                        __CPROVER_assume(__cs_pc_cs[2] <= 5);
                                        if (__cs_dr_ts == 3)
                                                                __cs_dataraceDetectionStarted = 1;
                                        main_thread();
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t2_r1 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[2] = __cs_pc_cs[2];
                                                }
/* thread1_0 */
                                        unsigned __CPROVER_bitvector[1] __cs_tmp_t0_r1;
                                        if (((__cs_dr_ts > 1) & __cs_dataraceContinue) & __cs_active_thread[0])
                                                {
                                        __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r1;
                                        __CPROVER_assume(__cs_pc_cs[0] >= __cs_pc[0]);
                                        __CPROVER_assume(__cs_pc_cs[0] <= 1);
                                        if (__cs_dr_ts == 4)
                                                                __cs_dataraceDetectionStarted = 1;
                                        thread1_0(__cs_threadargs[0]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t0_r1 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[0] = __cs_pc_cs[0];
                                                }
/* thread2_0 */
                                        unsigned __CPROVER_bitvector[2] __cs_tmp_t1_r1;
                                        if (((__cs_dr_ts > 2) & __cs_dataraceContinue) & __cs_active_thread[1])
                                                {
                                        __cs_pc_cs[1] = __cs_pc[1] + __cs_tmp_t1_r1;
                                        __CPROVER_assume(__cs_pc_cs[1] >= __cs_pc[1]);
                                        __CPROVER_assume(__cs_pc_cs[1] <= 3);
                                        if (__cs_dr_ts == 5)
                                                                __cs_dataraceDetectionStarted = 1;
                                        thread2_0(__cs_threadargs[1]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t1_r1 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[1] = __cs_pc_cs[1];
                                                }
/* round  2 */
/* main */
                                        unsigned __CPROVER_bitvector[3] __cs_tmp_t2_r2;
                                        if (((__cs_dr_ts > 3) & __cs_dataraceContinue) & __cs_active_thread[2])
                                                {
                                        __cs_pc_cs[2] = __cs_pc[2] + __cs_tmp_t2_r2;
                                        __CPROVER_assume(__cs_pc_cs[2] >= __cs_pc[2]);
                                        __CPROVER_assume(__cs_pc_cs[2] <= 5);
                                        if (__cs_dr_ts == 6)
                                                                __cs_dataraceDetectionStarted = 1;
                                        main_thread();
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t2_r2 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[2] = __cs_pc_cs[2];
                                                }
/* thread1_0 */
                                        unsigned __CPROVER_bitvector[1] __cs_tmp_t0_r2;
                                        if (((__cs_dr_ts > 4) & __cs_dataraceContinue) & __cs_active_thread[0])
                                                {
                                        __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r2;
                                        __CPROVER_assume(__cs_pc_cs[0] >= __cs_pc[0]);
                                        __CPROVER_assume(__cs_pc_cs[0] <= 1);
                                        if (__cs_dr_ts == 7)
                                                                __cs_dataraceDetectionStarted = 1;
                                        thread1_0(__cs_threadargs[0]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t0_r2 > 0))
                                                                __cs_dataraceContinue = 0;
                                        if (__cs_dataraceDetectionStarted)
                                                                __cs_dataraceSecondThread = 1;
                                        __cs_pc[0] = __cs_pc_cs[0];
                                                }
/* thread2_0 */
                                        unsigned __CPROVER_bitvector[2] __cs_tmp_t1_r2;
                                        if (((__cs_dr_ts > 5) & __cs_dataraceContinue) & __cs_active_thread[1])
                                                {
                                        __cs_pc_cs[1] = __cs_pc[1] + __cs_tmp_t1_r2;
                                        __CPROVER_assume(__cs_pc_cs[1] >= __cs_pc[1]);
                                        __CPROVER_assume(__cs_pc_cs[1] <= 3);
                                        thread2_0(__cs_threadargs[1]);
                                        if (__cs_dataraceSecondThread & (__cs_tmp_t1_r2 > 0))
                                                                __cs_dataraceContinue = 0;
                                        __cs_pc[1] = __cs_pc_cs[1];
                                                }
                                        __CPROVER_assert(__cs_dataraceNotDetected, "Data race failure");
                                        return 0;
                                        }
                                        
