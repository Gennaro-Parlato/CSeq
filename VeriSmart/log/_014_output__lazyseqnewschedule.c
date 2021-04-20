unsigned int __cs_active_thread[4]={};
unsigned int __cs_pc[4];
unsigned int __cs_pc_cs[4];
unsigned int __cs_last_thread;
unsigned int __cs_thread_lines[4] = {1, 3, 3, 6};
void *malloc(unsigned long int);
void *__cs_safe_malloc(unsigned int __cs_size) {
	void *__cs_ptr = malloc(__cs_size);
	return __cs_ptr;
}

void __CSEQ_message(char *__cs_message) { ; }

typedef int __cs_t;

void *__cs_threadargs[4];
void *__cs_thread_joinargs[4];

int __cs_create(__cs_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_thread_function)(void*), void *__cs_arg, int __cs_threadID) {
	if (__cs_threadID > THREADS) return 0;
	*__cs_new_thread_id = __cs_threadID;
	__cs_active_thread[__cs_threadID] = 1;
	__cs_threadargs[__cs_threadID] = __cs_arg;
	__CSEQ_message("thread spawned");
	return 0;
}

int __cs_join(__cs_t __cs_id, void **__cs_value_ptr) {
	__CSEQ_assume(__cs_pc[__cs_id] == __cs_thread_lines[__cs_id]);
	*__cs_value_ptr = __cs_thread_joinargs[__cs_id];
	return 0;
}

int __cs_exit(void *__cs_value_ptr, unsigned int __cs_thread_index) {
	__cs_thread_joinargs[__cs_thread_index] = __cs_value_ptr;
	return 0;
}

int __cs_self(void) { return 1; }

typedef int __cs_mutex_t;

int __cs_mutex_init (__cs_mutex_t *__cs_m, int __cs_val) {
	*__cs_m = -1;
	return 0;
}

int __cs_mutex_destroy(__cs_mutex_t *__cs_mutex_to_destroy) {
	__CSEQ_assume(*__cs_mutex_to_destroy!=0);
	__CSEQ_assume(*__cs_mutex_to_destroy!=-2);
	__CSEQ_assume(*__cs_mutex_to_destroy==-1);
	*__cs_mutex_to_destroy = -2;
	__CSEQ_message("lock destroyed");
	return 0;
}

int __cs_mutex_lock(__cs_mutex_t *__cs_mutex_to_lock, unsigned int __cs_thread_index) {
	__CSEQ_assume(*__cs_mutex_to_lock!=0);
	__CSEQ_assume(*__cs_mutex_to_lock!=-2);
	__CSEQ_assume(*__cs_mutex_to_lock==-1);
	*__cs_mutex_to_lock = __cs_thread_index+1;
	__CSEQ_message("lock acquired");
	return 0;
}

int __cs_mutex_unlock(__cs_mutex_t *__cs_mutex_to_unlock, unsigned int __cs_thread_index) {
	__CSEQ_assume(*__cs_mutex_to_unlock!=0);
	__CSEQ_assume(*__cs_mutex_to_unlock!=-2);
	__CSEQ_assume(*__cs_mutex_to_unlock==(__cs_thread_index+1));
	*__cs_mutex_to_unlock = -1;
	__CSEQ_message("lock released");
	return 0;
}

typedef int __cs_cond_t;

int __cs_cond_init(__cs_cond_t *__cs_cond_to_init, void *__cs_attr) {
	*__cs_cond_to_init = -1;
	return 0;
}

int __cs_cond_destroy(__cs_cond_t *__cs_cond_to_destroy) {
	*__cs_cond_to_destroy = -2;
	return 0;
}

int __cs_cond_wait_1(__cs_cond_t *__cs_cond_to_wait_for, __cs_mutex_t *__cs_m, unsigned int __cs_thread_index) {
	__CSEQ_assume(*__cs_cond_to_wait_for!=0);
	__CSEQ_assume(*__cs_cond_to_wait_for!=-2);
	__cs_mutex_unlock(__cs_m, __cs_thread_index);
	return 0;
}

int __cs_cond_wait_2(__cs_cond_t *__cs_cond_to_wait_for, __cs_mutex_t *__cs_m, unsigned int __cs_thread_index) {
	__CSEQ_assume(*__cs_cond_to_wait_for == 1);
	__cs_mutex_lock(__cs_m, __cs_thread_index);
	return 0;
}

int __cs_cond_signal(__cs_cond_t *__cs_cond_to_signal) {
	*__cs_cond_to_signal = 1;
	__CSEQ_message("conditional variable signal");
	return 0;
}

int __cs_cond_broadcast(__cs_cond_t *__cs_cond_to_broadcast) {
	*__cs_cond_to_broadcast = 1;
	__CSEQ_message("conditional variable broadcast");
	return 0;
}

typedef struct __cs_barrier_t{
	unsigned int init;
	unsigned int current;
} __cs_barrier_t;

int __cs_barrier_init(__cs_barrier_t *__cs_barrier_to_init, void * __cs_attr, unsigned int count){
	__CSEQ_assume(count > 0);
	__cs_barrier_to_init->current = count;
	__cs_barrier_to_init->init = count;
	return 0;
}

int __cs_barrier_destroy(__cs_barrier_t *__cs_barrier_to_destroy) {
	__cs_barrier_to_destroy->init = -1;
	__cs_barrier_to_destroy->current = -1;
	return 0;
}


int __cs_barrier_wait_1(__cs_barrier_t *__cs_barrier_to_wait){
	__CSEQ_assume(__cs_barrier_to_wait->init > 0); 
	__cs_barrier_to_wait->current--;
	return 0;
}

int __cs_barrier_wait_2(__cs_barrier_t *__cs_barrier_to_wait){
	__CSEQ_assume(__cs_barrier_to_wait->init > 0); 
	__CSEQ_assume(__cs_barrier_to_wait->current == 0);
	__cs_barrier_to_wait->current = __cs_barrier_to_wait->init;
	return 0;
}

typedef int __cs_attr_t;

struct sched_param {
   signed int sched_priority;
}; 

int   __cs_attr_init(__cs_attr_t * t) { return 0;}
int   __cs_attr_destroy(__cs_attr_t * t) { return 0;}
int   __cs_attr_getdetachstate(const __cs_attr_t * t, int * s) { return 0;}
int   __cs_attr_getguardsize(const __cs_attr_t * t, unsigned int * s) { return 0;}
int   __cs_attr_getinheritsched(const __cs_attr_t * t, int * s) { return 0;}
int   __cs_attr_getschedparam(const __cs_attr_t * t, struct sched_param * s) { return 0;}
int   __cs_attr_getschedpolicy(const __cs_attr_t * t, int * s) { return 0;}
int   __cs_attr_getscope(const __cs_attr_t * t, int * s) { return 0;}
int   __cs_attr_getstackaddr(const __cs_attr_t * t, void ** s) { return 0;}
int   __cs_attr_getstacksize(const __cs_attr_t * t, unsigned int *s) { return 0;}
int   __cs_attr_setdetachstate(__cs_attr_t * t, int s) { return 0;}
int   __cs_attr_setguardsize(__cs_attr_t * t, unsigned int s) { return 0;}
int   __cs_attr_setinheritsched(__cs_attr_t * t, int s) { return 0;}
int   __cs_attr_setschedparam(__cs_attr_t * t, const struct sched_param * s) { return 0;}
int   __cs_attr_setschedpolicy(__cs_attr_t * t, int s) { return 0;}
int   __cs_attr_setscope(__cs_attr_t * t, int s) { return 0;}
int   __cs_attr_setstackaddr(__cs_attr_t * t, void * s) { return 0;}
int   __cs_attr_setstacksize(__cs_attr_t * t, unsigned int s) { return 0;}

typedef int __cs_key_t;


int __cs_key_create(__cs_key_t *key) {
        static int currentkey = 0;
        *key = currentkey++;
        return 0;
}
_Bool __cs_dataraceDetectionStarted = 0; 
_Bool __cs_dataraceSecondThread = 0; 
_Bool __cs_dataraceNotDetected = 1; 
_Bool __cs_dataraceContinue = 1; 
void __VERIFIER_error();
typedef int _____STARTSTRIPPINGFROMHERE_____;
typedef int __cs_barrier_t;
typedef int __cs_barrierattr_t;
typedef int __cs_attr_t;
typedef int __cs_cond_t;
typedef int __cs_condattr_t;
typedef int __cs_key_t;
typedef int __cs_mutex_t;
typedef int __cs_mutexattr_t;
typedef int __cs_once_t;
typedef int __cs_rwlock_t;
typedef int __cs_rwlockattr_t;
typedef int __cs_t;
typedef int size_t;
typedef int __builtin_va_list;
typedef int __gnuc_va_list;
typedef int __int8_t;
typedef int __uint8_t;
typedef int __int16_t;
typedef int __uint16_t;
typedef int __int_least16_t;
typedef int __uint_least16_t;
typedef int __int32_t;
typedef int __uint32_t;
typedef int __int64_t;
typedef int __uint64_t;
typedef int __int_least32_t;
typedef int __uint_least32_t;
typedef int __s8;
typedef int __u8;
typedef int __s16;
typedef int __u16;
typedef int __s32;
typedef int __u32;
typedef int u32;
typedef int __s64;
typedef int __u64;
typedef int _LOCK_T;
typedef int _LOCK_RECURSIVE_T;
typedef int _off_t;
typedef int __dev_t;
typedef int __uid_t;
typedef int __gid_t;
typedef int _off64_t;
typedef int _fpos_t;
typedef int _ssize_t;
typedef int wint_t;
typedef int _mbstate_t;
typedef int _flock_t;
typedef int _iconv_t;
typedef int __ULong;
typedef int __FILE;
typedef int ptrdiff_t;
typedef int wchar_t;
typedef int __off_t;
typedef int __pid_t;
typedef int __loff_t;
typedef int u_char;
typedef int u_short;
typedef int u_int;
typedef int u_long;
typedef int ushort;
typedef int uint;
typedef int clock_t;
typedef int time_t;
typedef int daddr_t;
typedef int caddr_t;
typedef int ino_t;
typedef int off_t;
typedef int dev_t;
typedef int uid_t;
typedef int gid_t;
typedef int pid_t;
typedef int key_t;
typedef int ssize_t;
typedef int mode_t;
typedef int nlink_t;
typedef int fd_mask;
typedef int _types_fd_set;
typedef int fd_set;
typedef int clockid_t;
typedef int timer_t;
typedef int useconds_t;
typedef int suseconds_t;
typedef int FILE;
typedef int fpos_t;
typedef int cookie_read_function_t;
typedef int cookie_write_function_t;
typedef int cookie_seek_function_t;
typedef int cookie_close_function_t;
typedef int cookie_io_functions_t;
typedef int div_t;
typedef int ldiv_t;
typedef int lldiv_t;
typedef int sigset_t;
typedef int __sigset_t;
typedef int _sig_func_ptr;
typedef int sig_atomic_t;
typedef int __tzrule_type;
typedef int __tzinfo_type;
typedef int mbstate_t;
typedef int sem_t;
typedef int pthread_t;
typedef int pthread_attr_t;
typedef int pthread_mutex_t;
typedef int pthread_mutexattr_t;
typedef int pthread_cond_t;
typedef int pthread_condattr_t;
typedef int pthread_key_t;
typedef int pthread_once_t;
typedef int pthread_rwlock_t;
typedef int pthread_rwlockattr_t;
typedef int pthread_spinlock_t;
typedef int pthread_barrier_t;
typedef int pthread_barrierattr_t;
typedef int jmp_buf;
typedef int rlim_t;
typedef int sa_family_t;
typedef int sigjmp_buf;
typedef int stack_t;
typedef int siginfo_t;
typedef int z_stream;
typedef int int8_t;
typedef int uint8_t;
typedef int int16_t;
typedef int uint16_t;
typedef int int32_t;
typedef int uint32_t;
typedef int int64_t;
typedef int uint64_t;
typedef int int_least8_t;
typedef int uint_least8_t;
typedef int int_least16_t;
typedef int uint_least16_t;
typedef int int_least32_t;
typedef int uint_least32_t;
typedef int int_least64_t;
typedef int uint_least64_t;
typedef int int_fast8_t;
typedef int uint_fast8_t;
typedef int int_fast16_t;
typedef int uint_fast16_t;
typedef int int_fast32_t;
typedef int uint_fast32_t;
typedef int int_fast64_t;
typedef int uint_fast64_t;
typedef int intptr_t;
typedef int uintptr_t;
typedef int intmax_t;
typedef int uintmax_t;
typedef _Bool bool;
typedef void BZFILE;
typedef int va_list;
typedef int loff_t;
typedef unsigned char __gcc_v2di;
typedef unsigned char __gcc_v16qi;
typedef unsigned char __gcc_v4si;
typedef int dma_addr_t;
typedef int raw_spinlock_t;
typedef int wait_queue_head_t;
typedef int wait_queue_t;
typedef int gfp_t;
typedef int spinlock_t;
typedef int poll_table;
typedef int iobuff_t;
typedef int resource_size_t;
typedef int socklen_t;
typedef int evutil_socket_t;
typedef int _____STOPSTRIPPINGFROMHERE_____;
__cs_mutex_t m;
int data = 0;
void *thread1_0(void *__cs_param_thread1_arg)
{
$I1if ( ($L == __cs_pc_cs[0]) & __cs_dataraceDetectionStarted & !__cs_dataraceSecondThread) {
__CPROVER_set_field(&data,"dr_write",1);
}
$I2if ( ($L == __cs_pc[0]) & __cs_dataraceSecondThread & (__CPROVER_get_field(&data,"dr_write"))) __cs_dataraceNotDetected = 0;$I3
data++;
__exit_thread1: $G;;
$F 
__cs_exit(0, 0);
}
typedef struct anonstruct_0
{
char nome[30];
int x;
int y;
int z;
} luogo;
void *thread2_0(void *__cs_param_thread2_arg)
{
static luogo __cs_nondet_thread2_l;
static luogo *__cs_nondet_thread2_p;
$I1$I2$I3
__cs_nondet_thread2_l.x = 10;
$I1$I2$I3
__cs_nondet_thread2_p = (luogo) __cs_safe_malloc(sizeof(luogo));
$I1if ( ($L == __cs_pc_cs[1]) & __cs_dataraceDetectionStarted & !__cs_dataraceSecondThread) {
__CPROVER_set_field(__cs_nondet_thread2_p,"dr_write",1);
}
$I2if ( ($L == __cs_pc[1]) & __cs_dataraceSecondThread & (__CPROVER_get_field(__cs_nondet_thread2_p,"dr_write"))) __cs_dataraceNotDetected = 0;$I3
(*__cs_nondet_thread2_p).x = 100;
__exit_thread2: $G;;
$F 
__cs_exit(0, 1);
}
void *thread3_0(void *__cs_param_thread3_arg)
{
$I1$I2$I3
__cs_mutex_lock(&m, 2);
;;
static _Bool __cs_nondet_thread3___cs_tmp_if_cond_0;
$I1$I2if ( ($L == __cs_pc[2]) & __cs_dataraceSecondThread & (__CPROVER_get_field(&data,"dr_write"))) __cs_dataraceNotDetected = 0;$I3
__cs_nondet_thread3___cs_tmp_if_cond_0 = data >= 3;
if (__cs_nondet_thread3___cs_tmp_if_cond_0)
{
__CSEQ_assert(0);
;;
};
$I1$I2$I3
__cs_mutex_unlock(&m, 2);
__exit_thread3: $G;;
$F 
__cs_exit(0, 2);
}
int main_thread(void)
{
$I1$I2$I3
__cs_mutex_init(&m, 0);
static __cs_t __cs_nondet_main_t1;
static __cs_t __cs_nondet_main_t2;
static __cs_t __cs_nondet_main_t3;
__cs_create(&__cs_nondet_main_t1, 0, thread1_0, 0, 0);
$I1$I2$I3
__cs_create(&__cs_nondet_main_t2, 0, thread2_0, 0, 1);
$I1$I2$I3
__cs_create(&__cs_nondet_main_t3, 0, thread3_0, 0, 2);
$I1$I2$I3
__cs_join(__cs_nondet_main_t1, 0);
$I1$I2$I3
__cs_join(__cs_nondet_main_t2, 0);
$I1$I2$I3
__cs_join(__cs_nondet_main_t3, 0);
goto __exit_main;;
__exit_main: $G;;
$F 
__cs_exit(0, 3);
}
int main(void) {
__CPROVER_field_decl_global("dr_write", (_Bool) 0); 
          unsigned int __cs_dr_ts ;
          __CSEQ_assume(__cs_dr_ts <= 2);
__CSEQ_rawline("/* round  0 */");
__CSEQ_rawline("    /* main */");
__cs_active_thread[3] = 1;
          unsigned int __cs_tmp_t3_r0 ;
          __cs_pc_cs[3] = __cs_tmp_t3_r0;
          __CSEQ_assume(__cs_pc_cs[3] > 0);
          __CSEQ_assume(__cs_pc_cs[3] <= $ML3);
          if(__cs_dr_ts == 0) __cs_dataraceDetectionStarted=1;
          main_thread();
          if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;
          __cs_pc[3] = __cs_pc_cs[3];

__CSEQ_rawline("    /* thread1_0 */");
         unsigned int __cs_tmp_t0_r0 ;
         if (__cs_dataraceContinue & __cs_active_thread[0]) {
             __cs_pc_cs[0] = __cs_tmp_t0_r0;
             __CSEQ_assume(__cs_pc_cs[0] <= $ML0);
             if(__cs_dr_ts == 1) __cs_dataraceDetectionStarted=1;
             thread1_0(__cs_threadargs[0]);
             if(__cs_dataraceSecondThread & (__cs_tmp_t0_r0 > __cs_pc[0])) __cs_dataraceContinue=0;
             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;
             __cs_pc[0] = __cs_pc_cs[0];
         }

__CSEQ_rawline("    /* thread2_0 */");
         unsigned int __cs_tmp_t1_r0 ;
         if (__cs_dataraceContinue & __cs_active_thread[1]) {
             __cs_pc_cs[1] = __cs_tmp_t1_r0;
             __CSEQ_assume(__cs_pc_cs[1] <= $ML1);
             if(__cs_dr_ts == 2) __cs_dataraceDetectionStarted=1;
             thread2_0(__cs_threadargs[1]);
             if(__cs_dataraceSecondThread & (__cs_tmp_t1_r0 > __cs_pc[1])) __cs_dataraceContinue=0;
             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;
             __cs_pc[1] = __cs_pc_cs[1];
         }

__CSEQ_rawline("    /* thread3_0 */");
         unsigned int __cs_tmp_t2_r0 ;
         if (__cs_dataraceContinue & __cs_active_thread[2]) {
             __cs_pc_cs[2] = __cs_tmp_t2_r0;
             __CSEQ_assume(__cs_pc_cs[2] <= $ML2);
             thread3_0(__cs_threadargs[2]);
             if(__cs_dataraceSecondThread & (__cs_tmp_t2_r0 > __cs_pc[2])) __cs_dataraceContinue=0;
             __cs_pc[2] = __cs_pc_cs[2];
         }

     __CPROVER_assert(__cs_dataraceNotDetected,"Data race failure");
    return 0;
}

