

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




void *thread1(void *__cs_param_thread1_arg)


{
    

data++;
    __exit_thread1: ; __cs_exit(0);
}


typedef struct anonstruct_0
{
        

char nome[30];
        

int x;
        

int y;
        

int z;
} luogo;


void *thread2(void *__cs_param_thread2_arg)


{
    

static luogo __cs_nondet_thread2_l;
    

static luogo *__cs_nondet_thread2_p;
    

__cs_nondet_thread2_l.x = 10;
    

__cs_nondet_thread2_p = (luogo) __cs_safe_malloc(sizeof(luogo));
    

(*__cs_nondet_thread2_p).x = 100;
    __exit_thread2: ; __cs_exit(0);
}


void *thread3(void *__cs_param_thread3_arg)


{
    

__cs_mutex_lock(&m);
    

;
    

static _Bool __cs_nondet_thread3___cs_tmp_if_cond_0;
    

__cs_nondet_thread3___cs_tmp_if_cond_0 = data >= 3;
    

if (__cs_nondet_thread3___cs_tmp_if_cond_0)


    {
        

__CSEQ_assert(0);
        

;
    }

    

__cs_mutex_unlock(&m);
    __exit_thread3: ; __cs_exit(0);
}


int main()


{
    

__cs_mutex_init(&m, 0);
    

static __cs_t __cs_nondet_main_t1;
    

static __cs_t __cs_nondet_main_t2;
    

static __cs_t __cs_nondet_main_t3;
    

__cs_create(&__cs_nondet_main_t1, 0, thread1, 0);
    

__cs_create(&__cs_nondet_main_t2, 0, thread2, 0);
    

__cs_create(&__cs_nondet_main_t3, 0, thread3, 0);
    

__cs_join(__cs_nondet_main_t1, 0);
    

__cs_join(__cs_nondet_main_t2, 0);
    

__cs_join(__cs_nondet_main_t3, 0);
    

goto __exit_main; 
    __exit_main: ; __cs_exit(0);
}
