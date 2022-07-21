
#include <stdio.h>
#include <errno.h>
#include "/home/aldo/Desktop/program_analysis/project/verismart-distributed-integrated/CSeq/VeriSmart/modules/pthread_defs.c"
#define PRINT_DT(E,ID, EXP) printf("%s_%d, %d\n",EXP,ID,typename(E) )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
void *__cs_safe_malloc(int __cs_size);
enum t_typename {
       TYPENAME_INT,
       TYPENAME_CHAR,
       TYPENAME_LONG_INT,
       TYPENAME_SHORT,
       TYPENAME_LONG_LONG,
       TYPENAME_UNSIGNED_INT,
       TYPENAME_UNSIGNED_CHAR,
       TYPENAME_UNSIGNED_LONG_INT,
       TYPENAME_UNSIGNED_SHORT,
       TYPENAME_UNSIGNED_LONG_LONG,
       TYPENAME_OTHER
};
        
                                                                                                                                                                                                                                                                                                            #define typename(x) _Generic((x),                                                                                                                                                                                                                                                                                   char: TYPENAME_CHAR,                                                                                                                                                                                                                                                                                        unsigned char: TYPENAME_UNSIGNED_CHAR,                                                                                                                                                                                                                                                                      short: TYPENAME_SHORT,                                                                                                                                                                                                                                                                                      unsigned short: TYPENAME_UNSIGNED_SHORT,                                                                                                                                                                                                                                                                    int: TYPENAME_INT,                                                                                                                                                                                                                                                                                          unsigned int: TYPENAME_UNSIGNED_INT,                                                                                                                                                                                                                                                                        long int: TYPENAME_LONG_INT,                                                                                                                                                                                                                                                                                unsigned long int: TYPENAME_UNSIGNED_LONG_INT,                                                                                                                                                                                                                                                              long long : TYPENAME_LONG_LONG,                                                                                                                                                                                                                                                                             unsigned long long:  TYPENAME_UNSIGNED_LONG_LONG,                                                                                                                                                                                                                                                           default:  TYPENAME_OTHER)
        
int main(){
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
int flag1 = 0;
PRINT_DT((flag1),0, "TYPE");
PRINT_DT((0),1, "TYPE");
int flag2 = 0;
PRINT_DT((flag2),2, "TYPE");
int turn;
int x;
void *thr1_0(void *__dr_param_thr1___cs_unused);
void *__dr_param_thr1___cs_unused;
{
PRINT_DT((1),3, "TYPE");
PRINT_DT((turn),4, "TYPE");
PRINT_DT((!((flag2 == 1) && (turn == 1))),5, "TYPE");
PRINT_DT(((flag2 == 1) && (turn == 1)),6, "TYPE");
PRINT_DT((flag2 == 1),7, "TYPE");
PRINT_DT((turn == 1),8, "TYPE");
PRINT_DT((x),9, "TYPE");
static _Bool __dr_nondet_thr1___cs_tmp_if_cond_0;
PRINT_DT((__dr_nondet_thr1___cs_tmp_if_cond_0),10, "TYPE");
PRINT_DT((!(x <= 0)),11, "TYPE");
PRINT_DT((x <= 0),12, "TYPE");
{
}
}
void *thr2_0(void *__dr_param_thr2___cs_unused);
void *__dr_param_thr2___cs_unused;
{
PRINT_DT((!((flag1 == 1) && (turn == 0))),13, "TYPE");
PRINT_DT(((flag1 == 1) && (turn == 0)),14, "TYPE");
PRINT_DT((flag1 == 1),15, "TYPE");
PRINT_DT((turn == 0),16, "TYPE");
static _Bool __dr_nondet_thr2___cs_tmp_if_cond_1;
PRINT_DT((__dr_nondet_thr2___cs_tmp_if_cond_1),17, "TYPE");
PRINT_DT((!(x >= 1)),18, "TYPE");
PRINT_DT((x >= 1),19, "TYPE");
{
}
}
{
static __cs_t __dr_nondet_main_t1;
static __cs_t __dr_nondet_main_t2;
}
return 0;
}