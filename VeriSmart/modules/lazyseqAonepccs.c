#define THREADS <insert-maxthreads-here>
#define ROUNDS <insert-maxrounds-here>
#define STOP_VOID(A) return;
#define STOP_NONVOID(A) return 0;
#define IF(T,A,B,W) if (__CPROVER_myor(__CPROVER_ugt_bits(__cs_pc[T], A, W), __CPROVER_uge_bits(A, __cs_pc_cs, W))) goto B;
