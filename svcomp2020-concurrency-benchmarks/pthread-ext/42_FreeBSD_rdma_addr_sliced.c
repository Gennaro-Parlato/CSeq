#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile _Bool MTX = !1;
__thread _Bool COND = 0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(MTX==0);
 MTX = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(MTX==1);
 MTX = 0;
}
volatile unsigned int refctr = 0;
inline static void put_client(int client){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 --refctr;
 if (refctr == 0) {
  COND = 1; }
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void rdma_addr_unregister_client(int client){
 put_client(client);
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 if (refctr) {
  { COND = 0; __VERIFIER_atomic_release(); assume_abort_if_not(COND); __VERIFIER_atomic_acquire(); }; }
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline static void queue_req( ){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline static void process_req( ){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void rdma_resolve_ip( ){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 refctr++;
 __VERIFIER_atomic_release();
 if(__VERIFIER_nondet_int()){
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  refctr--;
  __VERIFIER_atomic_release(); }
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void rdma_addr_cancel( ){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
void* thr1(void* arg){
  while(1)
    switch(__VERIFIER_nondet_int()){
    case 0: rdma_addr_unregister_client(__VERIFIER_nondet_int()); break;
    case 1: queue_req(); break;
    case 2: process_req(); break;
    case 3: rdma_resolve_ip(); break;
    case 4: rdma_addr_cancel(); break;
  }
  return 0;
}
int main(){
  pthread_t t;
  while(1) pthread_create(&t, 0, thr1, 0);
}
