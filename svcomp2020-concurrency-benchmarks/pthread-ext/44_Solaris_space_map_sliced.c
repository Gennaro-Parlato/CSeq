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
_Bool LOADED = 0;
_Bool LOADING = 0;
inline void space_map_contains(){
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void space_map_walk(){
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void space_map_load_wait(){
 { if(!((MTX==1))) { goto ERROR; } };
 while (LOADING) {
  { if(!(!LOADED)) { goto ERROR; } };
  { COND = 0; __VERIFIER_atomic_release(); assume_abort_if_not(COND); __VERIFIER_atomic_acquire(); };
  { if(!(COND)) { goto ERROR; } }; }
       __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void space_map_load(){
 { if(!((MTX==1))) { goto ERROR; } };
 { if(!(!LOADED)) { goto ERROR; } };
 { if(!(!LOADING)) { goto ERROR; } };
 LOADING = 1;
 __VERIFIER_atomic_release();
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 for (;__VERIFIER_nondet_int();) {
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  if (__VERIFIER_nondet_int())
   break; }
 if (__VERIFIER_nondet_int())
  LOADED = 1;
 LOADING = 0;
 COND = 1;
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void space_map_unload(){
 { if(!((MTX==1))) { goto ERROR; } };
 LOADED = 0;
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline int space_map_alloc(){
 if (__VERIFIER_nondet_int())
  { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
 return __VERIFIER_nondet_int();
}
inline void space_map_sync(){
 { if(!((MTX==1))) { goto ERROR; } };
 if (__VERIFIER_nondet_int())
  return;
 while (__VERIFIER_nondet_int()) {
  while (__VERIFIER_nondet_int()) {
   if (__VERIFIER_nondet_int()) {
    __VERIFIER_atomic_release();
    __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };; }}}
 if (__VERIFIER_nondet_int()) {
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };; }
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void space_map_ref_generate_map(){
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
void* thr1(void* arg){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 switch(__VERIFIER_nondet_int()){
  case 1: space_map_contains(); break;
  case 2: space_map_walk(); break;
  case 3: if(LOADING)
    space_map_load_wait();
   else if(!LOADED)
    space_map_load();
   else
    space_map_unload(); break;
   break;
  case 6: space_map_alloc(); break;
  case 7: space_map_sync(); break;
  case 8: space_map_ref_generate_map(); break; }
 { if(!((MTX==1))) { goto ERROR; } };
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
  return 0;
}
int main(){
  pthread_t t;
 while(1) pthread_create(&t, 0, thr1, 0);
}
