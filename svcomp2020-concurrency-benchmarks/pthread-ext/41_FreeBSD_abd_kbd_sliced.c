#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile _Bool MTX = !1;
__thread _Bool COND = 0;
_Bool buf = 0;
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
inline static int adb_kbd_receive_packet(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { ERROR: {reach_error();abort();}(void)0; } };;
 __VERIFIER_atomic_release();
 COND = 1;
 return 0; }
inline static void akbd_repeat() {
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { ERROR: {reach_error();abort();}(void)0; } };;
 __VERIFIER_atomic_release(); }
inline static void akbd_read_char(int wait) {
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { ERROR: {reach_error();abort();}(void)0; } };;
 if (!buf && wait){
  { COND = 0; __VERIFIER_atomic_release(); assume_abort_if_not(COND); __VERIFIER_atomic_acquire(); };
  { if(!(COND)) { goto ERROR; } };}
 if (!buf) {
  __VERIFIER_atomic_release();
  return; }
 __VERIFIER_atomic_release(); }
inline static void akbd_clear_state(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { ERROR: {reach_error();abort();}(void)0; } };;
 buf = 0;
 __VERIFIER_atomic_release(); }
void* thr1(void* arg){
  while(1)
  {
    switch(__VERIFIER_nondet_int())
    {
    case 0: adb_kbd_receive_packet(); break;
    case 1: akbd_repeat(); break;
    case 2: akbd_read_char(__VERIFIER_nondet_int()); break;
    case 3: akbd_clear_state(); break;
    case 4: while(1){
        __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { ERROR: {reach_error();abort();}(void)0; } };;
        buf = !buf;
        __VERIFIER_atomic_release();
      }
    }
  }
  return 0;
}
int main(){
  pthread_t t;
  while(1) pthread_create(&t, 0, thr1, 0);
}
