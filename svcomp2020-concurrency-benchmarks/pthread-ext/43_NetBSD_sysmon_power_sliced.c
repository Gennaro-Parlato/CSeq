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
inline int sysmon_queue_power_event(){
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
 if (__VERIFIER_nondet_int())
  return 0;
 return 1; }
inline int sysmon_get_power_event(){
 { if(!((MTX==1))) { goto ERROR; } };
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
 if (__VERIFIER_nondet_int())
  return 0;
 return 1; }
inline int sysmon_power_daemon_task(){
 if (__VERIFIER_nondet_int()) return __VERIFIER_nondet_int();
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 switch (__VERIFIER_nondet_int()) {
 case 1:
  { if(!((MTX==1))) { goto ERROR; } };
  if (__VERIFIER_nondet_int()) {
   __VERIFIER_atomic_release();
   goto out;}
  break;
 case 2:
  { if(!((MTX==1))) { goto ERROR; } };
  if (__VERIFIER_nondet_int()) {
   __VERIFIER_atomic_release();
   goto out;}
  break;
 default:
  __VERIFIER_atomic_release();
  goto out;}
 sysmon_queue_power_event();
 if (__VERIFIER_nondet_int()) {
  __VERIFIER_atomic_release();
  goto out;}
 else {
  COND = 1;
  __VERIFIER_atomic_release();}
 out:
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
 return __VERIFIER_nondet_int(); }
inline void sysmonopen_power(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 if (__VERIFIER_nondet_int())
  { if(!((MTX==1))) { goto ERROR; } };
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void sysmonclose_power(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 { if(!((MTX==1))) { goto ERROR; } };
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void sysmonread_power(){
 if (__VERIFIER_nondet_int()){
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  for (;;) {
   if (sysmon_get_power_event()) {
    break;}
   if (__VERIFIER_nondet_int()) {
    break;}
   { COND = 0; __VERIFIER_atomic_release(); assume_abort_if_not(COND); __VERIFIER_atomic_acquire(); };
      { if(!(COND)) { goto ERROR; } }; }
  __VERIFIER_atomic_release(); }
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void sysmonpoll_power(){
 if(__VERIFIER_nondet_int()){
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  __VERIFIER_atomic_release(); }
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void filt_sysmon_power_rdetach(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void filt_sysmon_power_read(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void sysmonkqfilter_power(){
 __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
 __VERIFIER_atomic_release();
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
inline void sysmonioctl_power(){
 switch (__VERIFIER_nondet_int()) {
 case 3:
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  if (__VERIFIER_nondet_int()) {
   __VERIFIER_atomic_release();
   break;}
  __VERIFIER_atomic_release();
  __VERIFIER_atomic_acquire();{ if(!(MTX==1)) { goto ERROR; } };;
  __VERIFIER_atomic_release();
  break; }
  { if(!(1)) { ERROR: {reach_error();abort();}(void)0; } };
}
void* thr1(void* arg){
  while(1)
    switch(__VERIFIER_nondet_int()){
    case 0: sysmon_power_daemon_task(); break;
    case 1: sysmonopen_power(); break;
    case 2: sysmonclose_power(); break;
    case 3: sysmonread_power(); break;
    case 4: sysmonpoll_power(); break;
    case 5: filt_sysmon_power_rdetach(); break;
    case 6: filt_sysmon_power_read(); break;
    case 7: sysmonkqfilter_power(); break;
    case 8: sysmonioctl_power(); break; }}
int main(){
  pthread_t t;
  while(1) pthread_create(&t, 0, thr1, 0);
}
