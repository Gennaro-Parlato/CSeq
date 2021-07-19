#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

volatile unsigned next_ticket = 0;
volatile unsigned now_serving = 0;
unsigned fetch_and_increment__next_ticket(){
 __VERIFIER_atomic_begin();
 unsigned value;
  if(((next_ticket + 1) % 3) == now_serving){
   value = 3;
  }
  else
  {
   value = next_ticket;
   next_ticket = ((next_ticket + 1) % 3);
  }
 __VERIFIER_atomic_end();
 return value;
}
inline void acquire_lock(){
 unsigned my_ticket;
 my_ticket = fetch_and_increment__next_ticket();
 if(my_ticket == 3){
  assume_abort_if_not(0);
 }else{
  while(1){
   if(now_serving == my_ticket){
    break;
   }
  }
 }
 return;
}
inline void release_lock(){
 now_serving++;
}
int c = 0;
void* thr1(void* arg){
 acquire_lock();
 c++;
 { if(!(c == 1)) { ERROR: {reach_error();abort();}(void)0; } };
 c--;
 release_lock();
  return 0;
}
int main(){
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
