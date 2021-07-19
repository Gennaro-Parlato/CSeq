#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void __VERIFIER_atomic_acquire(int * m)
{
 assume_abort_if_not(*m==0);
 *m = 1;
}
void __VERIFIER_atomic_release(int * m)
{
 assume_abort_if_not(*m==1);
 *m = 0;
}
void __VERIFIER_atomic_CAS(
  int *v,
  int e,
  int u,
  int *r)
{
 if(*v == e)
 {
  *v = u, *r = 1;
 }
 else
 {
  *r = 0;
 }
}
int memory[(2*320+1)];
int next_alloc_idx = 1;
int m = 0;
int top;
inline int index_malloc(){
 int curr_alloc_idx = -1;
 __VERIFIER_atomic_acquire(&m);
 if(next_alloc_idx+2-1 > (2*320+1)){
  __VERIFIER_atomic_release(&m);
  curr_alloc_idx = 0;
 }else{
  curr_alloc_idx = next_alloc_idx;
  next_alloc_idx += 2;
  __VERIFIER_atomic_release(&m);
 }
 return curr_alloc_idx;
}
inline void EBStack_init(){
 top = 0;
}
inline int isEmpty() {
 if(top == 0)
  return 1;
 else
  return 0;
}
inline int push(int d) {
 int oldTop = -1, newTop = -1, casret = -1;
 newTop = index_malloc();
 if(newTop == 0){
  return 0;
 }else{
  memory[newTop+0] = d;
  while (1) {
   oldTop = top;
   memory[newTop+1] = oldTop;
   __VERIFIER_atomic_CAS(&top,oldTop,newTop,&casret);
   if(casret==1){
    return 1;
   }
  }
 }
}
void __VERIFIER_atomic_assert(int r)
{
  { if(!(!(!r || !isEmpty()))) { ERROR: {reach_error();abort();} (void)0; } };
}
inline void push_loop(){
 int r = -1;
 int arg = __VERIFIER_nondet_int();
 while(1){
  r = push(arg);
    __VERIFIER_atomic_assert(r);
 }
}
int m2 = 0;
int state = 0;
void* thr1(void* arg)
{
 __VERIFIER_atomic_acquire(&m2);
 switch(state)
 {
 case 0:
  EBStack_init();
  state = 1;
 case 1:
  __VERIFIER_atomic_release(&m2);
  push_loop();
  break;
 }
  return 0;
}
int main()
{
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
