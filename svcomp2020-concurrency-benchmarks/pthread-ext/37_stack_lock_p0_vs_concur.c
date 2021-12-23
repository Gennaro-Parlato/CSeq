#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int memory[(2*32+1)];
int next_alloc_idx = 1;
int m = 0;
int top = 0;
void __VERIFIER_atomic_acquire()
{
 assume_abort_if_not(m==0);
 m = 1;
}
void __VERIFIER_atomic_release()
{
 assume_abort_if_not(m==1);
 m = 0;
}
void __VERIFIER_atomic_index_malloc(int *curr_alloc_idx)
{
 if(next_alloc_idx+2-1 > (2*32+1)) *curr_alloc_idx = 0;
 else *curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;
}
inline void push(int d) {
 int oldTop = -1, newTop = -1;
 __VERIFIER_atomic_index_malloc(&newTop);
 if(newTop == 0)
  assume_abort_if_not(0);
 else{
  memory[newTop+0] = d;
  __VERIFIER_atomic_acquire();
  oldTop = top;
  memory[newTop+1] = oldTop;
  top = newTop;
  __VERIFIER_atomic_release();
 }
}
void* thr1(void* arg){
  while(1){push(10); { if(!(top != 0)) { ERROR: {reach_error();abort();}(void)0; } };}
  return 0;
}
int main()
{
  pthread_t t;
 while(1) { pthread_create(&t, 0, thr1, 0); }
}
