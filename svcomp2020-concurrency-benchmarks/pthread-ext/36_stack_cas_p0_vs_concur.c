#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

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
int memory[(2*32+1)];
int next_alloc_idx = 1;
int top = 0;
void __VERIFIER_atomic_index_malloc(int *curr_alloc_idx)
{
 if(next_alloc_idx+2-1 > (2*32+1)) *curr_alloc_idx = 0;
 else *curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;
}
inline void push(int d) {
 int oldTop, newTop,ret;
 __VERIFIER_atomic_index_malloc(&newTop);
 if(newTop == 0)
  assume_abort_if_not(0);;
 memory[newTop+0] = d;
 while (1) {
  oldTop = top;
  memory[newTop+1] = oldTop;
  __VERIFIER_atomic_CAS(&top,oldTop,newTop,&ret);
  if(ret) return;
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
