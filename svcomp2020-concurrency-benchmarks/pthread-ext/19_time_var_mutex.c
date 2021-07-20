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
int block;
int busy;
int inode;
int m_inode=0;
int m_busy=0;
void * thr1(void* arg)
{
  __VERIFIER_atomic_acquire(&m_inode);
  if(inode == 0){
    __VERIFIER_atomic_acquire(&m_busy);
    busy = 1;
    __VERIFIER_atomic_release(&m_busy);
    inode = 1;
  }
  block = 1;
  { if(!(block == 1)) { ERROR: {reach_error();abort();}(void)0; } };
  __VERIFIER_atomic_release(&m_inode);
  return 0;
}
void * thr2(void* arg)
{
  __VERIFIER_atomic_acquire(&m_busy);
  if(busy == 0){
    block = 0;
    { if(!(block == 0)) { ERROR: {reach_error();abort();}(void)0; } };
  }
  __VERIFIER_atomic_release(&m_busy);
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  thr2(0);
  return 0;
}
