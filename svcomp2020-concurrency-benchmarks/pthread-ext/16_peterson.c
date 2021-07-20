#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int turn;
int x;
int flag1 = 0, flag2 = 0;
void* thr1(void* arg) {
  flag1 = 1;
  turn = 1;
  do {} while (flag2==1 && turn==1);
  x = 0;
  { if(!(x<=0)) { ERROR: {reach_error();abort();}(void)0; } };
  flag1 = 0;
  return 0;
}
void* thr2(void* arg) {
  flag2 = 1;
  turn = 0;
  do {} while (flag1==1 && turn==0);
  x = 1;
  { if(!(x>=1)) { ERROR: {reach_error();abort();}(void)0; } };
  flag2 = 0;
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, thr1, 0);
  thr2(0);
  return 0;
}
