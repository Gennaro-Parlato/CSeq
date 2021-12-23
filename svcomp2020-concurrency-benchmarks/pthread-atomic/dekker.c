#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int flag1 = 0, flag2 = 0;
int turn;
int x;
void *thr1(void *_) {
  flag1 = 1;
  while (flag2 >= 1) {
    if (turn != 0) {
      flag1 = 0;
      while (turn != 0) {};
      flag1 = 1;
    }
  }
  x = 0;
  if (!(x<=0)) ERROR: {reach_error();abort();}
  turn = 1;
  flag1 = 0;
  return 0;
}
void *thr2(void *_) {
  flag2 = 1;
  while (flag1 >= 1) {
    if (turn != 1) {
      flag2 = 0;
      while (turn != 1) {};
      flag2 = 1;
    }
  }
  x = 1;
  if (!(x>=1)) ERROR: {reach_error();abort();}
  turn = 1;
  flag2 = 0;
  return 0;
}
int main() {
  pthread_t t1, t2;
  assume_abort_if_not(0<=turn && turn<=1);
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
