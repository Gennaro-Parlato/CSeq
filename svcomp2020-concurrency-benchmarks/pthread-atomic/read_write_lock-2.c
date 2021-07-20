#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int w=0, r=0, x, y;
void __VERIFIER_atomic_take_write_lock() {
  assume_abort_if_not(w==0 && r==0);
  w = 1;
}
void __VERIFIER_atomic_take_read_lock() {
  assume_abort_if_not(w==0);
  r = r+1;
}
void *writer(void *arg) {
  __VERIFIER_atomic_take_write_lock();
  x = 3;
  w = 0;
  return 0;
}
void *reader(void *arg) {
  int l;
  __VERIFIER_atomic_take_read_lock();
  l = x;
  y = l;
  if (!(y == x)) ERROR: {reach_error();abort();}
  l = r-1;
  r = l;
  return 0;
}
int main() {
  pthread_t t1, t2, t3, t4;
  pthread_create(&t1, 0, writer, 0);
  pthread_create(&t2, 0, reader, 0);
  pthread_create(&t3, 0, writer, 0);
  pthread_create(&t4, 0, reader, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_join(t4, 0);
  return 0;
}
