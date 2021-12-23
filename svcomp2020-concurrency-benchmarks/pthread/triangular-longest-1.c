#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
int i = 3, j = 6;
void *t1(void *arg) {
  for (int k = 0; k < 20; k++) {
    __VERIFIER_atomic_begin();
    i = j + 1;
    __VERIFIER_atomic_end();
  }
  pthread_exit(((void *)0));
}
void *t2(void *arg) {
  for (int k = 0; k < 20; k++) {
    __VERIFIER_atomic_begin();
    j = i + 1;
    __VERIFIER_atomic_end();
  }
  pthread_exit(((void *)0));
}
int main(int argc, char **argv) {
  pthread_t id1, id2;
  pthread_create(&id1, ((void *)0), t1, ((void *)0));
  pthread_create(&id2, ((void *)0), t2, ((void *)0));
  __VERIFIER_atomic_begin();
  int condI = i > (2*20 +6);
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  int condJ = j > (2*20 +6);
  __VERIFIER_atomic_end();
  if (condI || condJ) {
    ERROR: {reach_error();abort();}
  }
  return 0;
}
