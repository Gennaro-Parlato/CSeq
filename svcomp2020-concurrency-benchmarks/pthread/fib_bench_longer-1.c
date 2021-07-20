#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int i=1, j=1;
void *
t1(void* arg)
{
  int k = 0;
  for (k = 0; k < 6; k++) {
    __VERIFIER_atomic_begin();
    i+=j;
    __VERIFIER_atomic_end();
  }
  pthread_exit(((void *)0));
}
void *
t2(void* arg)
{
  int k = 0;
  for (k = 0; k < 6; k++) {
    __VERIFIER_atomic_begin();
    j+=i;
    __VERIFIER_atomic_end();
  }
  pthread_exit(((void *)0));
}
int
main(int argc, char **argv)
{
  pthread_t id1, id2;
  pthread_create(&id1, ((void *)0), t1, ((void *)0));
  pthread_create(&id2, ((void *)0), t2, ((void *)0));
  __VERIFIER_atomic_begin();
  int condI = i > 377;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  int condJ = j > 377;
  __VERIFIER_atomic_end();
  if (condI || condJ) {
    ERROR: {reach_error();abort();}
  }
  return 0;
}
