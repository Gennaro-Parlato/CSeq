#include <pthread.h>
#include <assert.h>

int data = 0;

int __VERIFIER_atomic_foo(int *x, int y) {
    *x=y;
    return x+5;
}

void *thread1(void *arg)
{
  int v;
  v = data;
  __VERIFIER_atomic_foo(&data,3);
}


int main()
{
  pthread_t t1, t2, t3;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread1, 0);
  pthread_create(&t3, 0, thread1, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);

  return 0;
}
