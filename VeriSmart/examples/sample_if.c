extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

char* v;


void *thread1(void *arg)
{
  v = "c";
}


void *thread2(void *arg)
{
  int i;
  if (v) 
    i=1;
//  i = data;
//  *x =  1;
//  *(a+3) = x; 
//  sizeof (int);
//  data, x++, a[0][2];
//  *x = (int) 3.14;
//  data = a[i][0] * data;
}


int main()
{
  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);

  return 0;
}
