extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

pthread_mutex_t  m;
//int data = (2,0); //inizializer element must be constant for storage class global and static
int data = 0;
const int pi = 3;
int b[3][3]={{0,0,0},{2}};

void *thread1(void *arg)
{
  data++;
}


void *thread2(void *arg)
{
  int *x, a[3][4],j;
  const int* i=data;
  j = pi;
  j = *i;
//  *x =  1;
//  data = foo(3)+7;
//  a[1][1]= 7+x;
//  *(a+3) = x; 
//  sizeof (int);
//  data, x++, a[0][2];
//  *x = (int) 3.14;
  data += *i;
  data = a[pi][0] * data;
}



int main()
{
  pthread_mutex_init(&m, 0);

  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);

  return 0;
}
