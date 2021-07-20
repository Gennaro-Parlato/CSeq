extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

pthread_mutex_t  m;
int data = 0;

int foo(int x, int y) {
    return x+5;
}

void *thread1(void *arg)
{
  data++;
}


void *thread2(void *arg)
{
  int *x, a[3][4];
  int i=1;
  i = 2;
  a[1][1]= 7;
  x =  malloc(sizeof(int));
//  i = data;
//  *x =  1;
  data = foo(i,*x)+7;
//  *(a+3) = x; 
//  sizeof (int);
//  data, x++, a[0][2];
//  *x = (int) 3.14;
//  data = a[i][0] * data;
}


void *thread3(void *arg)
{
  pthread_mutex_lock(&m);
  if (data >= 3){
    ERROR: __VERIFIER_error();
    ;
  }
  pthread_mutex_unlock(&m);
}


int main()
{
  pthread_mutex_init(&m, 0);

  pthread_t t1, t2, t3;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);

  return 0;
}
