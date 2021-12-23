extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

pthread_mutex_t  m;
//int data = (2,0); //inizializer element must be constant for storage class global and static
int data = 0;
const int pi = 3;

int foo(const int y){
	const int w = y;
	return w;
}

void *thread1(void *arg)
{
  data++;
}


void *thread2(void *arg)
{
  int *x, j;
  const int i=data;
  j = pi;
  j = i;
  foo(i);
//  *x =  1;
//  data = foo(3)+7;
//  a[1][1]= 7+x;
//  *(a+3) = x; 
//  sizeof (int);
//  data, x++, a[0][2];
//  *x = (int) 3.14;
  data += i;
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
