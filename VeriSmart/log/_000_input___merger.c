extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

pthread_mutex_t  m;
int data = 0;

int foo(int x) {
    return x+5;
}

void *thread1(void *arg)
{
  data++;
}

typedef struct { char nome[30]; 
		 int x,y,z; } luogo;


void *thread2(void *arg)
{
  luogo l, *p;
  l.x = 10;
  p = (luogo) malloc(sizeof(luogo));
  p->x = 100;  
  
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
