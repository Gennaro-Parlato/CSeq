extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>

pthread_mutex_t  m;

struct luogo { char nome[3]; 
		 int x,y,z; };

struct luogo g = {{0,0,0}, 1, 2, 3};

pthread_mutex_t mut = { { 0, 0, 0, 0, 0, { { 0, 0 } } } };

struct luogo **conns;

int data;

void *thread2(void *arg)
{
  struct luogo l, *p;
  char * msg;

  l.x = 10;
  p = &l;
  //p = (struct luogo *) malloc(2 * sizeof(struct luogo));
  //msg = realloc("",  2 * sizeof(struct luogo));
  //msg = realloc(c->msglist, c->msgsize * 2 * sizeof(struct msghdr));
  p = (struct luogo *) malloc(p->x * 2 * sizeof(struct luogo));
  //p->x = 100;  
  //g.x = l.y;
  if ((conns = calloc(l.x, sizeof(struct luogo *))) == NULL)
          msg = "Exit";
  
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

  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);

  pthread_join(t2, 0);
  pthread_join(t3, 0);

  return 0;
}
