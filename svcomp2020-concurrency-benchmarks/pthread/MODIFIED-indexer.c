/* Changes w.r.t. indexer.c: 
   replaced 128 --> NMUTEXES
            13  --> NTHREADS
   
*/ 

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#define NMUTEXES 3
#define NTHREADS 3

int table[NMUTEXES];
pthread_mutex_t cas_mutex[NMUTEXES];
pthread_t tids[NTHREADS];
int cas(int * tab, int h, int val, int new_val)
{
  int ret_val = 0;
  pthread_mutex_lock(&cas_mutex[h]);
  if ( tab[h] == val ) {
    tab[h] = new_val;
    ret_val = 1;
  }
  pthread_mutex_unlock(&cas_mutex[h]);
  return ret_val;
}
void * thread_routine(void * arg)
{
  int tid;
  int m = 0, w, h;
  tid = *((int *)arg);
  while(1){
    if ( m < 4 ){
      w = (++m) * 11 + tid;
    }
    else{
      pthread_exit(((void *)0));
    }
    h = (w * 7) % NMUTEXES;
    if (h<0)
    {
      ERROR: {reach_error();abort();}
      ;
    }
    while ( cas(table, h, 0, w) == 0){
      h = (h+1) % NMUTEXES;
    }
  }
}
int main()
{
  int i, arg;
  for (i = 0; i < NMUTEXES; i++)
    pthread_mutex_init(&cas_mutex[i], ((void *)0));
  for (i = 0; i < NTHREADS; i++){
    arg=i;
    pthread_create(&tids[i], ((void *)0), thread_routine, &arg);
  }
  for (i = 0; i < NTHREADS; i++){
    pthread_join(tids[i], ((void *)0));
  }
  for (i = 0; i < NMUTEXES; i++){
    pthread_mutex_destroy(&cas_mutex[i]);
  }
}
