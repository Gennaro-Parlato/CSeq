#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int table[128];
pthread_mutex_t cas_mutex[128];
pthread_t tids[13];
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
    h = (w * 7) % 128;
    if (h<0)
    {
      ERROR: {reach_error();abort();}
      ;
    }
    while ( cas(table, h, 0, w) == 0){
      h = (h+1) % 128;
    }
  }
}
int main()
{
  int i, arg;
  for (i = 0; i < 128; i++)
    pthread_mutex_init(&cas_mutex[i], ((void *)0));
  for (i = 0; i < 13; i++){
    arg=i;
    pthread_create(&tids[i], ((void *)0), thread_routine, &arg);
  }
  for (i = 0; i < 13; i++){
    pthread_join(tids[i], ((void *)0));
  }
  for (i = 0; i < 128; i++){
    pthread_mutex_destroy(&cas_mutex[i]);
  }
}
