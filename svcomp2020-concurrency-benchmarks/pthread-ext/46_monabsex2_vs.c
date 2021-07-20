#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

_Bool s = 0;
__thread _Bool l = 0;
void* thr1(void* arg)
{
 { if(!(!l || s)) { ERROR: {reach_error();abort();}(void)0; } };
  s = s || 1;
 l = 1;
  return 0;
}
int main()
{
  pthread_t t;
  while(1) pthread_create(&t, 0, thr1, 0);
}
