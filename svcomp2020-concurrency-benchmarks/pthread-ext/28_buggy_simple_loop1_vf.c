#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void* thr1(void* arg){
  unsigned int x=__VERIFIER_nondet_uint(), y=__VERIFIER_nondet_uint(), z=__VERIFIER_nondet_uint();
  int i, j=1, k=1;
  for(i=0; i<x; i++) {
    for(j=i+1; j<y; j++) {
      for(k = j; k < z; k++) {
 { if(!(k > i)) { goto ERROR; } };
      }
    }
  }
  { if(!(i == x && ( j == y || y <= x+1) && (x == 0 || y <= x+1 || k == z || z < y))) { ERROR: {reach_error();abort();}(void)0; } } ;
  return 0;
}
int main()
{
  pthread_t t;
  while(1)
  {
   pthread_create(&t, 0, thr1, 0);
  }
}
