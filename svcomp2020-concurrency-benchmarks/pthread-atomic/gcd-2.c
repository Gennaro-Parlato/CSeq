#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

unsigned a, b;
void __VERIFIER_atomic_dec_a()
{
  if(a>b)
    a=a-b;
}
void __VERIFIER_atomic_dec_b()
{
  if(b>a)
    b=b-a;
}
void* dec_a(void* arg)
{
  (void)arg;
  while(a!=b)
  {
    __VERIFIER_atomic_dec_a();
  }
  return 0;
}
void* dec_b(void* arg)
{
  (void)arg;
  while(a!=b)
  {
    __VERIFIER_atomic_dec_b();
  }
  return 0;
}
unsigned start(unsigned a_in, unsigned b_in)
{
  a=a_in;
  b=b_in;
  pthread_t t1, t2;
  pthread_create(&t1, 0, dec_a, 0);
  pthread_create(&t2, 0, dec_b, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return a;
}
void check_gcd(unsigned a_in, unsigned b_in, unsigned gcd)
{
  unsigned guessed_gcd=__VERIFIER_nondet_uint();
  assume_abort_if_not(guessed_gcd>1);
  assume_abort_if_not(a_in%guessed_gcd==0);
  assume_abort_if_not(b_in%guessed_gcd==0);
  __VERIFIER_assert(a_in%gcd==0);
  __VERIFIER_assert(b_in%gcd==0);
  __VERIFIER_assert(gcd>=guessed_gcd);
}
int main()
{
  unsigned a_in=__VERIFIER_nondet_uint();
  unsigned b_in=__VERIFIER_nondet_uint();
  assume_abort_if_not(a_in>0);
  assume_abort_if_not(b_in>0);
  check_gcd(a_in, b_in, start(a_in, b_in));
  return 0;
}
