extern void abort(void); 
void assume_abort_if_not(int cond) { 
  if(!cond) {abort();}
}
extern _Bool __VERIFIER_nondet_bool(void);
extern void abort(void); 
void reach_error(){}
void __VERIFIER_assert(int expression) { if (!expression) { ERROR: {reach_error();abort();} }; return; }
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

#include <assert.h>
#include <pthread.h>
#ifndef TRUE
#define TRUE (_Bool)1
#endif
#ifndef FALSE
#define FALSE (_Bool)0
#endif
#ifndef NULL
#define NULL ((void*)0)
#endif
#ifndef FENCE
#define FENCE(x) ((void)0)
#endif
#ifndef IEEE_FLOAT_EQUAL
#define IEEE_FLOAT_EQUAL(x,y) (x==y)
#endif
#ifndef IEEE_FLOAT_NOTEQUAL
#define IEEE_FLOAT_NOTEQUAL(x,y) (x!=y)
#endif



void * P0(void *arg);


void * P1(void *arg);


void fence();


void isync();


void lwfence();




int __unbuffered_cnt;


int __unbuffered_cnt = 0;


int __unbuffered_p0_EAX;


int __unbuffered_p0_EAX = 0;


int __unbuffered_p1_EAX;


int __unbuffered_p1_EAX = 0;


_Bool main$tmp_guard0;


_Bool main$tmp_guard1;


int x;


int x = 0;


int y;


int y = 0;



void * P0(void *arg)
{
  __VERIFIER_atomic_begin();
  y = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p0_EAX = x;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}



void * P1(void *arg)
{
  __VERIFIER_atomic_begin();
  x = 1;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_p1_EAX = y;
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  __unbuffered_cnt = __unbuffered_cnt + 1;
  __VERIFIER_atomic_end();
  return 0;
}



void fence()
{
  
}



void isync()
{
  
}



void lwfence()
{
  
}



int main()
{
  pthread_t t2629;
  pthread_create(&t2629, NULL, P0, NULL);
  pthread_t t2630;
  pthread_create(&t2630, NULL, P1, NULL);
  __VERIFIER_atomic_begin();
  main$tmp_guard0 = __unbuffered_cnt == 2;
  __VERIFIER_atomic_end();
  assume_abort_if_not(main$tmp_guard0);
  __VERIFIER_atomic_begin();
  __VERIFIER_atomic_end();
  __VERIFIER_atomic_begin();
  /* Program was expected to be safe for X86, model checker should have said NO.
This likely is a bug in the tool chain. */
  main$tmp_guard1 = !(__unbuffered_p0_EAX == 0 && __unbuffered_p1_EAX == 0);
  __VERIFIER_atomic_end();
  /* Program was expected to be safe for X86, model checker should have said NO.
This likely is a bug in the tool chain. */
  __VERIFIER_assert(main$tmp_guard1);
  return 0;
}

