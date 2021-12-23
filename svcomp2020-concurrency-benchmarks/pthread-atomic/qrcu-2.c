#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int idx=0;
int ctr1=1, ctr2=0;
int readerprogress1=0, readerprogress2=0;
pthread_mutex_t mutex;
void __VERIFIER_atomic_use1(int myidx) {
  assume_abort_if_not(myidx <= 0 && ctr1>0);
  ctr1++;
}
void __VERIFIER_atomic_use2(int myidx) {
  assume_abort_if_not(myidx >= 1 && ctr2>0);
  ctr2++;
}
void __VERIFIER_atomic_use_done(int myidx) {
  if (myidx <= 0) { ctr1--; }
  else { ctr2--; }
}
void __VERIFIER_atomic_take_snapshot(int readerstart1, int readerstart2) {
  readerstart1 = readerprogress1;
  readerstart2 = readerprogress2;
}
void __VERIFIER_atomic_check_progress1(int readerstart1) {
  if (__VERIFIER_nondet_int()) {
    assume_abort_if_not(readerstart1 == 1 && readerprogress1 == 1);
    if (!(0)) ERROR: {reach_error();abort();}
  }
  return;
}
void __VERIFIER_atomic_check_progress2(int readerstart2) {
  if (__VERIFIER_nondet_int()) {
    assume_abort_if_not(readerstart2 == 1 && readerprogress2 == 1);
    if (!(0)) ERROR: {reach_error();abort();}
  }
  return;
}
void *qrcu_reader1(void* arg) {
  int myidx;
  while (1) {
    myidx = idx;
    if (__VERIFIER_nondet_int()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__VERIFIER_nondet_int()) {
 __VERIFIER_atomic_use2(myidx);
 break;
      } else {}
    }
  }
  readerprogress1 = 1;
  readerprogress1 = 2;
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}
void *qrcu_reader2(void* arg) {
  int myidx;
  while (1) {
    myidx = idx;
    if (__VERIFIER_nondet_int()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__VERIFIER_nondet_int()) {
 __VERIFIER_atomic_use2(myidx);
 break;
      } else {}
    }
  }
  readerprogress2 = 1;
  readerprogress2 = 2;
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}
void* qrcu_updater(void* arg) {
  int i;
  int readerstart1=__VERIFIER_nondet_int(), readerstart2=__VERIFIER_nondet_int();
  int sum;
  __VERIFIER_atomic_take_snapshot(readerstart1, readerstart2);
  if (__VERIFIER_nondet_int()) { sum = ctr1; sum = sum + ctr2; } else { sum = ctr2; sum = sum + ctr1; };
  if (sum <= 1) { if (__VERIFIER_nondet_int()) { sum = ctr1; sum = sum + ctr2; } else { sum = ctr2; sum = sum + ctr1; }; }
  else {}
  if (sum > 1) {
    pthread_mutex_lock(&mutex);
    if (idx <= 0) { ctr2++; idx = 1; ctr1--; }
    else { ctr1++; idx = 0; ctr2--; }
    if (idx <= 0) { while (ctr1 > 0); }
    else { while (ctr2 > 0); }
    pthread_mutex_unlock(&mutex);
  } else {}
  __VERIFIER_atomic_check_progress1(readerstart1);
  __VERIFIER_atomic_check_progress2(readerstart2);
  return 0;
}
int main() {
  pthread_t t1, t2, t3;
  pthread_mutex_init(&mutex, 0);
  pthread_create(&t1, 0, qrcu_reader1, 0);
  pthread_create(&t2, 0, qrcu_reader2, 0);
  pthread_create(&t3, 0, qrcu_updater, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_mutex_destroy(&mutex);
  return 0;
}
