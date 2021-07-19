#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int i;
pthread_mutex_t lock;
inline int down_interruptible() {
  pthread_mutex_lock(&lock);
  return 0;
}
inline void up() {
  pthread_mutex_unlock(&lock);
  return;
}
inline int copy_to_user(int to, int from, int n) {
  to = from;
  return __VERIFIER_nondet_int();
}
inline int copy_from_user(int to, int from, int n) {
  to = from;
  return __VERIFIER_nondet_int();
}
inline int __get_user(int size, int ptr)
{
  return __VERIFIER_nondet_int();
}
inline int __put_user(int size, int ptr)
{
    return __VERIFIER_nondet_int();
}
int scull_quantum = 4000;
int scull_qset = 1000;
int dev_data;
int dev_quantum;
int dev_qset;
int dev_size;
int __X__;
int scull_trim(int dev)
{
  int qset = dev_qset;
  dev_size = 0;
  dev_quantum = scull_quantum;
  dev_qset = scull_qset;
  dev_data = 0;
  return 0;
}
inline int scull_open(int tid, int i, int filp)
{
  int dev;
  dev = i;
  filp = dev;
  if (down_interruptible())
    return -512;
  __X__ = 2;
  scull_trim(dev);
  if (!(__X__ >= 2)) ERROR: {reach_error();abort();}
  up();
  return 0;
}
inline int scull_follow(int dev, int n) {
  return __VERIFIER_nondet_int();
}
inline int scull_read(int tid, int filp, int buf, int count,
     int f_pos)
{
  int dev = filp;
  int dptr;
  int quantum = dev_quantum, qset = dev_qset;
  int itemsize = quantum * qset;
  int item, s_pos, q_pos, rest;
  int retval = 0;
  if (down_interruptible())
    return -512;
  __X__ = 0;
  if (f_pos >= dev_size)
    goto out;
  if (f_pos+count >= dev_size)
    count = dev_size - f_pos;
  item = f_pos / itemsize;
  rest = f_pos;
   s_pos = rest / quantum; q_pos = rest;
   dptr = scull_follow(dev, item);
   if (count > quantum - q_pos)
     count = quantum - q_pos;
  if (copy_to_user(buf, dev_data + s_pos + q_pos, count)) {
    retval = -2;
    goto out;
  }
  f_pos += count;
  retval = count;
  if (!(__X__ <= 0)) ERROR: {reach_error();abort();}
 out:
  up();
  return retval;
}
inline int scull_write(int tid, int filp, int buf, int count,
      int f_pos)
{
  int dev = filp;
  int dptr;
  int quantum = dev_quantum, qset = dev_qset;
  int itemsize = quantum * qset;
  int item, s_pos, q_pos, rest;
  int retval = -4;
  if (down_interruptible())
    return -512;
  item = f_pos / itemsize;
  rest = f_pos;
  s_pos = rest / quantum; q_pos = rest;
  dptr = scull_follow(dev, item);
  if (dptr == 0)
    goto out;
  if (count > quantum - q_pos)
    count = quantum - q_pos;
  __X__ = 1;
  if (copy_from_user(dev_data+s_pos+q_pos, buf, count)) {
    retval = -2;
    goto out;
  }
  f_pos += count;
  retval = count;
  if (dev_size < f_pos)
    dev_size = f_pos;
  if (!(__X__ == 1)) ERROR: {reach_error();abort();}
 out:
  up();
  return retval;
}
inline int scull_ioctl(int i, int filp,
                 int cmd, int arg)
{
 int err = 0, tmp;
 int retval = 0;
 switch(cmd) {
   case 0:
  scull_quantum = 4000;
  scull_qset = 1000;
  break;
   case 1:
  retval = __get_user(scull_quantum, arg);
  break;
   case 3:
  scull_quantum = arg;
  break;
   case 5:
  retval = __put_user(scull_quantum, arg);
  break;
   case 7:
  return scull_quantum;
   case 9:
  tmp = scull_quantum;
  retval = __get_user(scull_quantum, arg);
  if (retval == 0)
   retval = __put_user(tmp, arg);
  break;
   case 11:
  tmp = scull_quantum;
  scull_quantum = arg;
  return tmp;
   case 2:
  retval = __get_user(scull_qset, arg);
  break;
   case 4:
  scull_qset = arg;
  break;
   case 6:
  retval = __put_user(scull_qset, arg);
  break;
   case 8:
  return scull_qset;
   case 10:
  tmp = scull_qset;
  retval = __get_user(scull_qset, arg);
  if (retval == 0)
   retval = __put_user(tmp, arg);
  break;
   case 12:
  tmp = scull_qset;
  scull_qset = arg;
  return tmp;
   default:
  return -25;
 }
 return retval;
}
inline int scull_llseek(int filp, int off, int whence, int f_pos)
{
  int dev = filp;
  int newpos;
  switch(whence) {
  case 0:
    newpos = off;
    break;
  case 1:
    newpos = filp + f_pos + off;
    break;
  case 2:
    newpos = dev_size + off;
    break;
  default:
    return -28;
  }
  if (newpos < 0) return -28;
  filp = newpos;
  return newpos;
}
inline void scull_cleanup_module(void)
{
  int dev=__VERIFIER_nondet_int();
  scull_trim(dev);
}
inline int scull_init_module()
{
  int result = 0;
  return 0;
 fail:
  scull_cleanup_module();
  return result;
}
void *loader(void *arg) {
  scull_init_module();
  scull_cleanup_module();
  return 0;
}
void *thread1(void *arg) {
  int filp=__VERIFIER_nondet_int();
  int buf=__VERIFIER_nondet_int();
  int count = 10;
  int off = 0;
  scull_open(1, i, filp);
  scull_read(1, filp, buf, count, off);
  0;
  return 0;
}
void *thread2(void *arg) {
  int filp=__VERIFIER_nondet_int();
  int buf=__VERIFIER_nondet_int();
  int count = 10;
  int off = 0;
  scull_open(2, i, filp);
  scull_write(2, filp, buf, count, off);
  0;
  return 0;
}
int main() {
  pthread_t t1, t2, t3;
  pthread_mutex_init(&lock, 0);
  pthread_create(&t1, 0, loader, 0);
  pthread_create(&t2, 0, thread1, 0);
  pthread_create(&t3, 0, thread2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_mutex_destroy(&lock);
  return 0;
}
