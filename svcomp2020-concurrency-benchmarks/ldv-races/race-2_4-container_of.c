#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
int __VERIFIER_nondet_int(void);
void ldv_assert(int expression) { if (!expression) { ERROR: {reach_error();abort();}}; return; }
pthread_t t1,t2;
struct device {
};
struct A {
 int a;
 int b;
};
struct my_data {
 pthread_mutex_t lock;
 struct device dev;
 struct A shared;
};
void *my_callback(void *arg) {
 struct device *dev = (struct device*)arg;
 struct my_data *data;
 data = ({ const typeof( ((struct my_data *)0)->dev ) *__mptr = (dev); (struct my_data *)( (char *)__mptr - ((unsigned long) &((struct my_data *)0)->dev) );});
 pthread_mutex_lock (&data->lock);
 data->shared.a = 1;
 data->shared.b = data->shared.b + 1;
 pthread_mutex_unlock (&data->lock);
 return 0;
}
int my_drv_probe(struct my_data *data) {
 struct device *d = &data->dev;
 pthread_mutex_init(&data->lock, ((void *)0));
 data->shared.a = 0;
 data->shared.b = 0;
 int res = __VERIFIER_nondet_int();
 if(res)
  goto exit;
 pthread_create(&t1, ((void *)0), my_callback, (void *)d);
 pthread_create(&t2, ((void *)0), my_callback, (void *)d);
 return 0;
exit:
 pthread_mutex_destroy(&data->lock);
 return -1;
}
void my_drv_disconnect(struct my_data *data) {
 void *status;
 data->shared.a = 3;
 data->shared.b = 3;
 ldv_assert(data->shared.a==3);
 ldv_assert(data->shared.b==3);
 pthread_join(t1, &status);
 pthread_join(t2, &status);
 pthread_mutex_destroy(&data->lock);
}
int my_drv_init(void) {
 return 0;
}
void my_drv_cleanup(void) {
 return;
}
int main(void) {
 int ret = my_drv_init();
 if(ret==0) {
  int probe_ret;
  struct my_data data;
  probe_ret = my_drv_probe(&data);
  if(probe_ret==0) {
   my_drv_disconnect(&data);
   ldv_assert(data.shared.a==1);
   ldv_assert(data.shared.b==2);
  }
  my_drv_cleanup();
  data.shared.a = -1;
  data.shared.b = -1;
  ldv_assert(data.shared.a==-1);
  ldv_assert(data.shared.b==-1);
 }
 return 0;
}
