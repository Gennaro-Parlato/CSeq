#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <smack_svcomp.h>
const unsigned int default_alloc_size = 4;
void *external_alloc(unsigned int size)
{
  char *p = malloc(size);
  for(unsigned i = 0; i < size; ++i)
    p[i] = __VERIFIER_nondet_char();
  return p;
}
void __bit_spin_unlock(int arg0, unsigned long *arg1) {
  return;
}
int __VERIFIER_nondet_int(void);
int __get_user(int arg0, const void *arg1) {
  return __VERIFIER_nondet_int();
}
unsigned int __VERIFIER_nondet_uint(void);
u32 __iter_div_u64_rem(u64 arg0, u32 arg1, u64 *arg2) {
  return __VERIFIER_nondet_uint();
}
int __VERIFIER_nondet_int(void);
int __put_user(int arg0, void *arg1) {
  return __VERIFIER_nondet_int();
}
void *external_alloc(unsigned int size);
struct tty_driver *__tty_alloc_driver(unsigned int arg0, struct module *arg1, unsigned long arg2) {
  return (struct tty_driver *)external_alloc(sizeof(struct tty_driver));
}
int __VERIFIER_nondet_int(void);
int access_ok(int arg0, const void *arg1, unsigned long arg2) {
  return __VERIFIER_nondet_int();
}
int __VERIFIER_nondet_int(void);
int atomic_add_unless(atomic_t *arg0, int arg1, int arg2) {
  return __VERIFIER_nondet_int();
}
void barrier() {
  return;
}
bool __VERIFIER_nondet_bool(void);
bool bit_spin_is_locked(int arg0, unsigned long *arg1) {
  return __VERIFIER_nondet_bool();
}
void bit_spin_lock(int arg0, unsigned long *arg1) {
  return;
}
void clear_bit(long arg0, volatile unsigned long *arg1) {
  return;
}
void cpu_relax() {
  return;
}
void *external_alloc(unsigned int size);
void assume_abort_if_not(int);
struct timespec current_kernel_time() {
  struct timespec *tmp = (struct timespec*)external_alloc(sizeof(struct timespec));
  assume_abort_if_not(tmp != 0);
  return *tmp;
}
void d_instantiate(struct dentry *arg0, struct inode *arg1) {
  return;
}
void *external_alloc(unsigned int size);
struct dentry *d_instantiate_unique(struct dentry *arg0, struct inode *arg1) {
  return (struct dentry *)external_alloc(sizeof(struct dentry));
}
void d_rehash(struct dentry *arg0) {
  return;
}
void *external_alloc(unsigned int size);
void *dev_get_drvdata(struct device *arg0) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
void dev_set_drvdata(struct device *arg0, void *arg1) {
  return;
}
int __VERIFIER_nondet_int(void);
int ida_get_new_above(struct ida *arg0, int arg1, int *arg2) {
  return __VERIFIER_nondet_int();
}
void *external_alloc(unsigned int size);
void *idr_find_slowpath(struct idr *arg0, int arg1) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
void *external_alloc(unsigned int size);
struct kobject *kobject_get(struct kobject *arg0) {
  return (struct kobject *)external_alloc(sizeof(struct kobject));
}
void kobject_put(struct kobject *arg0) {
  return;
}
bool __VERIFIER_nondet_bool(void);
bool llist_add_batch(struct llist_node *arg0, struct llist_node *arg1, struct llist_head *arg2) {
  return __VERIFIER_nondet_bool();
}
void local_irq_restore(unsigned long arg0) {
  return;
}
int __VERIFIER_nondet_int(void);
int misc_deregister(struct miscdevice *arg0) {
  return __VERIFIER_nondet_int();
}
int __VERIFIER_nondet_int(void);
int misc_register(struct miscdevice *arg0) {
  return __VERIFIER_nondet_int();
}
bool __VERIFIER_nondet_bool(void);
bool mm_tlb_flush_pending(struct mm_struct *arg0) {
  return __VERIFIER_nondet_bool();
}
long __VERIFIER_nondet_long(void);
ssize_t nvram_get_size() {
  return __VERIFIER_nondet_long();
}
unsigned char __VERIFIER_nondet_uchar(void);
unsigned char nvram_read_byte(int arg0) {
  return __VERIFIER_nondet_uchar();
}
void nvram_sync() {
  return;
}
void nvram_write_byte(unsigned char arg0, int arg1) {
  return;
}
unsigned int __VERIFIER_nondet_uint(void);
dma_addr_t page_to_phys(struct page *arg0) {
  return __VERIFIER_nondet_uint();
}
int __VERIFIER_nondet_int(void);
int printk(const char *arg0, ...) {
  return __VERIFIER_nondet_int();
}
void *external_alloc(unsigned int size);
void *rcu_dereference_check(void *arg0, int arg1) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
void *external_alloc(unsigned int size);
void *rcu_dereference_raw(void *arg0) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
void set_normalized_timespec(struct timespec *arg0, time_t arg1, s64 arg2) {
  return;
}
void smp_mb() {
  return;
}
void smp_rmb() {
  return;
}
void *external_alloc(unsigned int size);
void assume_abort_if_not(int);
struct timespec timespec_trunc(struct timespec arg0, unsigned arg1) {
  struct timespec *tmp = (struct timespec*)external_alloc(sizeof(struct timespec));
  assume_abort_if_not(tmp != 0);
  return *tmp;
}
void tty_lock(struct tty_struct *arg0) {
  return;
}
unsigned int __VERIFIER_nondet_uint(void);
speed_t tty_termios_baud_rate(struct ktermios *arg0) {
  return __VERIFIER_nondet_uint();
}
void tty_unlock(struct tty_struct *arg0) {
  return;
}
void tty_wait_until_sent(struct tty_struct *arg0, long arg1) {
  return;
}
static struct mutex nvram_mutex = { 1, 0 };
static ssize_t nvram_len;
loff_t nvram_llseek(struct file *file, loff_t offset, int origin)
{
 switch (origin) {
 case 0:
  break;
 case 1:
  offset += file->f_pos;
  break;
 case 2:
  offset += nvram_len;
  break;
 default:
  offset = -1;
 }
 if (offset < 0)
  return -22;
 file->f_pos = offset;
 __VERIFIER_assert(file->f_pos == offset);
 return file->f_pos;
}
ssize_t read_nvram(struct file *file, char *buf,
     size_t count, loff_t *ppos)
{
 unsigned int i;
 char *p = buf;
 if (!access_ok(1, buf, count))
  return -14;
 if (*ppos >= nvram_len)
  return 0;
 for (i = *ppos; count > 0 && i < nvram_len; ++i, ++p, --count)
  if (__put_user(nvram_read_byte(i), p))
   return -14;
 *ppos = i;
 __VERIFIER_assert(*ppos == i);
 return p - buf;
}
ssize_t write_nvram(struct file *file, const char *buf,
      size_t count, loff_t *ppos)
{
 unsigned int i;
 const char *p = buf;
 char c = __VERIFIER_nondet_char();
 if (!access_ok(0, buf, count))
  return -14;
 if (*ppos >= nvram_len)
  return 0;
 for (i = *ppos; count > 0 && i < nvram_len; ++i, ++p, --count) {
  if (__get_user(c, p))
   return -14;
  nvram_write_byte(c, i);
 }
 *ppos = i;
 __VERIFIER_assert(*ppos == i);
 return p - buf;
}
static int nvram_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
 switch(cmd) {
 case (((0U) << (((0 +8)+8)+14)) | ((('p')) << (0 +8)) | (((0x43)) << 0) | ((0) << ((0 +8)+8))):
  nvram_sync();
  break;
 default:
  return -22;
 }
 return 0;
}
long nvram_unlocked_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
 int ret;
 mutex_lock(&nvram_mutex);
 ret = nvram_ioctl(file, cmd, arg);
 mutex_unlock(&nvram_mutex);
 return ret;
}
struct file_operations nvram_fops = {
 .owner = ((struct module *)0),
 .llseek = nvram_llseek,
 .read = read_nvram,
 .write = write_nvram,
 .unlocked_ioctl = nvram_unlocked_ioctl,
};
static struct miscdevice nvram_dev = {
 144,
 "nvram",
 &nvram_fops
};
int nvram_init(void)
{
 int ret = 0;
 printk("\001" "6" "Generic non-volatile memory driver v%s\n",
  "1.1");
 ret = misc_register(&nvram_dev);
 if (ret != 0)
  goto out;
 nvram_len = nvram_get_size();
 if (nvram_len < 0)
  nvram_len = 8192;
out:
 return ret;
}
void nvram_cleanup(void)
{
        misc_deregister( &nvram_dev );
}
int (* _whoop_init)(void) = nvram_init;
void (* _whoop_exit)(void) = nvram_cleanup;
struct inode *whoop_inode_0;
struct file *whoop_file_0;
struct inode *whoop_inode_1;
struct file *whoop_file_1;
struct inode *whoop_inode_2;
struct file *whoop_file_2;
struct inode *whoop_inode_3;
struct file *whoop_file_3;
struct inode *whoop_inode_4;
struct file *whoop_file_4;
struct pci_dev *whoop_pci_dev;
char *whoop_buf;
struct platform_device *whoop_platform_device;
struct vm_area_struct *whoop_vm_area_struct;
struct cx_dev *whoop_cx_dev;
poll_table *whoop_poll_table;
loff_t *whoop_loff_t;
int whoop_int;
void *whoop_wrapper_write_nvram(void* args)
{
 write_nvram(whoop_file_0, whoop_buf, whoop_int, whoop_loff_t);
 return ((void *)0);
}
void *whoop_wrapper_read_nvram(void* args)
{
 read_nvram(whoop_file_1, whoop_buf, whoop_int, whoop_loff_t);
 return ((void *)0);
}
void *whoop_wrapper_nvram_unlocked_ioctl(void* args)
{
 nvram_unlocked_ioctl(whoop_file_2, whoop_int, whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_nvram_llseek(void* args)
{
 nvram_llseek(whoop_file_3, __VERIFIER_nondet_long(), whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_nvram_cleanup(void* args)
{
 nvram_cleanup();
 return ((void *)0);
}
int main(void)
{
 whoop_inode_0 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_0 = (struct file *) malloc(sizeof(struct file));
 whoop_inode_1 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_1 = (struct file *) malloc(sizeof(struct file));
 whoop_inode_2 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_2 = (struct file *) malloc(sizeof(struct file));
 whoop_inode_3 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_3 = (struct file *) malloc(sizeof(struct file));
 whoop_inode_4 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_4 = (struct file *) malloc(sizeof(struct file));
 whoop_pci_dev = (struct pci_dev *) malloc(sizeof(struct pci_dev));
 whoop_buf = (char *) malloc(sizeof(char));
 whoop_platform_device = (struct platform_device *) malloc(sizeof(struct platform_device));
 whoop_vm_area_struct = (struct vm_area_struct *) malloc(sizeof(struct vm_area_struct));
 whoop_cx_dev = (struct cx_dev *) malloc(sizeof(struct cx_dev));
 whoop_poll_table = (poll_table *) malloc(sizeof(poll_table));
 whoop_loff_t = (loff_t *) malloc(sizeof(loff_t));
 whoop_int = __VERIFIER_nondet_int();
 assume_abort_if_not(whoop_int >= 0);
 int _whoop_init_result = _whoop_init();
 pthread_t pthread_t_read_nvram;
 pthread_t pthread_t_nvram_unlocked_ioctl;
 pthread_create(&pthread_t_read_nvram, ((void *)0), whoop_wrapper_read_nvram, ((void *)0));
 pthread_create(&pthread_t_nvram_unlocked_ioctl, ((void *)0), whoop_wrapper_nvram_unlocked_ioctl, ((void *)0));
 pthread_join(pthread_t_read_nvram, ((void *)0));
 pthread_join(pthread_t_nvram_unlocked_ioctl, ((void *)0));
}
