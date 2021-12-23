#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <smack_svcomp.h>

/* MOD: MOVED FROM ABOVE */                                                                                                                    
struct resource {
 unsigned long start, end;
 const char *name;
 unsigned long flags;
};
/* end MOVED FROM ABOVE */     

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
unsigned int __VERIFIER_nondet_uint(void);
u32 __iter_div_u64_rem(u64 arg0, u32 arg1, u64 *arg2) {
  return __VERIFIER_nondet_uint();
}
void __release_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2) {
  return;
}
void *external_alloc(unsigned int size);
struct resource *__request_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2, const char *arg3, int arg4) {
  return (struct resource *)external_alloc(sizeof(struct resource));
}
void *external_alloc(unsigned int size);
struct tty_driver *__tty_alloc_driver(unsigned int arg0, struct module *arg1, unsigned long arg2) {
  return (struct tty_driver *)external_alloc(sizeof(default_alloc_size));
}
int __VERIFIER_nondet_int(void);
int alloc_chrdev_region(dev_t *arg0, unsigned arg1, unsigned arg2, const char *arg3) {
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
int __VERIFIER_nondet_int(void);
int cdev_add(struct cdev *arg0, dev_t arg1, unsigned arg2) {
  return __VERIFIER_nondet_int();
}
void cdev_del(struct cdev *arg0) {
  return;
}
void cdev_init(struct cdev *arg0, struct file_operations *arg1) {
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
unsigned char __VERIFIER_nondet_uchar(void);
unsigned char inb_p(unsigned int arg0) {
  return __VERIFIER_nondet_uchar();
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
bool __VERIFIER_nondet_bool(void);
bool mm_tlb_flush_pending(struct mm_struct *arg0) {
  return __VERIFIER_nondet_bool();
}
int __VERIFIER_nondet_int(void);
int nonseekable_open(struct inode *arg0, struct file *arg1) {
  return __VERIFIER_nondet_int();
}
void outb_p(unsigned char arg0, unsigned int arg1) {
  return;
}
unsigned int __VERIFIER_nondet_uint(void);
dma_addr_t page_to_phys(struct page *arg0) {
  return __VERIFIER_nondet_uint();
}
int __VERIFIER_nondet_int(void);
int platform_device_add(struct platform_device *arg0) {
  return __VERIFIER_nondet_int();
}
void *external_alloc(unsigned int size);
struct platform_device *platform_device_alloc(const char *arg0, int arg1) {
  return (struct platform_device *)external_alloc(sizeof(struct platform_device));
}
void platform_device_del(struct platform_device *arg0) {
  return;
}
void platform_device_put(struct platform_device *arg0) {
  return;
}
void platform_device_unregister(struct platform_device *arg0) {
  return;
}
void *external_alloc(unsigned int size);
void *rcu_dereference_check(void *arg0, int arg1) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
void *external_alloc(unsigned int size);
void *rcu_dereference_raw(void *arg0) {
  return (void *)external_alloc(sizeof(default_alloc_size));
}
int __VERIFIER_nondet_int(void);
int register_chrdev_region(dev_t arg0, unsigned arg1, const char *arg2) {
  return __VERIFIER_nondet_int();
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
void unregister_chrdev_region(dev_t arg0, unsigned arg1) {
  return;
}
static int major;
static struct mutex pc8736x_gpio_config_lock = { 1, 0 };
static unsigned pc8736x_gpio_base;
static u8 pc8736x_gpio_shadow[4];
static unsigned char superio_cmd = 0;
static unsigned char selected_device = 0xFF;
static int port_offset[] = { 0, 4, 8, 10 };
static struct platform_device *pdev;
static __attribute__((always_inline)) void superio_outb(int addr, int val)
{
 outb_p(addr, superio_cmd);
 outb_p(val, superio_cmd + 1);
}
static __attribute__((always_inline)) int superio_inb(int addr)
{
 outb_p(addr, superio_cmd);
 return inb_p(superio_cmd + 1);
}
static int pc8736x_superio_present(void)
{
 int id;
 superio_cmd = 0x2E;
 id = superio_inb(0x20);
 if (id == 0xe5 || id == 0xe9)
  return superio_cmd;
 superio_cmd = 0x4E;
 id = superio_inb(0x20);
 if (id == 0xe5 || id == 0xe9)
  return superio_cmd;
 return 0;
}
static void device_select(unsigned devldn)
{
 superio_outb(0x7, devldn);
 selected_device = devldn;
}
static void select_pin(unsigned iminor)
{
 device_select(0x7);
 superio_outb(0xF0,
       ((iminor << 1) & 0xF0) | (iminor & 0x7));
}
static __attribute__((always_inline)) u32 pc8736x_gpio_configure_fn(unsigned index, u32 mask, u32 bits,
         u32 func_slct)
{
 u32 config, new_config;
 mutex_lock(&pc8736x_gpio_config_lock);
 device_select(0x7);
 select_pin(index);
 config = superio_inb(func_slct);
 new_config = (config & mask) | bits;
 superio_outb(func_slct, new_config);
 mutex_unlock(&pc8736x_gpio_config_lock);
 return config;
}
u32 pc8736x_gpio_configure(unsigned index, u32 mask, u32 bits)
{
 return pc8736x_gpio_configure_fn(index, mask, bits,
      0xF1);
}
int pc8736x_gpio_get(unsigned minor)
{
 int port, bit, val;
 port = minor >> 3;
 bit = minor & 7;
 val = inb_p(pc8736x_gpio_base + port_offset[port] + 1);
 val >>= bit;
 val &= 1;
 do {} while (0);
 return val;
}
void pc8736x_gpio_set(unsigned minor, int val)
{
 int port, bit, curval;
 minor &= 0x1f;
 port = minor >> 3;
 bit = minor & 7;
 curval = inb_p(pc8736x_gpio_base + port_offset[port] + 0);
 do {} while (0);
 val = (curval & ~(1 << bit)) | (val << bit);
 do {} while (0);
 outb_p(val, pc8736x_gpio_base + port_offset[port] + 0);
 curval = inb_p(pc8736x_gpio_base + port_offset[port] + 0);
 val = inb_p(pc8736x_gpio_base + port_offset[port] + 1);
 do {} while (0);
 pc8736x_gpio_shadow[port] = val;
 __VERIFIER_assert(pc8736x_gpio_shadow[port] == val);
}
int pc8736x_gpio_current(unsigned minor)
{
 int port, bit;
 minor &= 0x1f;
 port = minor >> 3;
 bit = minor & 7;
        u8 tmp = pc8736x_gpio_shadow[port];
        __VERIFIER_assert(tmp == pc8736x_gpio_shadow[port]);
 return ((tmp >> bit) & 0x01);
}
void pc8736x_gpio_change(unsigned index)
{
 pc8736x_gpio_set(index, !pc8736x_gpio_current(index));
}
static struct nsc_gpio_ops pc8736x_gpio_ops = {
 .owner = ((struct module *)0),
 .gpio_config = pc8736x_gpio_configure,
 .gpio_dump = nsc_gpio_dump,
 .gpio_get = pc8736x_gpio_get,
 .gpio_set = pc8736x_gpio_set,
 .gpio_change = pc8736x_gpio_change,
 .gpio_current = pc8736x_gpio_current
};
int pc8736x_gpio_open(struct inode *inode, struct file *file)
{
 unsigned m = iminor(inode);
 file->private_data = &pc8736x_gpio_ops;
 __VERIFIER_assert(file->private_data == &pc8736x_gpio_ops);
 do {} while (0);
 if (m >= 32)
  return -22;
 return nonseekable_open(inode, file);
}
static struct file_operations pc8736x_gpio_fileops = {
 .owner = ((struct module *)0),
 .open = pc8736x_gpio_open,
 .write = nsc_gpio_write,
 .read = nsc_gpio_read,
 .llseek = no_llseek,
};
static void pc8736x_init_shadow(void)
{
 int port;
 for (port = 0; port < 4; ++port)
  pc8736x_gpio_shadow[port]
      = inb_p(pc8736x_gpio_base + port_offset[port]
       + 0);
}
static struct cdev pc8736x_gpio_cdev;
int pc8736x_gpio_init(void)
{
 int rc;
 dev_t devid;
 pdev = platform_device_alloc("pc8736x_gpio", 0);
 if (!pdev)
  return -12;
 rc = platform_device_add(pdev);
 if (rc) {
  rc = -19;
  goto undo_platform_dev_alloc;
 }
 do {} while (0);
 if (!pc8736x_superio_present()) {
  rc = -19;
  do {} while (0);
  goto undo_platform_dev_add;
 }
 pc8736x_gpio_ops.dev = &pdev->dev;
        __VERIFIER_assert(pc8736x_gpio_ops.dev == &pdev->dev);
 rc = superio_inb(0x21);
 if (!(rc & 0x01)) {
  rc = -19;
  do {} while (0);
  goto undo_platform_dev_add;
 }
 device_select(0x7);
 if (!superio_inb(0x30)) {
  rc = -19;
  do {} while (0);
  goto undo_platform_dev_add;
 }
 pc8736x_gpio_base = (superio_inb(0x60) << 8
        | superio_inb(0x61));
 if (!__request_region(((void *)0), (pc8736x_gpio_base), (16), ("pc8736x_gpio"), 0)) {
  rc = -19;
  do {} while (0);
  goto undo_platform_dev_add;
 }
 do {} while (0);
 if (major) {
  devid = (((major) << 20) | (0));
  rc = register_chrdev_region(devid, 32, "pc8736x_gpio");
 } else {
  rc = alloc_chrdev_region(&devid, 0, 32, "pc8736x_gpio");
  major = ((unsigned int) ((devid) >> 20));
 }
 if (rc < 0) {
  do {} while (0);
  goto undo_request_region;
 }
 if (!major) {
  major = rc;
  do {} while (0);
 }
 pc8736x_init_shadow();
 cdev_init(&pc8736x_gpio_cdev, &pc8736x_gpio_fileops);
 cdev_add(&pc8736x_gpio_cdev, devid, 32);
 return 0;
undo_request_region:
 __release_region(((void *)0), (pc8736x_gpio_base), (16));
undo_platform_dev_add:
 platform_device_del(pdev);
undo_platform_dev_alloc:
 platform_device_put(pdev);
 return rc;
}
void pc8736x_gpio_cleanup(void)
{
 do {} while (0);
 cdev_del(&pc8736x_gpio_cdev);
 unregister_chrdev_region((((major) << 20) | (0)), 32);
 __release_region(((void *)0), (pc8736x_gpio_base), (16));
 platform_device_unregister(pdev);
}
int (* _whoop_init)(void) = pc8736x_gpio_init;
void (* _whoop_exit)(void) = pc8736x_gpio_cleanup;
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
struct inode *whoop_inode_5;
struct file *whoop_file_5;
struct inode *whoop_inode_6;
struct file *whoop_file_6;
struct pci_dev *whoop_pci_dev;
const char *whoop_buf;
struct platform_device *whoop_platform_device;
struct vm_area_struct *whoop_vm_area_struct;
struct cx_dev *whoop_cx_dev;
poll_table *whoop_poll_table;
loff_t *whoop_loff_t;
int whoop_int;
void *whoop_wrapper_pc8736x_gpio_set(void* args)
{
 pc8736x_gpio_set(whoop_int, whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_open(void* args)
{
 pc8736x_gpio_open(whoop_inode_1, whoop_file_1);
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_get(void* args)
{
 pc8736x_gpio_get(whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_current(void* args)
{
 pc8736x_gpio_current(whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_configure(void* args)
{
 pc8736x_gpio_configure(whoop_int, whoop_int, whoop_int);
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_cleanup(void* args)
{
 pc8736x_gpio_cleanup();
 return ((void *)0);
}
void *whoop_wrapper_pc8736x_gpio_change(void* args)
{
 pc8736x_gpio_change(whoop_int);
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
 whoop_inode_5 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_5 = (struct file *) malloc(sizeof(struct file));
 whoop_inode_6 = (struct inode *) malloc(sizeof(struct inode));
 whoop_file_6 = (struct file *) malloc(sizeof(struct file));
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
 pthread_t pthread_t_pc8736x_gpio_current;
 pthread_t pthread_t_pc8736x_gpio_configure;
 pthread_create(&pthread_t_pc8736x_gpio_current, ((void *)0), whoop_wrapper_pc8736x_gpio_current, ((void *)0));
 pthread_create(&pthread_t_pc8736x_gpio_configure, ((void *)0), whoop_wrapper_pc8736x_gpio_configure, ((void *)0));
 pthread_join(pthread_t_pc8736x_gpio_current, ((void *)0));
 pthread_join(pthread_t_pc8736x_gpio_configure, ((void *)0));
}
