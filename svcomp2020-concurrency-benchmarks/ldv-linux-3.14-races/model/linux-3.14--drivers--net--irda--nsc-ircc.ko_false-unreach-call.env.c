// Skip function: pthread_join

// Function: platform_device_register_full
// with type: struct platform_device *platform_device_register_full(const struct platform_device_info *)
// with return type: (struct platform_device)*
struct platform_device *platform_device_register_full(const struct platform_device_info *arg0){
  // Pointer type
  return ldv_malloc(sizeof(struct platform_device));
}

// Function: debug_dma_alloc_coherent
// with type: void debug_dma_alloc_coherent(struct device *, size_t , dma_addr_t , void *)
// with return type: void
void debug_dma_alloc_coherent(struct device *arg0, size_t arg1, dma_addr_t arg2, void *arg3){
  // Void type
  return;
}

// Function: async_wrap_skb
// with type: int async_wrap_skb(struct sk_buff *, __u8 *, int)
// with return type: int
int __VERIFIER_nondet_int(void);
int async_wrap_skb(struct sk_buff *arg0, __u8 *arg1, int arg2){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: async_unwrap_char
// with type: void async_unwrap_char(struct net_device *, struct net_device_stats *, iobuff_t *, __u8 )
// with return type: void
void async_unwrap_char(struct net_device *arg0, struct net_device_stats *arg1, iobuff_t *arg2, __u8 arg3){
  // Void type
  return;
}

// Function: __raw_spin_lock_init
// with type: void __raw_spin_lock_init(raw_spinlock_t *, const char *, struct lock_class_key *)
// with return type: void
void __raw_spin_lock_init(raw_spinlock_t *arg0, const char *arg1, struct lock_class_key *arg2){
  // Void type
  return;
}

// Function: pnp_get_resource
// with type: struct resource *pnp_get_resource(struct pnp_dev *, unsigned long, unsigned int)
// with return type: (struct resource)*
struct resource *pnp_get_resource(struct pnp_dev *arg0, unsigned long arg1, unsigned int arg2){
  // Pointer type
  return ldv_malloc(sizeof(struct resource));
}

// Skip function: pthread_mutex_trylock

// Function: consume_skb
// with type: void consume_skb(struct sk_buff *)
// with return type: void
void consume_skb(struct sk_buff *arg0){
  // Void type
  return;
}

// Function: __const_udelay
// with type: void __const_udelay(unsigned long)
// with return type: void
void __const_udelay(unsigned long arg0){
  // Void type
  return;
}

// Function: sprintf
// with type: int sprintf(char *, const char *, ...)
// with return type: int
int __VERIFIER_nondet_int(void);
int sprintf(char *arg0, const char *arg1, ...){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Skip function: pthread_mutex_lock

// Skip function: pthread_mutex_unlock

// Function: _raw_spin_unlock_irqrestore
// with type: void _raw_spin_unlock_irqrestore(raw_spinlock_t *, unsigned long)
// with return type: void
void _raw_spin_unlock_irqrestore(raw_spinlock_t *arg0, unsigned long arg1){
  // Void type
  return;
}

// Function: irda_setup_dma
// with type: void irda_setup_dma(int, dma_addr_t , int, int)
// with return type: void
void irda_setup_dma(int arg0, dma_addr_t arg1, int arg2, int arg3){
  // Void type
  return;
}

// Function: rtnl_lock
// with type: void rtnl_lock()
// with return type: void
void rtnl_lock(){
  // Void type
  return;
}

// Function: ldv_after_alloc
// with type: void ldv_after_alloc(void *)
// with return type: void
void ldv_after_alloc(void *arg0){
  // Void type
  return;
}

// Function: irda_qos_bits_to_value
// with type: void irda_qos_bits_to_value(struct qos_info *)
// with return type: void
void irda_qos_bits_to_value(struct qos_info *arg0){
  // Void type
  return;
}

// Function: netif_rx
// with type: int netif_rx(struct sk_buff *)
// with return type: int
int __VERIFIER_nondet_int(void);
int netif_rx(struct sk_buff *arg0){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: pnp_unregister_driver
// with type: void pnp_unregister_driver(struct pnp_driver *)
// with return type: void
void pnp_unregister_driver(struct pnp_driver *arg0){
  // Void type
  return;
}

// Skip function: memset

// Function: platform_device_unregister
// with type: void platform_device_unregister(struct platform_device *)
// with return type: void
void platform_device_unregister(struct platform_device *arg0){
  // Void type
  return;
}

// Function: ldv_switch_to_interrupt_context
// with type: void ldv_switch_to_interrupt_context()
// with return type: void
void ldv_switch_to_interrupt_context(){
  // Void type
  return;
}

// Function: _raw_spin_unlock
// with type: void _raw_spin_unlock(raw_spinlock_t *)
// with return type: void
void _raw_spin_unlock(raw_spinlock_t *arg0){
  // Void type
  return;
}

// Function: ldv_check_alloc_flags
// with type: void ldv_check_alloc_flags(gfp_t )
// with return type: void
void ldv_check_alloc_flags(gfp_t arg0){
  // Void type
  return;
}

// Function: irda_init_max_qos_capabilies
// with type: void irda_init_max_qos_capabilies(struct qos_info *)
// with return type: void
void irda_init_max_qos_capabilies(struct qos_info *arg0){
  // Void type
  return;
}

// Function: rtnl_unlock
// with type: void rtnl_unlock()
// with return type: void
void rtnl_unlock(){
  // Void type
  return;
}

// Function: netif_device_attach
// with type: void netif_device_attach(struct net_device *)
// with return type: void
void netif_device_attach(struct net_device *arg0){
  // Void type
  return;
}

// Skip function: __VERIFIER_nondet_ulong

// Function: __release_region
// with type: void __release_region(struct resource *, resource_size_t , resource_size_t )
// with return type: void
void __release_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2){
  // Void type
  return;
}

// Function: __ldv_spin_lock
// with type: void __ldv_spin_lock(spinlock_t *)
// with return type: void
void __ldv_spin_lock(spinlock_t *arg0){
  // Void type
  return;
}

// Function: ldv_switch_to_process_context
// with type: void ldv_switch_to_process_context()
// with return type: void
void ldv_switch_to_process_context(){
  // Void type
  return;
}

// Function: unregister_netdevice_queue
// with type: void unregister_netdevice_queue(struct net_device *, struct list_head *)
// with return type: void
void unregister_netdevice_queue(struct net_device *arg0, struct list_head *arg1){
  // Void type
  return;
}

// Function: __netdev_alloc_skb
// with type: struct sk_buff *__netdev_alloc_skb(struct net_device *, unsigned int, gfp_t )
// with return type: (struct sk_buff)*
struct sk_buff *__netdev_alloc_skb(struct net_device *arg0, unsigned int arg1, gfp_t arg2){
  // Pointer type
  return ldv_malloc(sizeof(struct sk_buff));
}

// Function: printk
// with type: int printk(const char *, ...)
// with return type: int
int __VERIFIER_nondet_int(void);
int printk(const char *arg0, ...){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: warn_slowpath_null
// with type: void warn_slowpath_null(const char *, const int)
// with return type: void
void warn_slowpath_null(const char *arg0, const int arg1){
  // Void type
  return;
}

// Function: capable
// with type: bool capable(int)
// with return type: bool 
bool __VERIFIER_nondet_bool(void);
bool capable(int arg0){
  // Typedef type
  // Real type: _Bool
  // Simple type
  return __VERIFIER_nondet_bool();
}

// Skip function: calloc

// Function: skb_put
// with type: unsigned char *skb_put(struct sk_buff *, unsigned int)
// with return type: (unsigned char)*
unsigned char *skb_put(struct sk_buff *arg0, unsigned int arg1){
  unsigned char *ret_val = arg0->data + arg0->tail;
  // a more precise implementation of skb_put would actually re-allocate memory
  // here
  arg0->tail += arg1;
  // Pointer type
  return ret_val;
}

// Function: do_gettimeofday
// with type: void do_gettimeofday(struct timeval *)
// with return type: void
void do_gettimeofday(struct timeval *arg0){
  // Void type
  return;
}

// Function: netif_device_detach
// with type: void netif_device_detach(struct net_device *)
// with return type: void
void netif_device_detach(struct net_device *arg0){
  // Void type
  return;
}

// Skip function: __VERIFIER_error

// Function: net_ratelimit
// with type: int net_ratelimit()
// with return type: int
int __VERIFIER_nondet_int(void);
int net_ratelimit(){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: __udelay
// with type: void __udelay(unsigned long)
// with return type: void
void __udelay(unsigned long arg0){
  // Void type
  return;
}

// Function: request_dma
// with type: int request_dma(unsigned int, const char *)
// with return type: int
int __VERIFIER_nondet_int(void);
int request_dma(unsigned int arg0, const char *arg1){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Skip function: free

// Skip function: malloc

// Function: irlap_close
// with type: void irlap_close(struct irlap_cb *)
// with return type: void
void irlap_close(struct irlap_cb *arg0){
  // Void type
  return;
}

// Function: ldv_failed_register_netdev
// with type: int ldv_failed_register_netdev()
// with return type: int
int __VERIFIER_nondet_int(void);
int ldv_failed_register_netdev(){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: _raw_spin_lock
// with type: void _raw_spin_lock(raw_spinlock_t *)
// with return type: void
void _raw_spin_lock(raw_spinlock_t *arg0){
  // Void type
  return;
}

// Function: __request_region
// with type: struct resource *__request_region(struct resource *, resource_size_t , resource_size_t , const char *, int)
// with return type: (struct resource)*
struct resource *__request_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2, const char *arg3, int arg4){
  // Pointer type
  return ldv_malloc(sizeof(struct resource));
}

// Function: debug_dma_free_coherent
// with type: void debug_dma_free_coherent(struct device *, size_t , void *, dma_addr_t )
// with return type: void
void debug_dma_free_coherent(struct device *arg0, size_t arg1, void *arg2, dma_addr_t arg3){
  // Void type
  return;
}

// Function: alloc_irdadev
// with type: struct net_device *alloc_irdadev(int)
// with return type: (struct net_device)*
struct net_device *alloc_irdadev(int arg0){
  // Pointer type
  return ldv_malloc(sizeof(struct net_device));
}

// Function: memcpy
// with type: void *memcpy(void *, const void *, size_t )
// with return type: (void)*
void *memcpy(void *arg0, const void *arg1, size_t arg2){
  // Pointer type
  return ldv_malloc(0UL);
}

// Skip function: __VERIFIER_nondet_int

// Function: free_dma
// with type: void free_dma(unsigned int)
// with return type: void
void free_dma(unsigned int arg0){
  // Void type
  return;
}

// Function: irlap_open
// with type: struct irlap_cb *irlap_open(struct net_device *, struct qos_info *, const char *)
// with return type: (struct irlap_cb)*
struct irlap_cb *irlap_open(struct net_device *arg0, struct qos_info *arg1, const char *arg2){
  // Pointer type
  return ldv_malloc(0UL);
}

// Function: netpoll_trap
// with type: int netpoll_trap()
// with return type: int
int __VERIFIER_nondet_int(void);
int netpoll_trap(){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Function: irda_device_set_media_busy
// with type: void irda_device_set_media_busy(struct net_device *, int)
// with return type: void
void irda_device_set_media_busy(struct net_device *arg0, int arg1){
  // Void type
  return;
}

// Function: __netif_schedule
// with type: void __netif_schedule(struct Qdisc *)
// with return type: void
void __netif_schedule(struct Qdisc *arg0){
  // Void type
  return;
}

// Function: pnp_register_driver
// with type: int pnp_register_driver(struct pnp_driver *)
// with return type: int
int __VERIFIER_nondet_int(void);
int pnp_register_driver(struct pnp_driver *arg0){
  // Simple type
  return __VERIFIER_nondet_int();
}

// Skip function: pthread_create

