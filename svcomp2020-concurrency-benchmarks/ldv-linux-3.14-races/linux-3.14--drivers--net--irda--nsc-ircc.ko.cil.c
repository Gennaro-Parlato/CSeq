#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
pthread_mutex_t smutex_NOT_ARG_SIGN ;
void ldv_spin_lock_NOT_ARG_SIGN(void)
{
  {
  {
  pthread_mutex_lock(& smutex_NOT_ARG_SIGN);
  }
  return;
}
}
void ldv_spin_unlock_NOT_ARG_SIGN(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_NOT_ARG_SIGN);
  }
  return;
}
}
int ldv_spin_trylock_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_NOT_ARG_SIGN);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_NOT_ARG_SIGN(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_NOT_ARG_SIGN();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_NOT_ARG_SIGN(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_NOT_ARG_SIGN(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_NOT_ARG_SIGN();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex__xmit_lock_of_netdev_queue ;
void ldv_spin_lock__xmit_lock_of_netdev_queue(void)
{
  {
  {
  pthread_mutex_lock(& smutex__xmit_lock_of_netdev_queue);
  }
  return;
}
}
void ldv_spin_unlock__xmit_lock_of_netdev_queue(void)
{
  {
  {
  pthread_mutex_unlock(& smutex__xmit_lock_of_netdev_queue);
  }
  return;
}
}
int ldv_spin_trylock__xmit_lock_of_netdev_queue(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex__xmit_lock_of_netdev_queue);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait__xmit_lock_of_netdev_queue(void)
{
  {
  return;
}
}
int ldv_spin_is_locked__xmit_lock_of_netdev_queue(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock__xmit_lock_of_netdev_queue(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked__xmit_lock_of_netdev_queue();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended__xmit_lock_of_netdev_queue(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock__xmit_lock_of_netdev_queue(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock__xmit_lock_of_netdev_queue();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_addr_list_lock_of_net_device ;
void ldv_spin_lock_addr_list_lock_of_net_device(void)
{
  {
  {
  pthread_mutex_lock(& smutex_addr_list_lock_of_net_device);
  }
  return;
}
}
void ldv_spin_unlock_addr_list_lock_of_net_device(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_addr_list_lock_of_net_device);
  }
  return;
}
}
int ldv_spin_trylock_addr_list_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_addr_list_lock_of_net_device);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_addr_list_lock_of_net_device(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_addr_list_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_addr_list_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_addr_list_lock_of_net_device();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_addr_list_lock_of_net_device(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_addr_list_lock_of_net_device(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_addr_list_lock_of_net_device();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_alloc_lock_of_task_struct ;
void ldv_spin_lock_alloc_lock_of_task_struct(void)
{
  {
  {
  pthread_mutex_lock(& smutex_alloc_lock_of_task_struct);
  }
  return;
}
}
void ldv_spin_unlock_alloc_lock_of_task_struct(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_alloc_lock_of_task_struct);
  }
  return;
}
}
int ldv_spin_trylock_alloc_lock_of_task_struct(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_alloc_lock_of_task_struct);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_alloc_lock_of_task_struct(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_alloc_lock_of_task_struct(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_alloc_lock_of_task_struct(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_alloc_lock_of_task_struct();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_alloc_lock_of_task_struct(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_alloc_lock_of_task_struct(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_alloc_lock_of_task_struct();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_dma_spin_lock ;
void ldv_spin_lock_dma_spin_lock(void)
{
  {
  {
  pthread_mutex_lock(& smutex_dma_spin_lock);
  }
  return;
}
}
void ldv_spin_unlock_dma_spin_lock(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_dma_spin_lock);
  }
  return;
}
}
int ldv_spin_trylock_dma_spin_lock(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_dma_spin_lock);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_dma_spin_lock(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_dma_spin_lock(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_dma_spin_lock(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_dma_spin_lock();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_dma_spin_lock(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_dma_spin_lock(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_dma_spin_lock();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_i_lock_of_inode ;
void ldv_spin_lock_i_lock_of_inode(void)
{
  {
  {
  pthread_mutex_lock(& smutex_i_lock_of_inode);
  }
  return;
}
}
void ldv_spin_unlock_i_lock_of_inode(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_i_lock_of_inode);
  }
  return;
}
}
int ldv_spin_trylock_i_lock_of_inode(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_i_lock_of_inode);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_i_lock_of_inode(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_i_lock_of_inode(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_i_lock_of_inode(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_i_lock_of_inode();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_i_lock_of_inode(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_i_lock_of_inode(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_i_lock_of_inode();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_lock ;
void ldv_spin_lock_lock(void)
{
  {
  {
  pthread_mutex_lock(& smutex_lock);
  }
  return;
}
}
void ldv_spin_unlock_lock(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_lock);
  }
  return;
}
}
int ldv_spin_trylock_lock(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_lock);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_lock(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_lock(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_lock(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_lock();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_lock(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_lock(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_lock();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_lock_of_NOT_ARG_SIGN ;
void ldv_spin_lock_lock_of_NOT_ARG_SIGN(void)
{
  {
  {
  pthread_mutex_lock(& smutex_lock_of_NOT_ARG_SIGN);
  }
  return;
}
}
void ldv_spin_unlock_lock_of_NOT_ARG_SIGN(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_lock_of_NOT_ARG_SIGN);
  }
  return;
}
}
int ldv_spin_trylock_lock_of_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_lock_of_NOT_ARG_SIGN);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_lock_of_NOT_ARG_SIGN(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_lock_of_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_lock_of_NOT_ARG_SIGN(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_lock_of_NOT_ARG_SIGN();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_lock_of_NOT_ARG_SIGN(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_lock_of_NOT_ARG_SIGN(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_lock_of_NOT_ARG_SIGN();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_lock_of_nsc_ircc_cb ;
void ldv_spin_lock_lock_of_nsc_ircc_cb(void)
{
  {
  {
  pthread_mutex_lock(& smutex_lock_of_nsc_ircc_cb);
  }
  return;
}
}
void ldv_spin_unlock_lock_of_nsc_ircc_cb(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_lock_of_nsc_ircc_cb);
  }
  return;
}
}
int ldv_spin_trylock_lock_of_nsc_ircc_cb(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_lock_of_nsc_ircc_cb);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_lock_of_nsc_ircc_cb(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_lock_of_nsc_ircc_cb(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_lock_of_nsc_ircc_cb(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_lock_of_nsc_ircc_cb();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_lock_of_nsc_ircc_cb(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_lock_of_nsc_ircc_cb(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_lock_of_nsc_ircc_cb();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_lru_lock_of_netns_frags ;
void ldv_spin_lock_lru_lock_of_netns_frags(void)
{
  {
  {
  pthread_mutex_lock(& smutex_lru_lock_of_netns_frags);
  }
  return;
}
}
void ldv_spin_unlock_lru_lock_of_netns_frags(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_lru_lock_of_netns_frags);
  }
  return;
}
}
int ldv_spin_trylock_lru_lock_of_netns_frags(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_lru_lock_of_netns_frags);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_lru_lock_of_netns_frags(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_lru_lock_of_netns_frags(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_lru_lock_of_netns_frags(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_lru_lock_of_netns_frags();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_lru_lock_of_netns_frags(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_lru_lock_of_netns_frags(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_lru_lock_of_netns_frags();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_node_size_lock_of_pglist_data ;
void ldv_spin_lock_node_size_lock_of_pglist_data(void)
{
  {
  {
  pthread_mutex_lock(& smutex_node_size_lock_of_pglist_data);
  }
  return;
}
}
void ldv_spin_unlock_node_size_lock_of_pglist_data(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_node_size_lock_of_pglist_data);
  }
  return;
}
}
int ldv_spin_trylock_node_size_lock_of_pglist_data(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_node_size_lock_of_pglist_data);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_node_size_lock_of_pglist_data(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_node_size_lock_of_pglist_data(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_node_size_lock_of_pglist_data(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_node_size_lock_of_pglist_data();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_node_size_lock_of_pglist_data(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_node_size_lock_of_pglist_data(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_node_size_lock_of_pglist_data();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_ptl ;
void ldv_spin_lock_ptl(void)
{
  {
  {
  pthread_mutex_lock(& smutex_ptl);
  }
  return;
}
}
void ldv_spin_unlock_ptl(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_ptl);
  }
  return;
}
}
int ldv_spin_trylock_ptl(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_ptl);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_ptl(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_ptl(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_ptl(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_ptl();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_ptl(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_ptl(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_ptl();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_siglock_of_sighand_struct ;
void ldv_spin_lock_siglock_of_sighand_struct(void)
{
  {
  {
  pthread_mutex_lock(& smutex_siglock_of_sighand_struct);
  }
  return;
}
}
void ldv_spin_unlock_siglock_of_sighand_struct(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_siglock_of_sighand_struct);
  }
  return;
}
}
int ldv_spin_trylock_siglock_of_sighand_struct(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_siglock_of_sighand_struct);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_siglock_of_sighand_struct(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_siglock_of_sighand_struct(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_siglock_of_sighand_struct(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_siglock_of_sighand_struct();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_siglock_of_sighand_struct(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_siglock_of_sighand_struct(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_siglock_of_sighand_struct();
    }
    return (1);
  } else {
  }
  return (0);
}
}
pthread_mutex_t smutex_tx_global_lock_of_net_device ;
void ldv_spin_lock_tx_global_lock_of_net_device(void)
{
  {
  {
  pthread_mutex_lock(& smutex_tx_global_lock_of_net_device);
  }
  return;
}
}
void ldv_spin_unlock_tx_global_lock_of_net_device(void)
{
  {
  {
  pthread_mutex_unlock(& smutex_tx_global_lock_of_net_device);
  }
  return;
}
}
int ldv_spin_trylock_tx_global_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = pthread_mutex_trylock(& smutex_tx_global_lock_of_net_device);
  }
  return (tmp);
}
}
void ldv_spin_unlock_wait_tx_global_lock_of_net_device(void)
{
  {
  return;
}
}
int ldv_spin_is_locked_tx_global_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = ldv_undef_int();
  }
  if (tmp != 0) {
    return (1);
  } else {
    return (0);
  }
}
}
int ldv_spin_can_lock_tx_global_lock_of_net_device(void)
{
  int tmp ;
  {
  {
  tmp = ldv_spin_is_locked_tx_global_lock_of_net_device();
  }
  return (tmp == 0);
}
}
int ldv_spin_is_contended_tx_global_lock_of_net_device(void)
{
  int is_spin_contended ;
  {
  {
  is_spin_contended = ldv_undef_int();
  }
  if (is_spin_contended != 0) {
    return (0);
  } else {
    return (1);
  }
}
}
int ldv_atomic_dec_and_lock_tx_global_lock_of_net_device(void)
{
  int atomic_value_after_dec ;
  {
  {
  atomic_value_after_dec = ldv_undef_int();
  }
  if (atomic_value_after_dec == 0) {
    {
    ldv_spin_lock_tx_global_lock_of_net_device();
    }
    return (1);
  } else {
  }
  return (0);
}
}
void free(void *);
void kfree(void const *p) {
  free((void *)p);
}
struct platform_device *platform_device_register_full(const struct platform_device_info *arg0){
  return ldv_malloc(sizeof(struct platform_device));
}
void debug_dma_alloc_coherent(struct device *arg0, size_t arg1, dma_addr_t arg2, void *arg3){
  return;
}
int __VERIFIER_nondet_int(void);
int async_wrap_skb(struct sk_buff *arg0, __u8 *arg1, int arg2){
  return __VERIFIER_nondet_int();
}
void async_unwrap_char(struct net_device *arg0, struct net_device_stats *arg1, iobuff_t *arg2, __u8 arg3){
  return;
}
void __raw_spin_lock_init(raw_spinlock_t *arg0, const char *arg1, struct lock_class_key *arg2){
  return;
}
struct resource *pnp_get_resource(struct pnp_dev *arg0, unsigned long arg1, unsigned int arg2){
  return ldv_malloc(sizeof(struct resource));
}
void consume_skb(struct sk_buff *arg0){
  return;
}
void __const_udelay(unsigned long arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int sprintf(char *arg0, const char *arg1, ...){
  return __VERIFIER_nondet_int();
}
void _raw_spin_unlock_irqrestore(raw_spinlock_t *arg0, unsigned long arg1){
  return;
}
void irda_setup_dma(int arg0, dma_addr_t arg1, int arg2, int arg3){
  return;
}
void rtnl_lock(){
  return;
}
void ldv_after_alloc(void *arg0){
  return;
}
void irda_qos_bits_to_value(struct qos_info *arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int netif_rx(struct sk_buff *arg0){
  return __VERIFIER_nondet_int();
}
void pnp_unregister_driver(struct pnp_driver *arg0){
  return;
}
void platform_device_unregister(struct platform_device *arg0){
  return;
}
void ldv_switch_to_interrupt_context(){
  return;
}
void _raw_spin_unlock(raw_spinlock_t *arg0){
  return;
}
void ldv_check_alloc_flags(gfp_t arg0){
  return;
}
void irda_init_max_qos_capabilies(struct qos_info *arg0){
  return;
}
void rtnl_unlock(){
  return;
}
void netif_device_attach(struct net_device *arg0){
  return;
}
void __release_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2){
  return;
}
void __ldv_spin_lock(spinlock_t *arg0){
  return;
}
void ldv_switch_to_process_context(){
  return;
}
void unregister_netdevice_queue(struct net_device *arg0, struct list_head *arg1){
  return;
}
struct sk_buff *__netdev_alloc_skb(struct net_device *arg0, unsigned int arg1, gfp_t arg2){
  return ldv_malloc(sizeof(struct sk_buff));
}
int __VERIFIER_nondet_int(void);
int printk(const char *arg0, ...){
  return __VERIFIER_nondet_int();
}
void warn_slowpath_null(const char *arg0, const int arg1){
  return;
}
bool __VERIFIER_nondet_bool(void);
bool capable(int arg0){
  return __VERIFIER_nondet_bool();
}
unsigned char *skb_put(struct sk_buff *arg0, unsigned int arg1){
  unsigned char *ret_val = arg0->data + arg0->tail;
  arg0->tail += arg1;
  return ret_val;
}
void do_gettimeofday(struct timeval *arg0){
  return;
}
void netif_device_detach(struct net_device *arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int net_ratelimit(){
  return __VERIFIER_nondet_int();
}
void __udelay(unsigned long arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int request_dma(unsigned int arg0, const char *arg1){
  return __VERIFIER_nondet_int();
}
void irlap_close(struct irlap_cb *arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int ldv_failed_register_netdev(){
  return __VERIFIER_nondet_int();
}
void _raw_spin_lock(raw_spinlock_t *arg0){
  return;
}
struct resource *__request_region(struct resource *arg0, resource_size_t arg1, resource_size_t arg2, const char *arg3, int arg4){
  return ldv_malloc(sizeof(struct resource));
}
void debug_dma_free_coherent(struct device *arg0, size_t arg1, void *arg2, dma_addr_t arg3){
  return;
}
struct net_device *alloc_irdadev(int arg0){
  return ldv_malloc(sizeof(struct net_device));
}
void *memcpy(void *arg0, const void *arg1, size_t arg2){
  return ldv_malloc(0UL);
}
void free_dma(unsigned int arg0){
  return;
}
struct irlap_cb *irlap_open(struct net_device *arg0, struct qos_info *arg1, const char *arg2){
  return ldv_malloc(0UL);
}
int __VERIFIER_nondet_int(void);
int netpoll_trap(){
  return __VERIFIER_nondet_int();
}
void irda_device_set_media_busy(struct net_device *arg0, int arg1){
  return;
}
void __netif_schedule(struct Qdisc *arg0){
  return;
}
int __VERIFIER_nondet_int(void);
int pnp_register_driver(struct pnp_driver *arg0){
  return __VERIFIER_nondet_int();
}
