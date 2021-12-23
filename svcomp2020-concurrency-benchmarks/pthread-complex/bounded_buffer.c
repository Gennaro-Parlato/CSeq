#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

typedef struct bounded_buf_tag
{
    int valid;
    pthread_mutex_t mutex;
    pthread_cond_t not_full;
    pthread_cond_t not_empty;
    size_t item_num;
    size_t max_size;
    size_t head, rear;
    size_t p_wait;
    size_t c_wait;
    void ** buf;
}bounded_buf_t;
int bounded_buf_init(bounded_buf_t * bbuf, size_t sz)
{
    int status = 0;
    if (bbuf == ((void *)0)) return 22;
    bbuf->valid = 0xACDEFA;
    status = pthread_mutex_init(&bbuf->mutex, ((void *)0));
    if (status != 0) return status;
    status = pthread_cond_init(&bbuf->not_full, ((void *)0));
    if (status != 0)
    {
        pthread_mutex_destroy(&bbuf->mutex);
        return status;
    }
    status = pthread_cond_init(&bbuf->not_empty, ((void *)0));
    if (status != 0)
    {
        pthread_cond_destroy(&bbuf->not_full);
        pthread_mutex_destroy(&bbuf->mutex);
        return status;
    }
    bbuf->item_num = 0;
    bbuf->max_size = sz;
    bbuf->head = 0;
    bbuf->rear = 0;
    bbuf->buf = calloc( sz, sizeof(void*) );
    if (bbuf->buf == ((void *)0))
    {
        pthread_mutex_destroy(&bbuf->mutex);
        pthread_cond_destroy(&bbuf->not_full);
        pthread_cond_destroy(&bbuf->not_empty);
        return 12;
    }
    bbuf->head = 0;
    bbuf->rear = 0;
    bbuf->p_wait = 0;
    bbuf->c_wait = 0;
    return 0;
}
int bounded_buf_destroy(bounded_buf_t * bbuf)
{
    int status = 0, status1 = 0, status2 = 0;
    if (bbuf == ((void *)0) || bbuf->valid != 0xACDEFA)
        return 22;
    status = pthread_mutex_lock(&bbuf->mutex);
    if (status != 0) return status;
    bbuf->valid = 0;
    status = pthread_mutex_unlock(&bbuf->mutex);
    if (status != 0) return status;
    status = pthread_mutex_destroy(&bbuf->mutex);
    status1= pthread_cond_destroy(&bbuf->not_full);
    status2= pthread_cond_destroy(&bbuf->not_empty);
    int i;
    if (bbuf->rear >= bbuf->head ) {
        for (i = bbuf->head; i < bbuf->rear; i++) free(bbuf->buf[i]);
    }
    else{
        for (i = bbuf->head; i < bbuf->max_size; i++) free(bbuf->buf[i]);
        for (i = 0; i < bbuf->rear; i++) free(bbuf->buf[i]);
    }
    free(bbuf->buf);
    return (status != 0)? status:((status1 != 0)? status1 : status2);
}
void bounded_buf_putcleanup(void * arg)
{
    bounded_buf_t * bbuf = (bounded_buf_t*) arg;
    bbuf->p_wait--;
    pthread_mutex_unlock(&bbuf->mutex);
}
void bounded_buf_getcleanup(void *arg)
{
    bounded_buf_t * bbuf = (bounded_buf_t*) arg;
    bbuf->c_wait--;
    pthread_mutex_unlock(&bbuf->mutex);
}
int bounded_buf_put(bounded_buf_t * bbuf, void *item)
{
    int status = 0, status1 = 0, status2 = 0;
    if (bbuf == ((void *)0) || bbuf->valid != 0xACDEFA)
        return 22;
    status = pthread_mutex_lock(&bbuf->mutex);
    ;
    if (status != 0) return status;
    if ( (bbuf->rear + 1)% bbuf->max_size == bbuf->head )
    {
        bbuf->p_wait++;
        while ( (bbuf->rear + 1)% bbuf->max_size == bbuf->head ){
            ;
            status = pthread_cond_wait(&bbuf->not_full, &bbuf->mutex);
            if (status != 0) break;
        }
        bbuf->p_wait--;
    }
    if (status == 0){
        bbuf->buf[bbuf->rear]= item;
        bbuf->rear = (bbuf->rear+1)% (bbuf->max_size);
        if (bbuf->c_wait > 0){
            ;
            status1 = pthread_cond_signal(&bbuf->not_empty);
        }
    }
    ;
    status2 = pthread_mutex_unlock(&bbuf->mutex);
    return (status == 0)? status2 : status;
}
int bounded_buf_get(bounded_buf_t *bbuf, void **item)
{
    int status = 0,status1 = 0, status2 = 0;
    if (bbuf == ((void *)0) || item == ((void *)0) || bbuf->valid != 0xACDEFA)
        return 22;
    status = pthread_mutex_lock(&bbuf->mutex);
    ;
    if (status != 0) return status;
    if (bbuf->head == bbuf->rear)
    {
        bbuf->c_wait++;
        while (bbuf->head == bbuf->rear)
        {
            ;
            status = pthread_cond_wait(&bbuf->not_empty, &bbuf->mutex);
            if (status != 0) break;
        }
        bbuf->c_wait--;
    }
    ;
    status = pthread_mutex_unlock(&bbuf->mutex);
    status = pthread_mutex_lock(&bbuf->mutex);
    ;
    if (status == 0)
    {
        if(bbuf->head == bbuf->rear)
        {
            ERROR: {reach_error();abort();}
        }
        *item = bbuf->buf[bbuf->head];
        bbuf->head = (bbuf->head+1) % bbuf->max_size;
        if (bbuf->p_wait > 0){
            ;
            status1 = pthread_cond_signal(&bbuf->not_full);
        }
    }
    ;
    status2 = pthread_mutex_unlock(&bbuf->mutex);
    return (status != 0)? status : (status1 != 0)? status1 : status2;
}
int bounded_buf_is_empty(bounded_buf_t* bbuf)
{
    int status = 0, retval;
    if (bbuf == ((void *)0) || bbuf->valid != 0xACDEFA)
        return -1;
    status = pthread_mutex_lock(&bbuf->mutex);
    if (status != 0) return status;
    retval = (bbuf->rear == bbuf->head )? 1 : 0;
    status = pthread_mutex_unlock(&bbuf->mutex);
    return (status == 0)? retval : -1;
}
int bounded_buf_is_full(bounded_buf_t* bbuf)
{
    int status = 0, retval;
    if (bbuf == ((void *)0) || bbuf->valid != 0xACDEFA) return -1;
    status = pthread_mutex_lock(&bbuf->mutex);
    if (status != 0) return status;
    retval = ( (bbuf->rear + 1) % bbuf->max_size == bbuf->head )? 1 : 0;
    status = pthread_mutex_unlock(&bbuf->mutex);
    return (status == 0)? retval : -1;
}
typedef struct thread_tag
{
    pthread_t pid;
    int id;
    bounded_buf_t * bbuf;
}thread_t;
void * producer_routine(void *arg)
{
    thread_t * thread = (thread_t*) arg;
    int i, temp;
    int ch;
    int status = 0;
    for (i = 0; i < 4; i++)
    {
        ch = __VERIFIER_nondet_int();
        temp = ch;
        status = bounded_buf_put(thread->bbuf, (void*)((int)temp));
        if (status != 0)
            ;
        else
            ;
        fflush(stdout);
    }
    return ((void *)0);
}
void * consumer_routine(void * arg)
{
    thread_t * thread = (thread_t*) arg;
    int i;
    int ch;
    int status = 0;
    void* temp;
    for (i = 0; i < 4; i++)
    {
        status = bounded_buf_get(thread->bbuf, &temp);
        if (status != 0)
            ;
        else
        {
            ch = (char)( (int)temp );
            ;
        }
        fflush(stdout);
    }
    return ((void *)0);
}
int main(void)
{
    thread_t producers[2];
    thread_t consumers[2];
    int i;
    bounded_buf_t buffer;
    bounded_buf_init(&buffer, 3);
    for (i = 0; i < 2; i++)
    {
        producers[i].id = i;
        producers[i].bbuf = &buffer;
        pthread_create(&producers[i].pid, ((void *)0), producer_routine, (void*)&producers[i]);
    }
    for (i = 0; i < 2; i++)
    {
        consumers[i].id = i;
        consumers[i].bbuf = &buffer;
        pthread_create(&consumers[i].pid, ((void *)0), consumer_routine, (void*)&consumers[i]);
    }
    for (i = 0; i < 2; i++)
        pthread_join(producers[i].pid, ((void *)0));
    for (i = 0; i < 2; i++)
        pthread_join(consumers[i].pid, ((void *)0));
    bounded_buf_destroy(&buffer);
    return 0;
}
