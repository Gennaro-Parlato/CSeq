#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void abort(void); 
void reach_error(){}
void *worker( void *k ) {
    pthread_key_t *key = k;
    long val = (long)pthread_getspecific( *key );
    (!(val == 0) ? reach_error() : (void)0);
    int r = pthread_setspecific( *key, (void *)42 );
    (!(r == 0) ? reach_error() : (void)0);
    val = (long)pthread_getspecific( *key );
    (!(val == 42) ? reach_error() : (void)0);
    return 0;
}
int main() {
    pthread_key_t key;
    int r = pthread_key_create( &key, ((void *)0) );
    (!(r == 0) ? reach_error() : (void)0);
    pthread_t tid;
    long val = (long)pthread_getspecific( key );
    (!(val == 0) ? reach_error() : (void)0);
    pthread_create( &tid, ((void *)0), worker, &key );
    val = (long)pthread_getspecific( key );
    (!(val == 0) ? reach_error() : (void)0);
    r = pthread_setspecific( key, (void *)16 );
    (!(r == 0) ? reach_error() : (void)0);
    val = (long)pthread_getspecific( key );
    (!(val == 16) ? reach_error() : (void)0);
    pthread_join( tid, ((void *)0) );
    val = (long)pthread_getspecific( key );
    (!(val == 16) ? reach_error() : (void)0);
}
