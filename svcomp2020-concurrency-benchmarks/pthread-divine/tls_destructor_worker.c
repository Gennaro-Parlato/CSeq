#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void abort(void); 
void reach_error(){}
void dtor( void *v ) {
    long val = (long)v;
    (!(val != 42) ? reach_error() : (void)0);
}
void *worker( void *k ) {
    pthread_key_t *key = k;
    int r = pthread_setspecific( *key, (void *)42 );
    (!(r == 0) ? reach_error() : (void)0);
    return 0;
}
int main() {
    pthread_key_t key;
    int r = pthread_key_create( &key, &dtor );
    (!(r == 0) ? reach_error() : (void)0);
    pthread_t tid;
    pthread_create( &tid, ((void *)0), worker, &key );
    r = pthread_setspecific( key, (void *)16 );
    (!(r == 0) ? reach_error() : (void)0);
    pthread_join( tid, ((void *)0) );
}
