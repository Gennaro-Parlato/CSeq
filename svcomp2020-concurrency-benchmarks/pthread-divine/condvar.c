#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void abort(void); 
void reach_error(){}
pthread_mutex_t lock;
pthread_cond_t cond;
int x;
_Bool x_set = 0;
void *thread( void *arg ) {
    (void)arg;
    pthread_mutex_lock( &lock );
    while ( !x_set )
        pthread_cond_wait( &cond, &lock );
    (!(x == 42) ? reach_error() : (void)0);
    pthread_mutex_unlock( &lock );
    return ((void *)0);
}
int main() {
    pthread_t t;
    pthread_create( &t, ((void *)0), thread, ((void *)0) );
    for ( int i = 0; i <= 42; i++ )
        x = i;
    x_set = 1;
    pthread_cond_broadcast( &cond );
    pthread_join( t, ((void *)0) );
}
