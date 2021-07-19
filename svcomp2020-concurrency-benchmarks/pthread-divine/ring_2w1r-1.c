#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void *reader_two( void *arg ) {
    Ring *r = arg;
    long val = 0, i = 0;
    int read[ 8 ] = { 0 };
    while ( i < 2 * 8 ) {
        if ( ring_empty( r ) )
            continue;
        val = ring_dequeue( r );
        (!(val > 0) ? reach_error() : (void)0);
        (!(val <= 8) ? reach_error() : (void)0);
        ++read[ val - 1 ];
        for ( int i = 0; i < val; ++i ) {
            (!(read[ i ] <= 2) ? reach_error() : (void)0);
            (!(read[ i ] > 0) ? reach_error() : (void)0);
        }
        ++i;
    }
    return 0;
}
int main() {
    pthread_t reader, writer;
    Ring r;
    ring_init( &r );
    pthread_create( &reader, ((void *)0), &reader_two, &r );
    pthread_create( &writer, ((void *)0), &writer_fn, &r );
    writer_fn( &r );
    long status;
    pthread_join( reader, ((void *)0) );
    pthread_join( writer, ((void *)0) );
}
