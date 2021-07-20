#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
void abort(void); 
void reach_error(){}
struct FifoNode_ {
    int *read;
    int buffer[ 2 ];
    int *volatile write;
    struct FifoNode_ *next;
};
typedef struct FifoNode_ FifoNode;
FifoNode *fifo_node_init( FifoNode *self ) {
    self->read = self->write = self->buffer;
    self->next = 0;
    return self;
}
struct Fifo_ {
    FifoNode *head;
    FifoNode *volatile tail;
};
typedef struct Fifo_ Fifo;
_Bool fifo_empty( Fifo *self ) {
    return self->head == self->tail && self->head->read >= self->head->write;
}
Fifo *fifo_init( Fifo *self ) {
    self->head = self->tail = fifo_node_init( malloc( sizeof( FifoNode ) ) );
    (!(fifo_empty( self )) ? reach_error() : (void)0);
    return self;
}
void *fifo_destroy( Fifo *self ) {
    while ( self->head != self->tail ) {
        FifoNode *next = self->head->next;
        (!(next != 0) ? reach_error() : (void)0);
        free( self->head );
        self->head = next;
    }
    free( self->head );
    return self;
}
void fifo_push( Fifo *self, int x ) {
    FifoNode *t;
    if ( self->tail->write == self->tail->buffer + 2 )
        t = fifo_node_init( malloc( sizeof( FifoNode ) ) );
    else
        t = self->tail;
    *t->write = x;
    ++t->write;
    if ( self->tail != t ) {
        self->tail->next = t;
        self->tail = t;
    }
}
int fifo_size( Fifo *self ) {
    int size = 0;
    FifoNode *n = self->head;
    do {
        size += n->write - n->read;
        n = n->next;
    } while ( n );
    return size;
}
void fifo_drop_head( Fifo *self ) {
    FifoNode *old = self->head;
    self->head = self->head->next;
    (!(!!self->head) ? reach_error() : (void)0);
    free( old );
}
void fifo_pop( Fifo *self ) {
  again:
    (!(!fifo_empty( self )) ? reach_error() : (void)0);
    ++self->head->read;
    if ( self->head->read == self->head->buffer + 2 ) {
        if ( self->head->next != ((void *)0) )
        {
            fifo_drop_head( self );
        }
    }
    if ( self->head != self->tail && self->head->read > self->head->buffer + 2 )
    {
        fifo_drop_head( self );
        goto again;
    }
}
int *fifo_front( Fifo *self, _Bool wait ) {
    while ( wait && fifo_empty( self ) ) ;
    (!(!!self->head) ? reach_error() : (void)0);
    (!(!fifo_empty( self )) ? reach_error() : (void)0);
    if ( self->head->read == self->head->buffer + 2 ) {
        fifo_drop_head( self );
    }
    return self->head->read;
}
void *pusher( void *q_ ) {
    Fifo *q = q_;
    for ( int i = 0; i < 7; ++i )
        fifo_push( q, 42 + i );
    return 0;
};
int main() {
    Fifo q;
    fifo_init( &q );
    pthread_t p;
    pthread_create( &p, 0, &pusher, &q );
    for ( int i = 0; i < 7; ++i ) {
        int got = *fifo_front( &q, 1 );
        fifo_pop( &q );
        (!(got == 42 + i) ? reach_error() : (void)0);
    }
    (!(fifo_empty( &q )) ? reach_error() : (void)0);
    pthread_join( p, 0 );
    (!(fifo_empty( &q )) ? reach_error() : (void)0);
    fifo_destroy( &q );
    return 0;
}
