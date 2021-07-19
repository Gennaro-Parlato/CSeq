#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

typedef struct Obj {
    int field;
} Obj;
void Init_ObjType(Obj *r) {
    r->field = 0;
}
void Operation(Obj *r) {
    r->field++;
}
void Check(Obj *r) {
    if(!(r->field == 1)) {reach_error();abort();}
}
typedef struct WorkStealQueue {
    pthread_mutex_t cs;
    long MaxSize;
    long InitialSize;
    long head;
    long tail;
    Obj* elems[16];
    long mask;
} WorkStealQueue;
WorkStealQueue q;
long atomic_exchange(long *obj, long v) {
    __VERIFIER_atomic_begin();
    long t = *obj;
    *obj = v;
    __VERIFIER_atomic_end();
    return t;
}
_Bool atomic_compare_exchange_strong(long* obj, long* expected, long desired) {
    int ret = 0;
    __VERIFIER_atomic_begin();
    if (*obj == *expected) {
        *obj = desired;
        ret = 1;
    } else {
        *expected = *obj;
        ret = 0;
    }
    __VERIFIER_atomic_end();
    return ret;
}
long readV(long *v) {
    long expected = 0;
    atomic_compare_exchange_strong(v, &expected, 0);
    return expected;
}
void writeV(long *v, long w) {
    atomic_exchange(v, w);
}
void Init_WorkStealQueue(long size) {
    q.MaxSize = 1024 * 1024;
    q.InitialSize = 1024;
    pthread_mutex_init(&q.cs, ((void *)0));
    writeV(&q.head, 0);
    q.mask = size - 1;
    writeV(&q.tail, 0);
}
void Destroy_WorkStealQueue() {}
_Bool Steal(Obj **result) {
    _Bool found;
    pthread_mutex_lock(&q.cs);
    long h = readV(&q.head);
    writeV(&q.head, h + 1);
    if (h < readV(&q.tail)) {
        long temp = h & q.mask;
        *result = q.elems[temp];
        found = 1;
    } else {
        writeV(&q.head, h);
        found = 0;
    }
    pthread_mutex_unlock(&q.cs);
    return found;
}
_Bool SyncPop(Obj **result) {
    _Bool found;
    pthread_mutex_lock(&q.cs);
    long t = readV(&q.tail) - 1;
    writeV(&q.tail, t);
    if (readV(&q.head) <= t) {
        long temp = t & q.mask;
        *result = q.elems[temp];
        found = 1;
    } else {
        writeV(&q.tail, t + 1);
        found = 0;
    }
    if (readV(&q.head) > t) {
        writeV(&q.head, 0);
        writeV(&q.tail, 0);
        found = 0;
    }
    pthread_mutex_unlock(&q.cs);
    return found;
}
_Bool Pop(Obj **result) {
    long t = readV(&q.tail) - 1;
    writeV(&q.tail, t);
    if (readV(&q.head) <= t) {
        long temp = t & q.mask;
        *result = q.elems[temp];
        return 1;
    } else {
        writeV(&q.tail, t + 1);
        return SyncPop(result);
    }
}
void SyncPush(Obj* elem) {
    pthread_mutex_lock(&q.cs);
    long h = readV(&q.head);
    long count = readV(&q.tail) - h;
    h = h & q.mask;
    writeV(&q.head, h);
    writeV(&q.tail, h + count);
    if (count >= q.mask) {
        long newsize = (q.mask == 0 ? q.InitialSize : 2 * (q.mask + 1));
        if(!(newsize < q.MaxSize)) {reach_error();abort();}
        Obj *newtasks[16];
        long i;
        for (i = 0; i < count; i++) {
            long temp = (h + i) & q.mask;
            newtasks[i] = q.elems[temp];
        }
        for (i = 0; i < newsize; i++) {
            q.elems[i] = newtasks[i];
        }
        q.mask = newsize - 1;
        writeV(&q.head, 0);
        writeV(&q.tail, count);
    }
    if(!(count < q.mask)) {reach_error();abort();}
    long t = readV(&q.tail);
    long temp = t & q.mask;
    q.elems[temp] = elem;
    writeV(&q.tail, t + 1);
    pthread_mutex_unlock(&q.cs);
}
void Push(Obj* elem) {
    long t = readV(&q.tail);
    if (t < readV(&q.head) + q.mask
            && t < q.MaxSize)
    {
        long temp = t & q.mask;
        q.elems[temp] = elem;
        writeV(&q.tail, t + 1);
    } else {
        SyncPush(elem);
    }
}
void *Stealer(void *param) {
    int i;
    Obj *r;
    for (i = 0; i < 1; i++) {
        if (Steal(&r)) {
            Operation(r);
        }
    }
    return 0;
}
Obj items[4];
int main(void) {
    int i;
    pthread_t handles[2];
    Init_WorkStealQueue(2);
    for (i = 0; i < 4; i++) {
        Init_ObjType(&items[i]);
    }
    for (i = 0; i < 2; i++) {
        pthread_create(&handles[i], ((void *)0), Stealer, 0);
    }
    for (i = 0; i < 4 / 2; i++) {
        Push(&items[2 * i]);
        Push(&items[2 * i + 1]);
        Obj *r;
        if (Pop(&r)) {
            Operation(r);
        }
    }
    for (i = 0; i < 4 / 2; i++) {
        Obj *r;
        if (Pop(&r)) {
            Operation(r);
        }
    }
    for (i = 0; i < 2; i++) {
        pthread_join(handles[i], ((void *)0));
    }
    for (i = 0; i < 4; i++) {
        Check(&items[i]);
    }
    return 0;
}
