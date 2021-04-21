#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>
#include <assert.h>

/**
 * This version try to simulate the bug and succeeded
 */

#define CASDEF(t,ty) \
    int __VERIFIER_atomic_ ## t ## _cas(ty *p, ty cmp, ty new) { \
        if (*p == cmp) { \
            *p = new; \
            return 1; \
        } \
        else \
            return 0; \
    }

#define CAS(t,x,y,z) __VERIFIER_atomic_ ## t ## _cas(x,y,z)

#define LOCATION_ARRAY_SIZE 8 // 8 is original number
#define COLLISION_ARRAY_SIZE 1

#define POP 0
#define PUSH 1
#define TRUE 1
#define FALSE 0

typedef struct Cell Cell;
struct Cell {
    Cell        *pnext;
    int         pdata;
};

typedef struct ThreadInfo ThreadInfo;
struct ThreadInfo {
    unsigned int  id;
    int           op;
    Cell          cell;
};

typedef struct Simple_Stack Simple_Stack;
struct Simple_Stack {
    Cell *ptop;
};


Simple_Stack S;
ThreadInfo *location[LOCATION_ARRAY_SIZE];
int collision;

int unique_id = 0;
void StackOp(ThreadInfo *p);
int TryPerformStackOp(ThreadInfo *p);

CASDEF(int, int)
CASDEF(ti, ThreadInfo*)
CASDEF(c, Cell*)

/**
 * THREADS and STUFF
 */

#define NUM_THREADS 4      //
ThreadInfo threads[NUM_THREADS];
int allocated[NUM_THREADS];

ThreadInfo* __VERIFIER_atomic_malloc_ThreadInfo() {
    int i;
    __VERIFIER_assume(0 <= i && i < NUM_THREADS);
    __VERIFIER_assume(!allocated[i]);
    allocated[i] = 1;
    return &threads[i];
}




void __VERIFIER_atomic_free_ThreadInfo(ThreadInfo* ti) {
    int i;
    __VERIFIER_assume(0 <= i && i < NUM_THREADS);
    __VERIFIER_assume(&threads[i] == ti);
    allocated[i] = 0; // BUG Free the memory to witness the ABA bug
}




/**
 *  ALGORITHM
 */
void LesOP(ThreadInfo *p) {
    // {
    int mypid = p->id;
    location[mypid] = p;
    int him = collision;   // GetPosition(p) = pos = 0;

    __VERIFIER_assume (CAS(int, &collision, him, mypid));

    if (him > 0) {
        ThreadInfo* q = location[him];
        if (q != NULL && q->id == him && q->op != p->op) {
            if (CAS(ti, &location[mypid], p, NULL)) {
                if (__VERIFIER_atomic_TryCollision(p, q, him) == TRUE) {
                    return;
                } else {
                    goto stack;
                }
            }
            else {
                __VERIFIER_atomic_FinishCollision(p);
                return;
            }
        }
    }
    // delay (p->spin);
    if (!CAS(ti, &location[mypid], p, NULL)) {
        __VERIFIER_atomic_FinishCollision(p);
        return;
    }
stack:
    if (TryPerformStackOp(p) == TRUE) {
        return;
    }
    // }
    __VERIFIER_assume(0);  // One loop is enough to simulate the bug
}

int TryPerformStackOp(ThreadInfo * p) {
    Cell *phead, *pnext;
    if (p->op == PUSH) {
        phead = S.ptop;
        p->cell.pnext = phead;
        if (CAS(c, &S.ptop, phead, &p->cell)) {
            return TRUE;
        } else {
            return FALSE;
        }
    }
    if (p->op == POP) {
        phead = S.ptop;
        if (phead == NULL) {
            // p->cell = EMPTY;  //Original code
            p->cell.pnext = 0; p->cell.pdata = 2;    // 2 means EMPTY
            return TRUE;
        }
        pnext = phead->pnext;
        if (CAS(c, &S.ptop, phead, pnext)) {
            // p->cell.pdata = phead->pdata;  // Jad Injected code
            p->cell = *phead;  // Truc, make the assignment above more general
            // Injected code  // TRUC
            __VERIFIER_atomic_begin();
            int i = __VERIFIER_nondet_int();  // Guess index instead of guess pointer to structure (major change, see below comment)
            __VERIFIER_assume(0 <= i && i < NUM_THREADS);
            __VERIFIER_assume(&threads[i].cell == phead);
            allocated[i] = 0;
            __VERIFIER_atomic_end();
            // OLD CODE
            // ThreadInfo *oldti;     // this will get init to 0 in Lazy-CSeq, that's why it cannot detect the problem
            // __VERIFIER_assume(&oldti->cell == phead);
            // __VERIFIER_atomic_free_ThreadInfo(oldti);
            // assert(0);
            // END: Injected code
            //
            //
            return TRUE;
        }
        else {
            // p->cell = EMPTY;
            p->cell.pnext = 0; p->cell.pdata = 2;    // 2 means EMPTY
            return FALSE;
        }
    }
}


void __VERIFIER_atomic_FinishCollision(ThreadInfo * p) {
    if (p->op == POP) {
        int mypid = p->id;
        // p->cell.pdata = location[mypid]->cell.pdata;  // Jad injected code
        p->cell = location[mypid]->cell;
        location[mypid] = NULL;
    }
}

int __VERIFIER_atomic_TryCollision(ThreadInfo * p, ThreadInfo * q, int him) {
    int mypid = p->id;
    if (p->op == PUSH) {
        if (CAS(ti, &location[him], q, p)) {
            return TRUE;
        }
        else {
            return FALSE;
        }
    }
    if (p->op == POP) {
        if (CAS(ti, &location[him], q, NULL)) {
            // p->cell.pdata = q->cell.pdata;   // Jad injected code
            p->cell = q->cell;
            location[mypid] = NULL;
            return TRUE;
        }
        else {
            return FALSE;
        }
    }
    return FALSE;
}


/**
 * Injected code
 */

void Init() {
    S.ptop = NULL;
}

// Derive from
// void StackOp (ThreadInfo * pInfo) {
//     if (TryPerformStackOp (p) == FALSE)
//         LesOP (p);
//     return;
// }

void Push(int x) {
    ThreadInfo *ti = __VERIFIER_atomic_malloc_ThreadInfo();
    // Initialize threads
    ti->id = ++unique_id;
    ti->op = PUSH;
    ti->cell.pdata = x;

    if (TryPerformStackOp(ti) == FALSE) {
        LesOP(ti);
    }
}

int Pop() {
    ThreadInfo *ti = __VERIFIER_atomic_malloc_ThreadInfo();
    ti->id = ++unique_id;
    ti->op = POP;

    if (TryPerformStackOp(ti) == FALSE) {
        LesOP(ti);
    }
    int v = ti->cell.pdata;
    __VERIFIER_atomic_free_ThreadInfo(ti);
    return v;
}

#define PushArg0Max 2

int PushOpen[PushArg0Max];
int PushDone[PushArg0Max];

#define PopRetMax 3
int PopOpen;
int PopDone[PopRetMax];

void checkInvariant()
{
    assert (
        PopDone[0]  <= PushDone[0]  + PushOpen[0] &&
        PopDone[1]  <= PushDone[1]  + PushOpen[1]
    );
}

void __VERIFIER_atomic_atomicIncr_Push(int localPush1) {
    PushOpen[localPush1]++;
}

void __VERIFIER_atomic_atomicDecrIncr_Push(int localPush1) {
    PushOpen[localPush1]--;
    PushDone[localPush1]++;
    checkInvariant();
}

void __VERIFIER_atomic_atomicIncr_Pop() {
    PopOpen++;
}

void __VERIFIER_atomic_atomicDecrIncr_Pop(int localPop_ret) {
    PopOpen--;
    PopDone[localPop_ret]++;
    checkInvariant();
}


void* instrPush0(void* unused) {
    __VERIFIER_atomic_atomicIncr_Push(1);
    Push(1);
    __VERIFIER_atomic_atomicDecrIncr_Push(1);
    return NULL;
}

void* instrPush1(void* unused) {
    __VERIFIER_atomic_atomicIncr_Push(1);
    Push(1);
    __VERIFIER_atomic_atomicDecrIncr_Push(1);
    return NULL;
}

void* instrPush2(void* unused) {
    __VERIFIER_atomic_atomicIncr_Push(1);
    Push(1);
    __VERIFIER_atomic_atomicDecrIncr_Push(1);
    return NULL;
}




void* instrPop3(void* unused) {
    __VERIFIER_atomic_atomicIncr_Pop();
    int localPop_ret = Pop();
    __VERIFIER_atomic_atomicDecrIncr_Pop(localPop_ret);
    return NULL;
}

void* instrPop4(void* unused) {
    __VERIFIER_atomic_atomicIncr_Pop();
    int localPop_ret = Pop();
    __VERIFIER_atomic_atomicDecrIncr_Pop(localPop_ret);
    return NULL;
}

void* instrPop5(void* unused) {
    __VERIFIER_atomic_atomicIncr_Pop();
    int localPop_ret = Pop();
    __VERIFIER_atomic_atomicDecrIncr_Pop(localPop_ret);
    return NULL;
}

void* instrPop6(void* unused) {
    __VERIFIER_atomic_atomicIncr_Pop();
    int localPop_ret = Pop();
    __VERIFIER_atomic_atomicDecrIncr_Pop(localPop_ret);
    return NULL;
}


int main(void) {
    Init();

    pthread_t tid1, tid2, tid3, tid4, tid5, tid6, tid7;

    pthread_create(&tid1, NULL, &instrPush0, NULL);
    pthread_create(&tid2, NULL, &instrPush1, NULL);
    pthread_create(&tid3, NULL, &instrPush2, NULL);

    pthread_create(&tid4, NULL, &instrPop3, NULL);
    pthread_create(&tid5, NULL, &instrPop4, NULL);
    pthread_create(&tid6, NULL, &instrPop5, NULL);
    pthread_create(&tid7, NULL, &instrPop6, NULL);
}
