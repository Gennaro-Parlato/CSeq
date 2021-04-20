#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <assert.h>

#define NUM_THREADS 3
/*
typedef struct SafeStackItem
{
    volatile int Value;
    int Next;
} SafeStackItem;

typedef struct SafeStack
{
    SafeStackItem* array;
    int head;
    int count;
} SafeStack;


/// Global
SafeStack stack;
*/
int stack_array_Value[NUM_THREADS];
int stack_array_Next[NUM_THREADS];
int stack_head;
int stack_count;




void __VERIFIER_atomic_store(int *obj, int v)
{
    *obj = v;
}

int __VERIFIER_atomic_load(int *obj)
{
    return *obj;
}

int __VERIFIER_atomic_exchange(int *obj, int v)
{
    int t = *obj;
    *obj = v;
    return t;
}

_Bool __VERIFIER_atomic_compare_and_exchange(int *obj, int *expected, int desired)
{
    if(*obj == *expected)
    {
        *obj = desired;
        return 1;
    }
    else
    {
        *expected = *obj;
        return 0;
    }
}

int __VERIFIER_atomic_fetch_add(int * obj, int v)
{
    int old = *obj;
    *obj = *obj + v;
    return old;
}

int __VERIFIER_atomic_fetch_sub(int * obj, int v)
{
    int old = *obj;
    *obj = *obj - v;
    return old;
}

void Init(int pushCount)
{
    int i;
    //stack.array = malloc(pushCount * sizeof(SafeStackItem));
    __VERIFIER_atomic_store(&stack_count, pushCount);
    __VERIFIER_atomic_store(&stack_head, 0);
    for (i = 0; i < pushCount - 1; i++)
    {
        __VERIFIER_atomic_store(&stack_array_Next[i], i + 1);
    }
    __VERIFIER_atomic_store(&stack_array_Next[pushCount - 1], -1);
}

void Destroy(void)
{
    free(stack_array);
}

int Pop(void)
{
    while (__VERIFIER_atomic_load(&stack_count) > 1)
    {
        int head1 = __VERIFIER_atomic_load(&stack_head);
        int next1 = __VERIFIER_atomic_exchange(&stack_array_Next[head1], -1);

        if (next1 >= 0)
        {
            int head2 = head1;
            if (__VERIFIER_atomic_compare_and_exchange(&stack_head, &head2, next1))
            {
                __VERIFIER_atomic_fetch_sub(&stack_count, 1);
                return head1;
            }
            else
            {
                __VERIFIER_atomic_exchange(&stack_array_Next[head1], next1);
            }
        }
    }

    return -1;
}

void Push(int index)
{
    int head1 = __VERIFIER_atomic_load(&stack_head);
    do
    {
        __VERIFIER_atomic_store(&stack_array_Next[index], head1);

    } while (!(__VERIFIER_atomic_compare_and_exchange(&stack_head, &head1, index)));
    __VERIFIER_atomic_fetch_add(&stack_count, 1);
}


void* thread(void* arg)
{
    size_t i;
    int idx = (int)(size_t)arg;
    for (i = 0; i < 2; i++)
    {
        int elem;
        for (;;)
        {
            elem = Pop();
            if (elem >= 0)
                break;
        }

        stack_array_Value[elem] = idx;
        assert(stack_array_Value[elem] == idx);

        Push(elem);
    }
    return NULL;
}

int main(void)
{
	pthread_t threads[NUM_THREADS];
    int i;
    Init(NUM_THREADS);
    for (i = 0; i < NUM_THREADS; ++i) {
        pthread_create(&threads[i], NULL, thread, (void*) i);
    }

    for (i = 0; i < NUM_THREADS; ++i) {
        pthread_join(threads[i], NULL);
    }

    return 0;
}

