#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <assert.h>

#define NUM_THREADS 3

typedef struct SafeStackItem
{
    volatile int Value;
    int Next;
} SafeStackItem;

typedef struct SafeStack
{
    SafeStackItem array[3];
    int head;
    int count;
} SafeStack;

pthread_t threads[NUM_THREADS];
pthread_t thread_p;  //added for DR detection test
SafeStack stack;

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
    // stack.array = malloc(pushCount * sizeof(SafeStackItem));
    __VERIFIER_atomic_store(&stack.count, pushCount);
    __VERIFIER_atomic_store(&stack.head, 0);
    for (i = 0; i < pushCount - 1; i++)
    {
        __VERIFIER_atomic_store(&stack.array[i].Next, i + 1);
    }
    __VERIFIER_atomic_store(&stack.array[pushCount - 1].Next, -1);
}

// void Destroy(void)
// {
//     free(stack.array);
// }

int Pop(void)
{
    while (__VERIFIER_atomic_load(&stack.count) > 1)
    {
        int head1 = __VERIFIER_atomic_load(&stack.head);
        int next1 = __VERIFIER_atomic_exchange(&stack.array[head1].Next, -1);

        if (next1 >= 0)
        {
            int head2 = head1;
            if (__VERIFIER_atomic_compare_and_exchange(&stack.head, &head2, next1))
            {
                __VERIFIER_atomic_fetch_sub(&stack.count, 1);
                return head1;
            }
            else
            {
                __VERIFIER_atomic_exchange(&stack.array[head1].Next, next1);
            }
        }
    }

    return -1;
}

void Push(int index)
{
    int head1 = __VERIFIER_atomic_load(&stack.head);
    do
    {
        __VERIFIER_atomic_store(&stack.array[index].Next, head1);

    } while (!(__VERIFIER_atomic_compare_and_exchange(&stack.head, &head1, index)));
    __VERIFIER_atomic_fetch_add(&stack.count, 1);
}


int fake;   //added for DR detection test

void* thread(void* arg)
{
    size_t i;
    int idx = (int)(size_t)arg;
    
    //int l_fake;  //added for DR detection test

    for (i = 0; i < 2; i++)
    {
        int elem;
        for (;;)
        {
            elem = Pop();
            if (elem >= 0)
                break;
        }

//        stack.array[elem].Value = idx;
//        assert(stack.array[elem].Value == idx);
//      the above is modified in the following three lines for DR detection test        
	__VERIFIER_atomic_store(&stack.array[elem].Value, idx);
        if(stack.array[elem].Value != idx)
        	fake=1;
//        else
//        	l_fake = fake;

        Push(elem);
    }
    return NULL;
}

// following added for DR detection test
void* fake_thread(void* arg)
{
    int l_fake;
    l_fake = fake;
    return NULL;
}

int main(void)
{
    int i;
    Init(NUM_THREADS);
    for (i = 0; i < NUM_THREADS; ++i) {
        pthread_create(&threads[i], NULL, thread, (void*) i);
    }
    pthread_create(&thread_p, NULL, fake_thread, (void*) i);    //added for DR detection test

    for (i = 0; i < NUM_THREADS; ++i) {
        pthread_join(threads[i], NULL);
    }
    pthread_join(thread_p, NULL);    //added for DR detection test

    return 0;
}

