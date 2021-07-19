#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

int myglobal;
pthread_mutex_t mymutex = { { 0, 0, 0, 0, 0, { { 0, 0 } } } };
void *thread_function_mutex(void *arg)
{
    int i,j;
    for ( i=0; i<20; i++ )
    {
        pthread_mutex_lock(&mymutex);
        j=myglobal;
        j=j+1;
        printf("\nIn thread_function_mutex..\t");
        myglobal=j;
        pthread_mutex_unlock(&mymutex);
    }
    return ((void *)0);
}
int main(void)
{
    pthread_t mythread;
    int i;
    printf("\n\t\t---------------------------------------------------------------------------");
    printf("\n\t\t Centre for Development of Advanced Computing (C-DAC)");
    printf("\n\t\t Email : hpcfte@cdac.in");
    printf("\n\t\t---------------------------------------------------------------------------");
    myglobal = 0;
    if ( pthread_create( &mythread, ((void *)0), thread_function_mutex, ((void *)0)) )
    {
      exit(-1);
    }
    for ( i=0; i<20; i++)
    {
        pthread_mutex_lock(&mymutex);
        myglobal=myglobal+1;
        pthread_mutex_unlock(&mymutex);
    }
    if ( pthread_join ( mythread, ((void *)0) ) )
    {
      exit(-1);
    }
    __VERIFIER_assert(myglobal == 40);
    exit(0);
}
