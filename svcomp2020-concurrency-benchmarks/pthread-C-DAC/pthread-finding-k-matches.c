#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
double a[1000];
int count ,num_threads,iterations;
double search_no ;
pthread_mutex_t count_mutex;
void *find_entries(void *tid)
{
    int i, start, *mytid, end;
    int local_count =0;
    mytid = (int *) tid;
    start = (*mytid * iterations);
    end = start + iterations;
    printf ("Thread %d doing iterations %d to %d\n",*mytid,start,end-1);
    for (i=start; i < end ; i++) {
        if ( a[i] == search_no ) {
            local_count ++;
        }
    }
    pthread_mutex_lock (&count_mutex);
    count = count + local_count;
    pthread_mutex_unlock (&count_mutex);
    return 0;
}
int main(int argc, char *argv[]) {
    int i,start,ret_count;
    int *tids;
    pthread_t * threads;
    pthread_attr_t attr;
    printf("\n\t\t---------------------------------------------------------------------------");
    printf("\n\t\t Centre for Development of Advanced Computing (C-DAC):  February-2008");
    printf("\n\t\t Email : hpcfte@cdac.in");
    printf("\n\t\t---------------------------------------------------------------------------");
    printf("\n\t\t Objective : Finding k matches in the given Array");
    printf("\n\t\t..........................................................................\n");
    for (i=0;i<1000;i++){
        a[i] = (i %10)+1.0;
    }
    search_no = __VERIFIER_nondet_int();
    num_threads = 2;
    if (num_threads > 8) {
        printf ("Number of thread should be less than or equal to 8\n");
        return 0;
    }
    iterations = 1000/num_threads;
    threads = (pthread_t *) malloc(sizeof(pthread_t) * num_threads);
    tids = (int *) malloc(sizeof(int) * num_threads);
    ret_count = pthread_mutex_init(&count_mutex, ((void *)0));
    if(ret_count)
    {
      exit(-1);
    }
    ret_count=pthread_attr_init(&attr);
    if(ret_count)
    {
      exit(-1);
    }
    ret_count = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
    if(ret_count)
    {
      exit(-1);
    }
    for (i=0; i<num_threads; i++) {
        tids[i] = i;
        ret_count = pthread_create(&threads[i], &attr,find_entries, (void *) &tids[i]);
        if(ret_count)
        {
   exit(-1);
        }
    }
    for (i=0; i<num_threads; i++) {
        ret_count = pthread_join(threads[i], ((void *)0));
        if(ret_count)
        {
   exit(-1);
        }
    }
    int temp = 0;
    for (i=0;i<1000;i++){
      if (a[i] == search_no)
 temp++;
    }
    __VERIFIER_assert(count == temp);
    printf("Number of search element found in list Count= %d\n",count);
    ret_count = pthread_attr_destroy(&attr);
    if(ret_count)
    {
      exit(-1);
    }
    ret_count = pthread_mutex_destroy(&count_mutex);
    if(ret_count)
    {
      exit(-1);
    }
    free(threads);
    free(tids);
    return 0;
}
