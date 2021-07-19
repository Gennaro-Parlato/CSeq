#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

void *compute_pi (void *);
double intervalWidth, intervalMidPoint, area = 0.0;
int numberOfIntervals, interval, iCount,iteration, num_threads;
double distance=0.5,four=4.0;
pthread_mutex_t area_mutex={ { 0, 0, 0, 0, 0, { { 0, 0 } } } };
pthread_mutex_t pi_mutex={ { 0, 0, 0, 0, 0, { { 0, 0 } } } };
void myPartOfCalc(int myID)
{
    int myInterval;
    double myIntervalMidPoint, myArea = 0.0, result;
    for (myInterval = myID + 1; myInterval <= numberOfIntervals; myInterval += numberOfIntervals)
    {
        myIntervalMidPoint = ((double) myInterval - distance) * intervalWidth;
        myArea += (four / (1.0 + myIntervalMidPoint * myIntervalMidPoint));
    }
    result = myArea * intervalWidth;
    pthread_mutex_lock(&area_mutex);
    area += result;
    pthread_mutex_unlock(&area_mutex);
}
int main(int argc, char *argv[])
{
    int i,Iteration,ret_count;
    pthread_t p_threads[8];
    pthread_t * threads;
    pthread_attr_t pta;
    pthread_attr_t attr;
    double computed_pi,diff;
    FILE *fp;
    int CLASS_SIZE,THREADS;
    char * CLASS;
    ret_count=pthread_mutex_init(&area_mutex,((void *)0));
    if (ret_count)
    {
      exit(-1);
     }
    printf("\n\t\t---------------------------------------------------------------------------");
    printf("\n\t\t Centre for Development of Advanced Computing (C-DAC)");
    printf("\n\t\t Email : hpcfte@cdac.in");
    printf("\n\t\t---------------------------------------------------------------------------");
    printf("\n\t\t Objective : PI Computations");
    printf("\n\t\t Computation of PI using Numerical Integration Method ");
    printf("\n\t\t..........................................................................\n");
    numberOfIntervals = __VERIFIER_nondet_int();
    if(numberOfIntervals > 8) {
        printf("\n Number Of Intervals should be less than or equal to 8.Aborting\n");
        return 0;
    }
    num_threads = numberOfIntervals ;
    printf("\n\t\t Input Parameters :");
    printf("\n\t\t Number Of Intervals : %d ",numberOfIntervals);
    ret_count=pthread_attr_init(&pta);
    if(ret_count)
    {
      exit(-1);
    }
    assume_abort_if_not(numberOfIntervals>0);
    /*if (numberOfIntervals == 0)
    {
        printf("\nNumber of Intervals are assumed to be 8");
        numberOfIntervals = 8;
	num_threads = numberOfIntervals ;
    }*/
    threads = (pthread_t *) malloc(sizeof(pthread_t) * numberOfIntervals);
    intervalWidth = 1.0 / (double) numberOfIntervals;
    for (iCount = 0; iCount < num_threads; iCount++)
    {
        ret_count=pthread_create(&threads[iCount], &pta, (void *(*) (void *)) myPartOfCalc, (void *) iCount);
        if (ret_count)
        {
   exit(-1);
        }
     }
    for (iCount = 0; iCount < numberOfIntervals; iCount++)
    {
        ret_count=pthread_join(threads[iCount], ((void *)0));
        if (ret_count)
        {
   exit(-1);
        }
    }
    ret_count=pthread_attr_destroy(&pta);
    if (ret_count)
    {
      exit(-1);
    }
    printf("\n\t\t Computation Of PI value Using Numerical Integration Method ......Done\n");
    printf("\n\t\t Computed Value Of PI        :  %lf", area);
    __VERIFIER_assert(area - 3.14159265388372456789123456789456 < 1.0E-5 || 3.14159265388372456789123456789456 - area < 1.0E-5);
    printf("\n\t\t..........................................................................\n");
    free(threads);
    return 0;
}
