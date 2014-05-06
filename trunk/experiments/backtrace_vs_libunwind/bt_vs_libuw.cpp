     #include <execinfo.h>
     #include <stdio.h>
     #include <stdlib.h>
     #include <stdint.h>
#include<iostream>
#include <sstream> 
#include<sys/time.h>
#define UNW_LOCAL_ONLY
#include <libunwind.h>
    void GetContextHash(){

            unw_cursor_t cursor; unw_context_t uc;
            unw_word_t ip, sp;

            unw_getcontext(&uc);
            unw_init_local(&cursor, &uc);
            uint64_t hash = 0;
            while (unw_step(&cursor) > 0) {
                    unw_get_reg(&cursor, UNW_REG_IP, &ip);
		// std::stringstream command;
                //command << "addr2line -C -f -e " << " ./a.out " << " " << std::hex << ip;
		//	system(command.str().c_str());
                    hash += ip;
            }
    }

using namespace std;
#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)


     
     void *array[1000];
     /* Obtain a backtrace and print it to stdout. */

     void
     print_trace_orig (void)
     {
       void *array[10];
       size_t size;
       char **strings;
       size_t i;

       size = backtrace (array, 10);
       strings = backtrace_symbols (array, size);

       printf ("Obtained %zd stack frames.\n", size);

       for (i = 0; i < size; i++)
          printf ("%s\n", strings[i]);

       free (strings);
     }

     void
     print_trace (void)
     {
       size_t size;
       size_t i;
     
       size = backtrace (array, 1000);
       uint64_t hash = 0; 
       for (i = 0; i < size; i++)
          hash += (uint64_t) array[i];
 
     }
     
void
     dummy_function (int i);
     void dummy_function2(int i){
		return dummy_function(i+1);
     }
 
     /* A dummy function to make the backtrace more interesting. */
     void
     dummy_function (int i)
     {
	if(i == 100)
       		print_trace ();
	else
		dummy_function2(i);	
     }

     void dummy_function_luw (int i);

     void dummy_function2_luw(int i){
                return dummy_function_luw(i+1);
     }

     void
     dummy_function_luw (int i)
     {
        if(i == 100)
                GetContextHash();
        else
                dummy_function2_luw(i);
     }

     
     int
     main (void)
     {

        struct timeval start;
        struct timeval end;
        uint64_t t1;

	gettimeofday(&start, 0);
	int iter = 0xffff;
	//int iter = 2;
	for(int i = 0 ; i < iter; i++)
       		dummy_function (0);
	gettimeofday(&end,0);

	t1 = TIME_SPENT(start,end);
	cout<<"\n T1 = "<< t1;

        gettimeofday(&start, 0);
        for(int i = 0 ; i < iter; i++)
                dummy_function_luw (0);
        gettimeofday(&end,0);

        t1 = TIME_SPENT(start,end);
        cout<<"\n T1 = "<< t1;
        cout<<"\n";


       return 0;

     }
