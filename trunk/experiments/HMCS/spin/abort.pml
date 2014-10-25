#define MAX_THREADS (3)
#define NONE (255)


#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (254)
#define ABORTED (253)
#define READY_TO_USE (252)
#define ACQUIRE_PARENT (251)
#define CANT_WAIT_FOR_NEXT (254)

#define COHORT_START (0x1)
#define ALARM_TIME (3 * 60)

#define VALID_SUCC(id) (next[id] > 0  && next[id] < MAX_THREADS)


byte next[MAX_THREADS];
byte status[MAX_THREADS];
byte L;
bool initialized;
byte inCS;


#define MY_STATUS status[_pid]
#define MY_NEXT next[_pid]

#define SWAP(loc, var, val) d_step{var=loc; loc=val;}


#define CAS(loc, oldVal, newVal, retOld) d_step{ \
						  if \
							:: loc == oldVal -> retOld = loc; loc = newVal;\
							:: else -> retOld = loc;\
						  fi\
						}

#define BOOL_CAS(loc, oldVal, newVal, retOld) d_step{ \
						  if \
							:: loc == oldVal -> retOld = true; loc = newVal;\
							:: else -> retOld = false;\
						  fi \
						}



inline Acquire(abortedNode)
{
        byte prevStatus;
        byte pred;
	byte predStat;
	SWAP(MY_STATUS, prevStatus, WAIT);

	if
		:: prevStatus == ABORTED -> goto START_SPIN;
	        :: prevStatus == READY_TO_USE -> skip;
            	:: prevStatus == WAIT -> skip;
	        :: prevStatus == UNLOCKED ->
                /*while(I->status != READY_TO_USE); No unbounded wait*/
		if 
			:: MY_STATUS == READY_TO_USE -> goto USE_QNODE;	
			:: else -> skip;
		fi

		byte tmpStatus;
		CAS(MY_STATUS, WAIT, UNLOCKED, tmpStatus);

		if
			:: tmpStatus != READY_TO_USE -> abortedNode = _pid; goto DONE_ACQUIRE;
			:: else -> skip; 
		fi

		:: else -> assert (false);
	fi

    USE_QNODE:
        MY_NEXT = NONE;
        SWAP(L,pred, _pid);

        if

		:: pred != NONE -> 
            		/* Avoid unbounded wait for I->next */
			SWAP(next[pred], predStat, _pid);
			if
			    :: predStat == CANT_WAIT_FOR_NEXT ->
                		status[pred]= READY_TO_USE;
				goto SET_AND_FINISH_ACQUIRE;
            		    :: else -> skip
			fi
        	
	START_SPIN:

	 	    if
			:: MY_STATUS == UNLOCKED -> abortedNode = NONE; goto DONE_ACQUIRE;
			:: else -> skip;
		    fi

        	    SWAP(MY_STATUS, prevStatus , ABORTED);
	            if
			:: prevStatus == UNLOCKED -> goto SET_AND_FINISH_ACQUIRE;
			:: else -> skip;
		    fi

	      		abortedNode = _pid; 
			goto DONE_ACQUIRE;

		:: else -> goto SET_AND_FINISH_ACQUIRE;
	fi


SET_AND_FINISH_ACQUIRE: skip;
d_step {
	MY_STATUS = UNLOCKED;
        abortedNode = NONE; 
}
DONE_ACQUIRE: skip;
}

inline AcquireWrapper(acquired)
{
        byte abortedNode;
	Acquire(abortedNode);
        if
		:: abortedNode==NONE -> 
			d_step{
				acquired=true; 
				inCS++;
			} 
			assert(inCS == 1); 
			inCS--;
		:: else -> acquired=false;
	fi
}


inline DealWithRestOfLevel1(me, prev){

	do
	  :: else ->
	    byte retOld;
	    BOOL_CAS(L, me, NONE, retOld);		

            if 
		:: retOld == false -> 
                	BOOL_CAS(next[me], NONE, CANT_WAIT_FOR_NEXT, retOld); 
	                if 
				:: retOld == false ->
	                   		byte tmpStatus;
					SWAP(status[next[me]], tmpStatus, UNLOCKED);
					if
						:: tmpStatus == ABORTED ->
							byte tmpSucc = next[me];
							d_step{
								next[me] = prev;
								prev = me;
								me = 	tmpSucc;
							}
						:: else -> status[me] = READY_TO_USE; break;

					fi	
                		:: else -> break;
			fi
		:: else -> status[me] = READY_TO_USE; break;
	   fi
        od
}

inline Release()
{
        byte prev = NONE;
	byte me = _pid;
	do
	    :: else ->
            if
		:: VALID_SUCC(me) -> 
	        	byte prevStatus;
			SWAP(status[next[me]], prevStatus , UNLOCKED);
                	if
		    		:: prevStatus == ABORTED ->
	                    		byte succ;
					succ = next[me];
                	    		d_step { 
	        	            		next[me] = prev;
						prev = me;
                    	    			me = succ; 
					}
               	    		:: else -> MY_STATUS = READY_TO_USE; goto CLEANUP;
                	fi 
                :: else -> 
               		DealWithRestOfLevel1(me, prev);
                	goto CLEANUP;
	   fi
	od


CLEANUP:
    do
	:: prev != NONE ->
	        byte pprev;
		pprev = next[prev]; 
		d_step{
	        	status[prev] = READY_TO_USE;
        		prev = pprev;
		}
	:: else -> break;
    od
}


active [MAX_THREADS] proctype  Work() 
{ 
        byte j = 3;
	bool acquired;

	/* init */
	if
		::_pid == 0 ->
			d_step{
				inCS = 0;
				L = NONE;
				byte i;
				for(i: 0..(MAX_THREADS-1)){
					next[i] = NONE;
					status[i] = WAIT;
				} 
				initialized = true;
			}
		:: else -> initialized == true;
	fi
	
        do
        :: j > 0 -> 
		AcquireWrapper(acquired); 
		if
			:: acquired -> Release();
			:: else -> skip;
		fi
		j--;
        :: else -> break;
        od;	
}
 
/*
init {
atomic {
	run Two();
	run Two();
};
} 
*/

