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
byte inCS;
chan ch0 = [1] of {bool};
chan ch1 = [1] of {bool};

#define MY_STATUS status[_pid-1]
#define MY_NEXT next[_pid-1]

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
	byte tmpStatus;
	SWAP(MY_STATUS, prevStatus, WAIT);

	if
		:: prevStatus == ABORTED -> goto START_SPIN;
	        :: d_step {prevStatus == READY_TO_USE -> skip;};
            	:: d_step {prevStatus == WAIT -> skip;};
	        :: prevStatus == UNLOCKED ->
                /*while(I->status != READY_TO_USE); No unbounded wait*/
/******************* OLD *************
		if 
			:: MY_STATUS == READY_TO_USE -> goto USE_QNODE;	
			:: d_step {else -> CAS(MY_STATUS, WAIT, UNLOCKED, tmpStatus);};
		fi

		if
			:: d_step {tmpStatus != READY_TO_USE -> abortedNode = _pid-1;}; goto DONE_ACQUIRE;
			:: d_step {else -> skip; };
		fi
********************** NEW *************/
		CAS(MY_STATUS, WAIT, UNLOCKED, tmpStatus);
		if
			:: d_step {tmpStatus != READY_TO_USE -> abortedNode = _pid-1;}; goto DONE_ACQUIRE;
			:: d_step {else -> skip; };
		fi
/*************** END **********/



		:: d_step {else -> assert (false);};
	fi

    USE_QNODE:
        MY_NEXT = NONE;
        SWAP(L,pred, _pid-1);

atomic{
        if
        :: (_pid -1 ==  0) && (numRounds == 3) -> run Work(); ch0 ? true;
        :: (_pid -1 ==  1) && (numRounds == 3) -> run Work(); ch1 ? true;
        :: (_pid -1 ==  2) && (numRounds == 3) -> ch1 ! true; ch0 ! true; 
	:: else -> skip;
        fi
};
        if

		:: d_step {pred != NONE -> 
            		/* Avoid unbounded wait for I->next */
			SWAP(next[pred], predStat, _pid-1);};
			if
			    :: d_step {predStat == CANT_WAIT_FOR_NEXT ->
                		status[pred]= READY_TO_USE;};
				goto SET_AND_FINISH_ACQUIRE;
            		    :: else -> skip
			fi
        	
	START_SPIN:
/******* OLD VERSION ****
	 	    if
			:: MY_STATUS == UNLOCKED -> abortedNode = NONE; goto DONE_ACQUIRE;
			:: else -> skip;
		    fi

        	    SWAP(MY_STATUS, prevStatus , ABORTED);
	            if
			:: prevStatus == UNLOCKED -> goto SET_AND_FINISH_ACQUIRE;
			:: else -> skip;
		    fi

	      		abortedNode = _pid-1; 
			goto DONE_ACQUIRE;
*********** IMPROVED VERSION ****/
                    if
                        :: d_step {MY_STATUS == UNLOCKED -> abortedNode = NONE;}; 
                        :: else -> 
	                    SWAP(MY_STATUS, prevStatus , ABORTED);
        	            if
                	        :: d_step {prevStatus == UNLOCKED -> MY_STATUS = UNLOCKED; abortedNode = NONE; };
                        	:: d_step {else -> abortedNode = _pid-1;}
                    	    fi
                    fi

                        goto DONE_ACQUIRE;
/******** END IMPROVED VERSION *****/

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
		:: d_step { abortedNode==NONE -> 
				acquired=true; 
				inCS++;
			};
  			d_step{
				assert(inCS == 1); 
				inCS--;
			};
		:: d_step {else -> acquired=false;};
	fi
}


inline DealWithRestOfLevel1(me, prev){
	byte tmpStatus;
	byte retOld;
	byte tmpSucc;
	do
	  ::d_step { else ->
	    BOOL_CAS(L, me, NONE, retOld);};		
            if 
		:: d_step {retOld == false -> 
                	BOOL_CAS(next[me], NONE, CANT_WAIT_FOR_NEXT, retOld); };
	                if 
				:: d_step { retOld == false ->
					SWAP(status[next[me]], tmpStatus, UNLOCKED);};
					if
						::  d_step { tmpStatus == ABORTED ->
							tmpSucc = next[me];
								next[me] = prev;
								prev = me;
								me = 	tmpSucc;
							};
						::  d_step {else -> status[me] = READY_TO_USE;}; break;

					fi	
                		:: else -> break;
			fi
		::  d_step {else -> status[me] = READY_TO_USE;}; break;
	   fi
        od
}

inline Release()
{

        byte prev = NONE;
	byte me = _pid-1;
	byte succ;
	byte pprev;
	byte prevStatus;

	do
	    :: else ->
            if
		:: VALID_SUCC(me) -> 
			SWAP(status[next[me]], prevStatus , UNLOCKED);
                	if
		    		::  d_step {prevStatus == ABORTED ->
					succ = next[me];
	        	            		next[me] = prev;
						prev = me;
                    	    			me = succ; 
					}
               	    		::  d_step {else -> status[me] = READY_TO_USE;};  goto CLEANUP;
                	fi 
                :: else -> 
               		DealWithRestOfLevel1(me, prev);
                	goto CLEANUP;
	   fi
	od


CLEANUP:
    do
	:: d_step{prev != NONE ->
		pprev = next[prev];};
		d_step{
	        	status[prev] = READY_TO_USE;
        		prev = pprev;
		};
	:: else -> break;
    od
}


proctype  Work() 
{ 
        byte numRounds = 3;
	bool acquired;
        do
        :: numRounds > 0 -> 
		AcquireWrapper(acquired); 
		if
			:: acquired -> Release();
			:: else -> skip;
		fi
		numRounds--;
        :: else -> break;
        od;	
}
 
init {
        /* init */
                        d_step{
                                inCS = 0;
                                L = NONE;
                                byte i;
                                for(i: 0..(MAX_THREADS-1)){
                                        next[i] = NONE;
                                        status[i] = WAIT;
                                }
                        }

	run Work();
} 

