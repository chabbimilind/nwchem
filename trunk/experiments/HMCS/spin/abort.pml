#define MAX_L1_THREADS (3)
#define MAX_L2_THREADS (3)
#define MAX_L3_THREADS (3)

#define THRESHOLD (3)

#define MAX_THREADS (3)

#define NONE (255)


#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (254)
#define ABORTED (253)
#define READY_TO_USE (252)
#define ACQUIRE_PARENT (251)
#define CANT_WAIT_FOR_NEXT (254)

#define COHORT_START (1)
#define ALARM_TIME (3 * 60)


bool initialized;
byte inCS;


byte nextL1[MAX_L1_THREADS];
byte statusL1[MAX_L1_THREADS];
byte L1;
#define MY_L1_STATUS statusL1[myL1Id]
#define MY_L1_NEXT nextL1[myL1Id]
#define L1_STATUS(id) statusL1[id]
#define L1_NEXT(id) nextL1[id]
#define HAS_VALID_L1_SUCC(id) nextL1[id] < CANT_WAIT_FOR_NEXT


byte nextL2[MAX_L2_THREADS];
byte statusL2[MAX_L2_THREADS];
byte L2;
#define MY_L2_STATUS statusL2[myL2Id]
#define MY_L2_NEXT nextL2[myL2Id]
#define L2_STATUS(id) statusL2[id]
#define L2_NEXT(id) nextL2[id]
#define HAS_VALID_L2_SUCC(id) nextL2[id] < CANT_WAIT_FOR_NEXT


byte nextL3[MAX_L3_THREADS];
byte statusL3[MAX_L3_THREADS];
byte L3;
#define MY_L3_STATUS statusL3[myL3Id]
#define MY_L3_NEXT nextL3[myL3Id]
#define L3_STATUS(id) statusL3[id]
#define L3_NEXT(id) nextL3[id]
#define HAS_VALID_L3_SUCC(id) nextL3[id] < CANT_WAIT_FOR_NEXT


#define MY_L1_NODE_ID(id) (id <= 2 -> id : 0 /* just to eliminate error */)

#define MY_L2_NODE_ID(id) (id <= 2 -> 0 : (id <= 4 -> id - 2 : 0 /* just to eliminate error */) )

#define MY_L3_NODE_ID(id) (id <= 4 -> 0 : id - 4)



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


inline AcquireL3(abortedLevel)
{
    byte myL3Id = MY_L3_NODE_ID(_pid);
    byte prevStatus_Acq_L3;
    byte pred_Acq_L3;
    byte predStat_Acq_L3;
    SWAP(MY_L3_STATUS, prevStatus_Acq_L3, WAIT);

    if
        :: prevStatus_Acq_L3 == ABORTED -> goto START_SPIN_L3;
        :: prevStatus_Acq_L3 == READY_TO_USE -> skip;
        :: prevStatus_Acq_L3 == WAIT -> skip;
        :: prevStatus_Acq_L3 == UNLOCKED ->
                /*while(I->status != READY_TO_USE); No unbounded wait*/
                /* Not needed in spin 
        if 
            :: MY_L3_STATUS == READY_TO_USE -> goto USE_QNODE_L3;    
            :: else -> skip;
        fi */

        byte tmpStatus;
        CAS(MY_L3_STATUS, WAIT, UNLOCKED, tmpStatus);

        if
            :: tmpStatus != READY_TO_USE -> atomic{ abortedLevel = 2 /* L3 */; goto DONE_ACQUIRE_L3;}
            :: else -> skip; 
        fi

        :: else -> assert (false);
    fi

    USE_QNODE_L3:
        MY_L3_NEXT = NONE;
        SWAP(L3,pred_Acq_L3, myL3Id);

        if

        :: pred_Acq_L3 != NONE -> 
                    /* Avoid unbounded wait for I->next */
            SWAP(L3_NEXT(pred_Acq_L3), predStat_Acq_L3, _pid);
            if
                :: predStat_Acq_L3 == CANT_WAIT_FOR_NEXT ->
                        atomic{ L3_STATUS(pred_Acq_L3)= READY_TO_USE;
                        goto SET_AND_FINISH_ACQUIRE_L3;}
                :: else -> skip
            fi
            
    START_SPIN_L3: skip;
 
                /* Not needed in spin 
            if
                :: MY_L3_STATUS == UNLOCKED -> atomic { abortedLevel = NONE; goto DONE_ACQUIRE_L3;}
                :: else -> skip;
            fi  */

            SWAP(MY_L3_STATUS, prevStatus_Acq_L3 , ABORTED);
            if
                :: prevStatus_Acq_L3 == UNLOCKED -> goto SET_AND_FINISH_ACQUIRE_L3;
                :: else -> skip;
            fi

            atomic { abortedLevel = 2 /* L3 */; goto DONE_ACQUIRE_L3;}

        :: else -> goto SET_AND_FINISH_ACQUIRE_L3;
    fi


SET_AND_FINISH_ACQUIRE_L3: skip;
d_step {
    MY_L3_STATUS = UNLOCKED;
    abortedLevel = NONE;
}
DONE_ACQUIRE_L3: skip;
}


inline AcquireL2(abortedLevel)
{
    byte myL2Id = MY_L2_NODE_ID(_pid);
    byte prevStatus_Acq_L2;
    byte pred_Acq_L2;
    byte predStat_Acq_L2;
    byte tmpStatus_Acq_L2;
    SWAP(MY_L2_STATUS, prevStatus_Acq_L2, WAIT);

    if
        :: prevStatus_Acq_L2 == ABORTED -> goto START_SPIN_L2;
        :: prevStatus_Acq_L2 == COHORT_START -> goto GOT_LOCK_L2;
        :: prevStatus_Acq_L2 == WAIT -> skip;
        :: prevStatus_Acq_L2 == READY_TO_USE -> skip;
        :: else ->
            /*while(I->status != READY_TO_USE); No unbounded wait*/
            CAS(MY_L2_STATUS, WAIT, UNLOCKED, tmpStatus_Acq_L2);
            if
                :: tmpStatus_Acq_L2 != READY_TO_USE -> atomic{ abortedLevel = 1 /* L2 */; goto DONE_ACQUIRE_L2;}
                :: else -> skip;
            fi
    fi

    USE_QNODE_L2:

    MY_L2_NEXT = NONE;
    SWAP(L2,pred_Acq_L2, myL2Id);

    if
        :: pred_Acq_L2 == NONE ->
    GOT_LOCK_L2:
            MY_L2_STATUS = COHORT_START;
            AcquireL3(abortedLevel);
            goto DONE_ACQUIRE_L2;

        :: else ->
            /* Avoid unbounded wait for I->next */
            SWAP(L2_NEXT(pred_Acq_L2), predStat_Acq_L2, myL2Id);
            if
                :: predStat_Acq_L2 == CANT_WAIT_FOR_NEXT ->
                    statusL2[pred_Acq_L2]= READY_TO_USE;
                    MY_L2_STATUS = COHORT_START;
                    AcquireL3(abortedLevel);
                    goto DONE_ACQUIRE_L2;
                :: else -> skip
            fi

        START_SPIN_L2: skip;

            SWAP(MY_L2_STATUS, prevStatus_Acq_L2 , ABORTED);
            if
                :: prevStatus_Acq_L2 < ACQUIRE_PARENT -> MY_L2_STATUS  = prevStatus_Acq_L2 ; goto SET_AND_FINISH_ACQUIRE_L2;
                :: prevStatus_Acq_L2 == ACQUIRE_PARENT -> MY_L2_STATUS  = COHORT_START ;  AcquireL3(abortedLevel); goto DONE_ACQUIRE_L2;
                :: else -> atomic { abortedLevel = 1 /* L2 */; goto DONE_ACQUIRE_L2;};
            fi
    fi


    SET_AND_FINISH_ACQUIRE_L2: skip;
    d_step {
        abortedLevel = NONE;
    }
    DONE_ACQUIRE_L2: skip;
}



inline AcquireL1(abortedLevel)
{
    byte myL1Id = MY_L1_NODE_ID(_pid);
    byte prevStatus_Acq_L1;
    byte pred_Acq_L1;
    byte predStat_Acq_L1;
    byte tmpStatus_Acq_L1;
    SWAP(MY_L1_STATUS, prevStatus_Acq_L1, WAIT);

    if
        :: prevStatus_Acq_L1 == ABORTED -> goto START_SPIN_L1;
        :: prevStatus_Acq_L1 == COHORT_START -> goto  GOT_LOCK_L1;
        :: prevStatus_Acq_L1 == WAIT -> skip;
        :: prevStatus_Acq_L1 == READY_TO_USE -> skip;
        :: else ->
                /*while(I->status != READY_TO_USE); No unbounded wait*/

            CAS(MY_L1_STATUS, WAIT, UNLOCKED, tmpStatus_Acq_L1);

            if
                :: tmpStatus_Acq_L1 != READY_TO_USE -> atomic{ abortedLevel = 0 /* L1 */; goto DONE_ACQUIRE_L1;}
                :: else -> skip;
            fi
    fi

    USE_QNODE_L1:

    MY_L1_NEXT = NONE;
    SWAP(L1,pred_Acq_L1, myL1Id);

    if
        :: pred_Acq_L1 == NONE ->
GOT_LOCK_L1:        
            MY_L1_STATUS = COHORT_START;
            AcquireL2(abortedLevel);
            goto DONE_ACQUIRE_L1;

        :: else ->
                /* Avoid unbounded wait for I->next */
            SWAP(L1_NEXT(pred_Acq_L1), predStat_Acq_L1, myL1Id);
            if
                :: predStat_Acq_L1 == CANT_WAIT_FOR_NEXT ->
                    statusL1[pred_Acq_L1]= READY_TO_USE;
                    MY_L1_STATUS = COHORT_START;
                    AcquireL2(abortedLevel);
                    goto DONE_ACQUIRE_L1;
                :: else -> skip
            fi
        
START_SPIN_L1: skip;

            SWAP(MY_L1_STATUS, prevStatus_Acq_L1 , ABORTED);
            if
                :: prevStatus_Acq_L1 < ACQUIRE_PARENT -> MY_L1_STATUS  = prevStatus_Acq_L1 ; goto SET_AND_FINISH_ACQUIRE_L1;
                :: prevStatus_Acq_L1 == ACQUIRE_PARENT -> MY_L1_STATUS  = COHORT_START ;  AcquireL2(abortedLevel); goto DONE_ACQUIRE_L1;
                :: else -> atomic { abortedLevel = 0 /* L1 */; goto DONE_ACQUIRE_L1;};
            fi
    fi


    SET_AND_FINISH_ACQUIRE_L1: skip;
    d_step {
            abortedLevel = NONE; 
    }
    DONE_ACQUIRE_L1: skip;
}



inline DealWithRestOfL2(me /* destroyed */, prev /* destroyed and used in caller */){
    byte retOld_DWR_L2;
    byte tmpStatus_DWR_L2;
    byte tmpSucc_DWR_L2;
    do
      :: else ->
            BOOL_CAS(L2, me, NONE, retOld_DWR_L2);

            if 
                :: retOld_DWR_L2 == false ->

                    if
                        :: L2_STATUS(me) == COHORT_START -> L2_STATUS(me) = ACQUIRE_PARENT;
                        :: else -> skip;
                    fi

                    BOOL_CAS(L2_NEXT(me), NONE, CANT_WAIT_FOR_NEXT, retOld_DWR_L2); 
                    if 
                        :: retOld_DWR_L2 == false ->
                            SWAP(L2_STATUS(L2_NEXT(me)), tmpStatus_DWR_L2, ACQUIRE_PARENT);
                            if
                                :: tmpStatus_DWR_L2 == ABORTED ->
                                    tmpSucc_DWR_L2 = L2_NEXT(me);
                                    d_step{
                                        L2_NEXT(me) = prev;
                                        prev = me;
                                        me =     tmpSucc_DWR_L2;
                                    }
                                :: else -> atomic {L2_STATUS(me) = READY_TO_USE; break;}
                            fi
                :: else -> break;
            fi
        :: else -> atomic {L2_STATUS(me) = READY_TO_USE; break;}
       fi
    od
}


inline DealWithRestOfL1(me /* destroyed */, prev /* destroyed and used in caller */){
    byte retOld_DWR_L1;
    byte tmpStatus_DWR_L1;
    byte tmpSucc_DWR_L1;
    do
      :: else ->
            BOOL_CAS(L1, me, NONE, retOld_DWR_L1);

            if 
                :: retOld_DWR_L1 == false ->

                    if
                        :: L1_STATUS(me) == COHORT_START -> L1_STATUS(me) = ACQUIRE_PARENT;
                        :: else -> skip;
                    fi

                    BOOL_CAS(L1_NEXT(me), NONE, CANT_WAIT_FOR_NEXT, retOld_DWR_L1); 
                    if 
                        :: retOld_DWR_L1 == false ->
                            SWAP(L1_STATUS(L1_NEXT(me)), tmpStatus_DWR_L1, ACQUIRE_PARENT);
                            if
                                :: tmpStatus_DWR_L1 == ABORTED ->
                                    tmpSucc_DWR_L1 = L1_NEXT(me);
                                    d_step{
                                        L1_NEXT(me) = prev;
                                        prev = me;
                                        me =     tmpSucc_DWR_L1;
                                    }
                                :: else -> atomic {L1_STATUS(me) = READY_TO_USE; break;}
                            fi
                :: else -> break;
            fi
        :: else -> atomic {L1_STATUS(me) = READY_TO_USE; break;}
       fi
    od
}

inline CleanupReverseChainL1(node, pprev_CRC_L1 /* local var */){
    do
    :: node != NONE ->
        pprev_CRC_L1 = L1_NEXT(node); 
        d_step{
            L1_STATUS(node) = READY_TO_USE;
            node = pprev_CRC_L1;
        }
    :: else -> break;
    od
}

inline CleanupReverseChainL2(node, pprev_CRC_L2 /* local var */){
    do
        :: node != NONE ->
            pprev_CRC_L2 = L2_NEXT(node);
            d_step{
                L2_STATUS(node) = READY_TO_USE;
                node = pprev_CRC_L2;
            }
        :: else -> break;
    od
}


inline HandleHorizontalPassingL2(value){
    byte prev_HHP_L2 = NONE;
    byte curNode_HHP_L2 = MY_L2_NODE_ID(_pid);
    byte succTmp_HHP_L2;
    byte prevStatus_HHP_L2;

    do
        :: else ->
            if
                :: HAS_VALID_L2_SUCC(curNode_HHP_L2) ->
                    SWAP(L2_STATUS(L2_NEXT(curNode_HHP_L2)), prevStatus_HHP_L2,  value);
                    if
                        :: prevStatus_HHP_L2 == ABORTED ->
                            succTmp_HHP_L2 = L2_NEXT(curNode_HHP_L2);
                            d_step {
                                L2_NEXT(curNode_HHP_L2) = prev_HHP_L2;
                                prev_HHP_L2 = curNode_HHP_L2;
                                curNode_HHP_L2 = succTmp_HHP_L2;}
                        :: else -> L2_STATUS(curNode_HHP_L2) = READY_TO_USE; break;
                    fi
                :: else ->  ReleaseL3(); DealWithRestOfL2(curNode_HHP_L2, prev_HHP_L2); break;
            fi
    od

    byte pprev_HHP_L2;
    CleanupReverseChainL2(prev_HHP_L2, pprev_HHP_L2);
}


inline HandleHorizontalPassingL1(value){
    byte prev_HHP_L1 = NONE;
    byte curNode_HHP_L1 = MY_L1_NODE_ID(_pid);
    byte succTmp_HHP_L1; 
    byte prevStatus_HHP_L1;

    do
        :: else ->
            if
                :: HAS_VALID_L1_SUCC(curNode_HHP_L1) ->
                    SWAP(L1_STATUS(L1_NEXT(curNode_HHP_L1)), prevStatus_HHP_L1,  value);
                    if
                        :: prevStatus_HHP_L1 == ABORTED ->
                            succTmp_HHP_L1 = L1_NEXT(curNode_HHP_L1);
                            d_step {
                                L1_NEXT(curNode_HHP_L1) = prev_HHP_L1;
                                prev_HHP_L1 = curNode_HHP_L1;
                                curNode_HHP_L1 = succTmp_HHP_L1;}
                        :: else -> L1_STATUS(curNode_HHP_L1) = READY_TO_USE; break;
                    fi
                :: else ->  ReleaseL2(); DealWithRestOfL1(curNode_HHP_L1, prev_HHP_L1); break;
            fi
    od

    byte pprev_HHP_L1;
    CleanupReverseChainL1(prev_HHP_L1, pprev_HHP_L1);
}



inline HandleVerticalAbortionL3(abortedLevel) {
    d_step{
        if
            :: abortedLevel == 2 /* L3 */ -> skip;
            :: else -> skip; /* Never happens HandleHorizontalAbortionL3(abortedLevel); */
        fi
    }
}

inline HandleHorizontalAbortionL2(abortedLevel){
    byte prev_HHA_L2 = NONE;
    byte curNode_HHA_L2 = MY_L2_NODE_ID(_pid);
    byte prevStatus_HHA_L2;
    byte succTmp_HHA_L2;
    do
        :: else ->
            if
                :: HAS_VALID_L2_SUCC(curNode_HHA_L2) ->
                    SWAP(L2_STATUS(L2_NEXT(curNode_HHA_L2)), prevStatus_HHA_L2,  ACQUIRE_PARENT);
                    if
                        :: prevStatus_HHA_L2 == ABORTED ->
                            succTmp_HHA_L2 = L2_NEXT(curNode_HHA_L2);
                            d_step {
                                L2_NEXT(curNode_HHA_L2) = prev_HHA_L2;
                                prev_HHA_L2 = curNode_HHA_L2;
                                curNode_HHA_L2 = succTmp_HHA_L2;}
            :: else -> L2_STATUS(curNode_HHA_L2) = READY_TO_USE; break;
            fi
                :: else ->  HandleVerticalAbortionL3(abortedLevel); DealWithRestOfL2(curNode_HHA_L2, prev_HHA_L2); break;
            fi
    od

    /*CleanupReverseChain(prev_HHA_L2);*/
    byte pprev_HHA_L2;
    CleanupReverseChainL2(prev_HHA_L2, pprev_HHA_L2);
}


inline HandleVerticalAbortionL2(abortedLevel) {
    if
        :: abortedLevel == 1 /* L2 */ -> skip;
        :: else -> HandleHorizontalAbortionL2(abortedLevel);
    fi
}




inline HandleHorizontalAbortionL1(abortedLevel){
    byte prev_HHA_L1 = NONE;
    byte curNode_HHA_L1 = MY_L1_NODE_ID(_pid);
    byte prevStatus_HHA_L1;
    byte succTmp_HHA_L1;
    do
        :: else ->
            if
                :: HAS_VALID_L1_SUCC(curNode_HHA_L1) ->
                    SWAP(L1_STATUS(L1_NEXT(curNode_HHA_L1)), prevStatus_HHA_L1,  ACQUIRE_PARENT);
                    if
                        :: prevStatus_HHA_L1 == ABORTED ->
                            succTmp_HHA_L1 = L1_NEXT(curNode_HHA_L1);
                            d_step {
                                L1_NEXT(curNode_HHA_L1) = prev_HHA_L1;
                                prev_HHA_L1 = curNode_HHA_L1;
                                curNode_HHA_L1 = succTmp_HHA_L1;}
                        :: else -> L1_STATUS(curNode_HHA_L1) = READY_TO_USE; break;
                    fi
                :: else ->  HandleVerticalAbortionL2(abortedLevel); DealWithRestOfL1(curNode_HHA_L1, prev_HHA_L1); break;
            fi
    od

    /*CleanupReverseChain(prev_HHA_L1);*/
    byte pprev_HHA_L1;
    CleanupReverseChainL1(prev_HHA_L1, pprev_HHA_L1);
}

inline HandleVerticalAbortionL1(abortedLevel) {
    if
        :: abortedLevel == 0 /* L1 */ -> skip;
        :: else -> HandleHorizontalAbortionL1(abortedLevel);
    fi
}

inline ReleaseL2() {
    byte myL2Id = MY_L2_NODE_ID(_pid);
    byte curCount_Rel_L2 = MY_L2_STATUS;
    byte succ_Rel_L2;
    byte prev_Rel_L2 = NONE;

    if
        :: curCount_Rel_L2 == THRESHOLD -> ReleaseL3(); 
                DealWithRestOfL2(myL2Id, prev_Rel_L2);
                byte pprev_tmp1_HHA_L2;
                CleanupReverseChainL2(prev_Rel_L2, pprev_tmp1_HHA_L2);
            goto DONE_L2_RELEASE;
        :: else -> skip;
    fi
        
    byte newCurCount_Rel_L2 = curCount_Rel_L2 +1;
    HandleHorizontalPassingL2(newCurCount_Rel_L2);
DONE_L2_RELEASE: skip;
}


inline ReleaseL1() {
    byte myL1Id = MY_L1_NODE_ID(_pid);
    byte curCount_Rel_L1 = MY_L1_STATUS;
    byte succ_Rel_L1;
    byte prev_Rel_L1 = NONE;

    if
        :: curCount_Rel_L1 == THRESHOLD -> ReleaseL2(); 
                DealWithRestOfL1(myL1Id, prev_Rel_L1);
                byte pprev_tmp1_HHA_L1;
                CleanupReverseChainL1(prev_Rel_L1, pprev_tmp1_HHA_L1);
            goto DONE_L1_RELEASE;
        :: else -> skip;
    fi
        
    byte newCurCount_Rel_L1 = curCount_Rel_L1 +1;
    HandleHorizontalPassingL1(newCurCount_Rel_L1);
DONE_L1_RELEASE: skip;
}



inline AcquireWrapperL1(acquired)
{
    byte abortedLevel;
    AcquireL1(abortedLevel);
        if
        :: abortedLevel==NONE -> 
            d_step{
                acquired=true; 
                inCS++;
            } 
            assert(inCS == 1); 
            inCS--;
        :: else -> acquired=false;
    fi
}

inline AcquireWrapperL2(acquired)
{
    byte abortedLevel;
    AcquireL2(abortedLevel);
        if
        :: abortedLevel==NONE -> 
            d_step{
                acquired=true; 
                inCS++;
            } 
            assert(inCS == 1); 
            inCS--;
        :: else -> acquired=false;
    fi
}

inline AcquireWrapperL3(acquired)
{
    byte abortedLevel;
    AcquireL3(abortedLevel);
        if
        :: abortedLevel==NONE -> 
            d_step{
                acquired=true; 
                inCS++;
            } 
            assert(inCS == 1); 
            inCS--;
        :: else -> acquired=false;
    fi
}



inline DealWithRestOfLevel3(me, prev){

    do
      :: else ->
        byte retOld;
        BOOL_CAS(L3, me, NONE, retOld);        

            if 
        :: retOld == false -> 
                    BOOL_CAS(L3_NEXT(me), NONE, CANT_WAIT_FOR_NEXT, retOld); 
                    if 
                :: retOld == false ->
                               byte tmpStatus;
                    SWAP(L3_STATUS(L3_NEXT(me)), tmpStatus, UNLOCKED);
                    if
                        :: tmpStatus == ABORTED ->
                            byte tmpSucc = L3_NEXT(me);
                            d_step{
                                L3_NEXT(me) = prev;
                                prev = me;
                                me =     tmpSucc;
                            }
                        :: else -> atomic {L3_STATUS(me) = READY_TO_USE; break;}

                    fi    
                        :: else -> break;
            fi
        :: else -> atomic {L3_NEXT(me) = READY_TO_USE; break;}
       fi
        od
}

inline ReleaseL3()
{
    byte myL3Id = MY_L3_NODE_ID(_pid);
    byte prev_Rel_L3 = NONE;
    byte curNode_Rel_L3 = MY_L3_NODE_ID(_pid);
    byte prevStatus_Rel_L3;
    byte succ_Rel_L3;
    do
        :: else ->
            if
                :: HAS_VALID_L3_SUCC(curNode_Rel_L3) -> 
                   SWAP(L3_STATUS(L3_NEXT(curNode_Rel_L3)), prevStatus_Rel_L3 , UNLOCKED);
                    if
                        :: prevStatus_Rel_L3 == ABORTED ->
                            succ_Rel_L3 = L3_NEXT(curNode_Rel_L3);
                            d_step { 
                                L3_NEXT(curNode_Rel_L3) = prev_Rel_L3;
                                prev_Rel_L3 = curNode_Rel_L3;
                                curNode_Rel_L3 = succ_Rel_L3; 
                             }
                        :: else -> atomic {MY_L3_STATUS = READY_TO_USE; goto CLEANUP;}
                    fi 
                :: else -> 
                    DealWithRestOfLevel3(curNode_Rel_L3, prevStatus_Rel_L3);
                    goto CLEANUP;
       fi
    od


CLEANUP:
    do
        :: prev_Rel_L3 != NONE ->
            byte pprev_Rel_L3;
            pprev_Rel_L3 = L3_NEXT(prev_Rel_L3); 
            d_step{
                L3_STATUS(prev_Rel_L3) = READY_TO_USE;
                prev_Rel_L3 = pprev_Rel_L3;
            }
        :: else -> break;
    od
}


active [MAX_THREADS] proctype  Work() 
{ 
    byte j = 3;
    bool acquired;
/*    byte myL1Id;
    byte myL2Id;
    byte myL3Id;
*/

    /* init */
    if
        ::_pid == 0 ->
            d_step{
                inCS = 0;
                L1 = NONE;
                L2 = NONE;
                L3 = NONE;
                byte i;
                for(i: 0..(MAX_L1_THREADS-1)){
                    L1_NEXT(i) = NONE;
                    L1_STATUS(i) = WAIT;
                } 
                for(i: 0..(MAX_L2_THREADS-1)){
                    L2_NEXT(i) = NONE;
                    L2_STATUS(i) = WAIT;
                } 
                for(i: 0..(MAX_L3_THREADS-1)){
                    L3_NEXT(i) = NONE;
                    L3_STATUS(i) = WAIT;
                } 
                initialized = true;
            }
        :: else -> initialized == true;
    fi
    
/*
           if 
               :: _pid < 3 ->
                   myL1Id = _pid;
                   myL2Id = 0;
                   myL3Id = 0;
               :: _pid == 3 ->
                   myL1Id = 255;
                   myL2Id = 1;
                   myL3Id = 0;
               :: _pid == 4 ->
                   myL1Id = 255;
                   myL2Id = 2;
                   myL3Id = 0;
               :: _pid == 5 ->
                   myL1Id = 255;
                   myL2Id = 255;
                   myL3Id = 1;
               :: _pid == 6 ->
                   myL1Id = 255;
                   myL2Id = 255;
                   myL3Id = 2;
               :: else -> assert (0);
           fi
*/


   do
        :: j > 0 -> 
           if 
               :: _pid < 3 ->
                   AcquireWrapperL1(acquired); 
                   if
                       :: acquired -> ReleaseL1();
                       :: else -> skip;
                   fi
               :: _pid >= 3 && _pid < 5->
                   AcquireWrapperL2(acquired); 
                   if
                       :: acquired -> ReleaseL2();
                       :: else -> skip;
                   fi
               :: else -> 
                   AcquireWrapperL3(acquired); 
                   if
                       :: acquired -> ReleaseL3();
                       :: else -> skip;
                   fi
           fi
           j--;
        :: else -> break;
    od
}
 
/*
init {
atomic {
    run Two();
    run Two();
};
} 
*/

