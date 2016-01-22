#define MAX_L1_THREADS (3)
#define MAX_L2_THREADS (3)
#define MAX_L3_THREADS (1)

#define THRESHOLD (3)

#define MAX_THREADS (7)

#define NONE (255)


#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (254)
#define ABORTED (253)
#define READY_TO_USE (252)
#define ACQUIRE_PARENT (250)
#define CANT_WAIT_FOR_NEXT (251)

#define COHORT_START (1)
#define ALARM_TIME (3 * 60)


bool initialized;
bool statusRoundOneA = true;
byte inCS;
byte done=0;


byte nextL1[MAX_L1_THREADS];
byte statusL1[MAX_L1_THREADS];
byte L1;
#define MY_L1_STATUS statusL1[myL1Id]
#define MY_L1_NEXT nextL1[myL1Id]
#define L1_STATUS(id_1) statusL1[id_1]
#define L1_NEXT(id_2) nextL1[id_2]
#define HAS_VALID_L1_SUCC(id_3) nextL1[id_3] < MAX_L1_THREADS


byte nextL2[MAX_L2_THREADS];
byte statusL2[MAX_L2_THREADS];
byte L2;
#define MY_L2_STATUS statusL2[myL2Id]
#define MY_L2_NEXT nextL2[myL2Id]
#define L2_STATUS(id_4) statusL2[id_4]
#define L2_NEXT(id_5) nextL2[id_5]
#define HAS_VALID_L2_SUCC(id_6) nextL2[id_6] < MAX_L2_THREADS



#define MY_L1_NODE_ID(id) (id <= 2 -> id : 0)

#define MY_L2_NODE_ID(id) (id <= 2 -> 0 : (id <= 4 -> id - 2 : 0) )

#define MY_L3_NODE_ID(id) (id <= 4 -> 0 : id - 4)

/*

#define MY_L1_NODE_ID(id_123) (0)

#define MY_L2_NODE_ID(id_456) (id_456 <= 2 -> id_456: 0)

#define MY_L3_NODE_ID(id_768) (id_768 <= 2 -> 0 : id_768 - 2 )
*/

/*
#define MY_L3_NODE_ID(id) (id)
*/

#define SWAP(loc_SWAP, var_SWAP, val_SWAP) d_step{var_SWAP=loc_SWAP; loc_SWAP=val_SWAP;}


#define CAS(loc_CAS, oldVal_CAS, newVal_CAS, retOld_CAS) d_step{ \
                          if \
                            :: loc_CAS == oldVal_CAS -> retOld_CAS = loc_CAS; loc_CAS = newVal_CAS;\
                            :: else -> retOld_CAS = loc_CAS;\
                          fi\
                        }

#define BOOL_CAS(loc_BCAS, oldVal_BCAS, newVal_BCAS, retOld_BCAS) d_step{ \
                          if \
                            :: loc_BCAS == oldVal_BCAS -> retOld_BCAS = true; loc_BCAS = newVal_BCAS;\
                            :: else -> retOld_BCAS = false;\
                          fi \
                        }


inline AcquireL3(abortedLevel_Acq_L3)
{


    /* always acquire here */
    abortedLevel_Acq_L3 = NONE;

    /* always abort here 
d_step{
        abortedLevel_Acq_L3 = 2; 
        inCS++;
      };
      d_step{ assert(inCS == 1); 
      inCS--;}; */
}


inline AcquireL2(abortedLevel_Acq_L2)
{
    byte prevStatus_Acq_L2;
    byte pred_Acq_L2;
    byte predNext_Acq_L2;
    byte tmpStatus_Acq_L2;
    SWAP(MY_L2_STATUS, prevStatus_Acq_L2, WAIT);

atomic{
    if
        :: prevStatus_Acq_L2 == ABORTED -> goto START_SPIN_L2;
        :: prevStatus_Acq_L2 == COHORT_START -> goto GOT_LOCK_L2;
        :: prevStatus_Acq_L2 == WAIT -> MY_L2_NEXT = NONE; goto USE_QNODE_L2;
        :: prevStatus_Acq_L2 == READY_TO_USE -> MY_L2_NEXT = NONE; goto USE_QNODE_L2;
        :: else ->
            /*while(I->status != READY_TO_USE); No unbounded wait*/
            CAS(MY_L2_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L2);
            if
                :: tmpStatus_Acq_L2 != READY_TO_USE -> abortedLevel_Acq_L2 = 1 /* L2 */; 
                   goto DONE_ACQUIRE_L2;
                :: else -> skip;
            fi
    fi

};

        /** Happens only from else ***/

    MY_L2_NEXT = NONE;

USE_QNODE_L2: skip;
/* arrange such that we are in the left */
atomic{
if
:: statusRoundOneA == true -> 
	statusRoundOneA = false; 
        SWAP(L2,pred_Acq_L2, myL2Id);
:: else ->  SWAP(L2,pred_Acq_L2, myL2Id);
fi
}

    if
        :: atomic{ pred_Acq_L2 == NONE ->
    GOT_LOCK_L2:
            MY_L2_STATUS = COHORT_START; };
            AcquireL3(abortedLevel_Acq_L2);
        :: else ->
            /* Avoid unbounded wait for I->next */
            SWAP(L2_NEXT(pred_Acq_L2), predNext_Acq_L2, myL2Id);
            if
                :: d_step { predNext_Acq_L2 == CANT_WAIT_FOR_NEXT ->
                    L2_STATUS(pred_Acq_L2)= READY_TO_USE;};
                    MY_L2_STATUS = COHORT_START;
                    AcquireL3(abortedLevel_Acq_L2);
                :: atomic { else ->
        START_SPIN_L2: skip;
            SWAP(MY_L2_STATUS, prevStatus_Acq_L2 , ABORTED); };
            atomic {
                if
                :: prevStatus_Acq_L2 < ACQUIRE_PARENT -> MY_L2_STATUS  = prevStatus_Acq_L2 ; goto DONE_ACQUIRE_L2;
                :: prevStatus_Acq_L2 == ACQUIRE_PARENT -> MY_L2_STATUS  = COHORT_START ;
                :: else -> abortedLevel_Acq_L2 = 1 /* L2 */; goto DONE_ACQUIRE_L2;
                fi
            };
            AcquireL3(abortedLevel_Acq_L2); 
     fi
    fi
    DONE_ACQUIRE_L2: skip;
}


inline DealWithRestOfL2(me_DWR_L2 /* destroyed */, prev_DWR_L2 /* destroyed and used in caller */){
    bool retOld_DWR_L2;
    byte tmpStatus_DWR_L2;
    byte tmpSucc_DWR_L2;
    do
      :: d_step{else ->
            BOOL_CAS(L2, me_DWR_L2, NONE, retOld_DWR_L2);};
            if 
            :: retOld_DWR_L2 == false ->
                    if
                         :: L2_STATUS(me_DWR_L2) == COHORT_START ->  
                            L2_STATUS(me_DWR_L2) = ACQUIRE_PARENT;
                         :: d_step{ else -> skip; };
                    fi

                    BOOL_CAS(L2_NEXT(me_DWR_L2), NONE, CANT_WAIT_FOR_NEXT, retOld_DWR_L2); 
                    if 
                    :: d_step{retOld_DWR_L2 == false ->
                       SWAP(L2_STATUS(L2_NEXT(me_DWR_L2)), tmpStatus_DWR_L2, ACQUIRE_PARENT);};
                       if
                       ::d_step{ tmpStatus_DWR_L2 == ABORTED ->
                          tmpSucc_DWR_L2 = L2_NEXT(me_DWR_L2);};
                          d_step{
                            L2_NEXT(me_DWR_L2) = prev_DWR_L2;
                            prev_DWR_L2 = me_DWR_L2;
                            me_DWR_L2 =     tmpSucc_DWR_L2;
                          }
                       :: atomic {else -> L2_STATUS(me_DWR_L2) = READY_TO_USE; break;};
                       fi
                    ::atomic{ else -> break;}
                    fi
            :: atomic {else -> L2_STATUS(me_DWR_L2) = READY_TO_USE; break;};
            fi
    od
}


inline CleanupReverseChainL2(node_CRC_L2 /* destroyed */, pprev_CRC_L2 /* local var */){
    do
        :: d_step{node_CRC_L2 != NONE ->
            pprev_CRC_L2 = L2_NEXT(node_CRC_L2);};
            d_step{
                L2_STATUS(node_CRC_L2) = READY_TO_USE;
                node_CRC_L2 = pprev_CRC_L2;
            }
        :: atomic {else -> break;};
    od
}


inline HandleHorizontalPassingL2(value_HHP_L2 /* const */){
    byte prev_HHP_L2 = NONE;
    byte curNode_HHP_L2 = myL2Id;
    byte succTmp_HHP_L2;
    byte prevStatus_HHP_L2;

    do
        :: else ->
            if
            :: HAS_VALID_L2_SUCC(curNode_HHP_L2) ->
                    SWAP(L2_STATUS(L2_NEXT(curNode_HHP_L2)), prevStatus_HHP_L2,  value_HHP_L2);
                    if
                    :: d_step{ prevStatus_HHP_L2 == ABORTED ->
                            succTmp_HHP_L2 = L2_NEXT(curNode_HHP_L2);};
                            d_step {
                                L2_NEXT(curNode_HHP_L2) = prev_HHP_L2;
                                prev_HHP_L2 = curNode_HHP_L2;
                                curNode_HHP_L2 = succTmp_HHP_L2;}
                    :: atomic { else -> L2_STATUS(curNode_HHP_L2) = READY_TO_USE; break;};
                    fi
            :: else ->  ReleaseL3(); DealWithRestOfL2(curNode_HHP_L2, prev_HHP_L2); break;
            fi
    od

    byte pprev_HHP_L2;
    CleanupReverseChainL2(prev_HHP_L2, pprev_HHP_L2);
}




inline HandleVerticalAbortionL3(abortedLevel_HVA_L3) {
    d_step{
        if
            :: abortedLevel_HVA_L3 == 2 /* L3 */ -> skip;
            :: else -> skip; /* Never happens HandleHorizontalAbortionL3(abortedLevel_HVA_L3); */
        fi
    }
}

inline HandleHorizontalAbortionL2(abortedLevel_HHA_L2){
    byte prev_HHA_L2 = NONE;
    byte curNode_HHA_L2 = myL2Id;
    byte prevStatus_HHA_L2;
    byte succTmp_HHA_L2;
    do
        :: else ->
            if
            :: HAS_VALID_L2_SUCC(curNode_HHA_L2) ->
                    SWAP(L2_STATUS(L2_NEXT(curNode_HHA_L2)), prevStatus_HHA_L2,  ACQUIRE_PARENT);
                    if
                    :: d_step { prevStatus_HHA_L2 == ABORTED ->
                            succTmp_HHA_L2 = L2_NEXT(curNode_HHA_L2);};
                            d_step {
                                L2_NEXT(curNode_HHA_L2) = prev_HHA_L2;
                                prev_HHA_L2 = curNode_HHA_L2;
                                curNode_HHA_L2 = succTmp_HHA_L2;}
                    :: atomic {else -> L2_STATUS(curNode_HHA_L2) = READY_TO_USE; break;};
                    fi
            :: else ->  HandleVerticalAbortionL3(abortedLevel_HHA_L2); DealWithRestOfL2(curNode_HHA_L2, prev_HHA_L2); break;
            fi
    od

    /*CleanupReverseChain(prev_HHA_L2);*/
    byte pprev_HHA_L2;
    CleanupReverseChainL2(prev_HHA_L2, pprev_HHA_L2);
}


inline HandleVerticalAbortionL2(abortedLevel_HVA_L2) {
    if
        :: d_step {abortedLevel_HVA_L2 == 1 /* L2 */ -> skip;}
        :: else -> HandleHorizontalAbortionL2(abortedLevel_HVA_L2);
    fi
}


inline ReleaseL2() {
    byte curCount_Rel_L2 = MY_L2_STATUS;
    byte succ_Rel_L2;
    byte prev_Rel_L2 = NONE;
    byte copyMyL2Id = myL2Id;
    byte newCurCount_Rel_L2 = curCount_Rel_L2 +1;
    byte pprev_tmp1_HHA_L2;

    if
    :: curCount_Rel_L2 == THRESHOLD -> ReleaseL3(); 
       DealWithRestOfL2(copyMyL2Id, prev_Rel_L2);
       CleanupReverseChainL2(prev_Rel_L2, pprev_tmp1_HHA_L2);
    :: else -> HandleHorizontalPassingL2(newCurCount_Rel_L2);
    fi
}


inline AcquireWrapperL2(acquired_AW_L2)
{
    byte abortedLevel_AW_L2 = NONE;
    AcquireL2(abortedLevel_AW_L2);
    if
    :: d_step{ abortedLevel_AW_L2==NONE -> 
                acquired_AW_L2=true; 
                inCS++;
       }
       d_step{   
            assert(inCS == 1); 
            inCS--;
       };
    :: d_step{ else -> acquired_AW_L2=false;}; HandleVerticalAbortionL2(abortedLevel_AW_L2); 
    fi
}

inline ReleaseL3()
{
  skip;
}




inline AcquireL1(abortedLevel_Acq_L1)
{
  byte prevStatus_Acq_L1;
  byte pred_Acq_L1;
  byte predStat_Acq_L1;
  byte tmpStatus_Acq_L1;
  SWAP(MY_L1_STATUS, prevStatus_Acq_L1, WAIT);


atomic{
  if
  :: prevStatus_Acq_L1 == ABORTED -> goto START_SPIN_L1;
  :: prevStatus_Acq_L1 == COHORT_START -> goto  GOT_LOCK_L1;
  :: prevStatus_Acq_L1 == WAIT -> MY_L1_NEXT = NONE; goto USE_QNODE_L1;
  :: prevStatus_Acq_L1 == READY_TO_USE -> MY_L1_NEXT = NONE; goto USE_QNODE_L1;
  :: else -> CAS(MY_L1_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L1);
             if
             :: tmpStatus_Acq_L1 != READY_TO_USE -> abortedLevel_Acq_L1 = 0 /* L1 */; 
                goto DONE_ACQUIRE_L1;
             ::else -> skip;
             fi;

  fi;
};
        /** Happens only from else ***/
        /*while(I->status != READY_TO_USE); No unbounded wait*/
       
  MY_L1_NEXT = NONE;


  USE_QNODE_L1: skip;

  /**** already set MY_L1_NEXT = NONE; ****/
  SWAP(L1,pred_Acq_L1, myL1Id);

/*atomic{
    if
    :: (_pid -1 ==  0) && (numRounds == 3) -> run Work(); ch0 ? true;
    :: (_pid -1 ==  1) && (numRounds == 3) -> run Work(); ch1 ? true;
    :: (_pid -1 ==  2) && (numRounds == 3) -> run Work(); ch2 ? true;
    :: else -> skip;
    fi
};*/



  if
  :: atomic{ pred_Acq_L1 == NONE ->
GOT_LOCK_L1:    
      MY_L1_STATUS = COHORT_START; };
      AcquireL2(abortedLevel_Acq_L1);
  :: else ->
        /* Avoid unbounded wait for I->next */
      SWAP(L1_NEXT(pred_Acq_L1), predStat_Acq_L1, myL1Id);
      if
      :: d_step {predStat_Acq_L1 == CANT_WAIT_FOR_NEXT ->
          L1_STATUS(pred_Acq_L1)= READY_TO_USE;};
          MY_L1_STATUS = COHORT_START;
          AcquireL2(abortedLevel_Acq_L1);
      :: atomic{ else -> 
START_SPIN_L1: skip;
           SWAP(MY_L1_STATUS, prevStatus_Acq_L1 , ABORTED); };
           atomic{
             if
             :: prevStatus_Acq_L1 < ACQUIRE_PARENT -> MY_L1_STATUS  = prevStatus_Acq_L1; abortedLevel_Acq_L1 = NONE;  goto DONE_ACQUIRE_L1;
             :: prevStatus_Acq_L1 == ACQUIRE_PARENT -> MY_L1_STATUS  = COHORT_START; 
             :: else -> abortedLevel_Acq_L1 = 0 /* L1 */; goto DONE_ACQUIRE_L1;
             fi
           };
           /* executed iff prevStatus_Acq_L1 == ACQUIRE_PARENT */
           AcquireL2(abortedLevel_Acq_L1); 
      fi
  fi
  DONE_ACQUIRE_L1: skip;
}




inline DealWithRestOfL1(me_DWR_L1 /* destroyed */, prev_DWR_L1 /* destroyed and used in caller */){
  bool retOld_DWR_L1;
  byte tmpStatus_DWR_L1;
  byte tmpSucc_DWR_L1;
  do
  :: d_step{else ->
     BOOL_CAS(L1, me_DWR_L1, NONE, retOld_DWR_L1);};
     if 
     :: retOld_DWR_L1 == false ->
        if
        :: L1_STATUS(me_DWR_L1) == COHORT_START ->  
             L1_STATUS(me_DWR_L1) = ACQUIRE_PARENT;
        :: d_step { else -> 
             skip; };
        fi
        BOOL_CAS(L1_NEXT(me_DWR_L1), NONE, CANT_WAIT_FOR_NEXT, retOld_DWR_L1); 
        if 
        :: d_step{retOld_DWR_L1 == false ->
           SWAP(L1_STATUS(L1_NEXT(me_DWR_L1)), tmpStatus_DWR_L1, ACQUIRE_PARENT);};
           if
           :: d_step{tmpStatus_DWR_L1 == ABORTED ->
              tmpSucc_DWR_L1 = L1_NEXT(me_DWR_L1);};
              d_step{
                L1_NEXT(me_DWR_L1) = prev_DWR_L1;
                prev_DWR_L1 = me_DWR_L1;
                me_DWR_L1 =   tmpSucc_DWR_L1;};
           :: atomic{else -> L1_STATUS(me_DWR_L1) = READY_TO_USE; break; };
           fi
        :: atomic{ else -> break; }
        fi
      :: atomic{else -> L1_STATUS(me_DWR_L1) = READY_TO_USE; break; };
      fi
  od
}

inline CleanupReverseChainL1(node_CRC_L1 /* destroyed */, pprev_CRC_L1 /* local var */){
  do
  :: d_step{ node_CRC_L1 != NONE ->
    pprev_CRC_L1 = L1_NEXT(node_CRC_L1); };
    d_step{
      L1_STATUS(node_CRC_L1) = READY_TO_USE;
      node_CRC_L1 = pprev_CRC_L1;
    };
  :: atomic{ else -> break; };
  od
}


inline HandleHorizontalPassingL1(value_HHP_L1 /* const */){
  byte prev_HHP_L1 = NONE;
  byte curNode_HHP_L1 = myL1Id;
  byte succTmp_HHP_L1; 
  byte prevStatus_HHP_L1;

  do
    :: else ->
       if
       :: HAS_VALID_L1_SUCC(curNode_HHP_L1) ->
         SWAP(L1_STATUS(L1_NEXT(curNode_HHP_L1)), prevStatus_HHP_L1,  value_HHP_L1);
          if
          :: d_step{prevStatus_HHP_L1 == ABORTED ->
             succTmp_HHP_L1 = L1_NEXT(curNode_HHP_L1);};
             d_step {
                L1_NEXT(curNode_HHP_L1) = prev_HHP_L1;
                prev_HHP_L1 = curNode_HHP_L1;
                curNode_HHP_L1 = succTmp_HHP_L1;};
          :: atomic{else -> L1_STATUS(curNode_HHP_L1) = READY_TO_USE; break; };
          fi
        :: else ->  ReleaseL2(); DealWithRestOfL1(curNode_HHP_L1, prev_HHP_L1); break;
      fi
  od

  byte pprev_HHP_L1;
  CleanupReverseChainL1(prev_HHP_L1, pprev_HHP_L1);
}


inline HandleHorizontalAbortionL1(abortedLevel_HHA_L1){
  byte prev_HHA_L1 = NONE;
  byte curNode_HHA_L1 = myL1Id;
  byte prevStatus_HHA_L1;
  byte succTmp_HHA_L1;
  do
    :: else ->
      if
      :: HAS_VALID_L1_SUCC(curNode_HHA_L1) ->
         SWAP(L1_STATUS(L1_NEXT(curNode_HHA_L1)), prevStatus_HHA_L1,  ACQUIRE_PARENT);
         if
         :: d_step{prevStatus_HHA_L1 == ABORTED ->
            succTmp_HHA_L1 = L1_NEXT(curNode_HHA_L1);};
            d_step {
                L1_NEXT(curNode_HHA_L1) = prev_HHA_L1;
                prev_HHA_L1 = curNode_HHA_L1;
                curNode_HHA_L1 = succTmp_HHA_L1;};
         :: atomic{else -> L1_STATUS(curNode_HHA_L1) = READY_TO_USE;break; };
         fi
      :: else ->  HandleVerticalAbortionL2(abortedLevel_HHA_L1); DealWithRestOfL1(curNode_HHA_L1, prev_HHA_L1); break;
      fi
  od

  /*CleanupReverseChain(prev_HHA_L1);*/
  byte pprev_HHA_L1;
  CleanupReverseChainL1(prev_HHA_L1, pprev_HHA_L1);
}

inline HandleVerticalAbortionL1(abortedLevel_HVA_L1) {
  if
  :: d_step{ abortedLevel_HVA_L1 == 0 /* L1 */ -> skip; };
  :: else -> HandleHorizontalAbortionL1(abortedLevel_HVA_L1);
  fi
}


inline ReleaseL1() {
  byte curCount_Rel_L1 = MY_L1_STATUS;
  byte succ_Rel_L1;
  byte prev_Rel_L1 = NONE;
  byte copyMyL1Id = myL1Id;
  byte newCurCount_Rel_L1 = curCount_Rel_L1 +1;
  byte pprev_tmp1_HHA_L1;

  if
  :: curCount_Rel_L1 == THRESHOLD -> ReleaseL2(); 
        DealWithRestOfL1(copyMyL1Id, prev_Rel_L1);
        CleanupReverseChainL1(prev_Rel_L1, pprev_tmp1_HHA_L1);
  :: else -> HandleHorizontalPassingL1(newCurCount_Rel_L1);
  fi
}



inline AcquireWrapperL1(acquired_AW_L1)
{
  byte abortedLevel_AW_L1 = NONE;
  AcquireL1(abortedLevel_AW_L1);
  if
  :: d_step{abortedLevel_AW_L1==NONE -> 
        acquired_AW_L1=true; 
        inCS++;
      }; 
     d_step{assert(inCS == 1); 
      inCS--;};
  :: d_step{else -> acquired_AW_L1=false;}; HandleVerticalAbortionL1(abortedLevel_AW_L1); 
  fi
}


inline EnsureAllinRState(){
        byte index;

        for(index: 0..(MAX_L1_THREADS-1)){
          assert(L1_STATUS(index) == READY_TO_USE);
        }
        for(index: 0..(MAX_L2_THREADS-1)){
          assert(L2_STATUS(index) == READY_TO_USE);
        }
}

proctype  WorkObserved() 
{ 
  bool acquired;
  byte numRounds = 2;
  byte myL1Id;
  byte myL2Id;

d_step{
  myL1Id = MY_L1_NODE_ID(_pid-1);
  myL2Id = MY_L2_NODE_ID(_pid-1);
};

  do
  :: numRounds > 0 ->
           AcquireWrapperL1(acquired); 
           if
           :: d_step {acquired -> numRounds--;}; ReleaseL1();
           :: d_step{else -> numRounds--;};
           fi
  :: atomic{ else -> break; };
  od
atomic{
done++;
};
}


proctype  WorkLevel1() 
{ 
  bool acquired;
  byte myL1Id;
  byte myL2Id;

d_step{
  myL1Id = MY_L1_NODE_ID(_pid-1);
  myL2Id = MY_L2_NODE_ID(_pid-1);
};


    /* ROUND 1 */
  byte abortedLevel_AW_L1 = NONE;
  AcquireL1(abortedLevel_AW_L1);
  if
  :: d_step{abortedLevel_AW_L1==NONE -> 
        inCS++;
      }; 
     d_step{assert(inCS == 1); 
      inCS--;}; ReleaseL1();
  :: else -> HandleVerticalAbortionL1(abortedLevel_AW_L1); 
  fi

atomic{
done++;
};
}

proctype  WorkLevel2() 
{ 
  bool acquired;
  byte myL1Id;
  byte myL2Id;


/* arrange such that myL2id==1 is in the middle and myL2id==2 is in the right */
atomic{
  myL1Id = MY_L1_NODE_ID(_pid-1);
  myL2Id = MY_L2_NODE_ID(_pid-1);
        if
                ::myL2Id==1 -> endA: L2==0; /* till the left guy is 0 */
                ::myL2Id==2 -> endB: L2==1;  /* till the left guy is 1 */
                ::else       -> assert(0);
        fi;
}

    /* ROUND 1 */

  byte abortedLevel_AW_L2 = NONE;
  AcquireL2(abortedLevel_AW_L2);
  if
  :: d_step{ abortedLevel_AW_L2==NONE -> 
        inCS++;
      };
      d_step{ assert(inCS == 1); 
      inCS--;}; ReleaseL2();
  :: else -> HandleVerticalAbortionL2(abortedLevel_AW_L2);
  fi

atomic{
done++;
};
}
 
 
init {
  /* init */
      d_step{
        inCS = 0;
        L1 = NONE;
        L2 = NONE;
        byte i;
        for(i: 0..(MAX_L1_THREADS-1)){
          L1_NEXT(i) = NONE;
          L1_STATUS(i) = READY_TO_USE;
        }
        for(i: 0..(MAX_L2_THREADS-1)){
          L2_NEXT(i) = NONE;
          L2_STATUS(i) = READY_TO_USE;
        }
      }
  // 4 threads
atomic {
  run WorkLevel1(); 
  run WorkLevel1(); 
  run WorkObserved(); 
  run WorkLevel2(); 
  run WorkLevel2(); 
};
if
::done == 5 -> EnsureAllinRState();
::else -> skip;
fi;
} 


