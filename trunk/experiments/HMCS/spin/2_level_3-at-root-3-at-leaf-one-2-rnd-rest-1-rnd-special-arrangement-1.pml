/***
arrangement


L------------------------
                         |
T4-------->T5          T6

         T1 T2 T3

****/

#define MAX_L1_THREADS (3)
#define MAX_L2_THREADS (3)
#define THRESHOLD (3)
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


byte inCS;
chan ch0 = [0] of {bool};
chan ch1 = [0] of {bool};
chan ch2 = [0] of {bool};
chan ch3 = [0] of {bool};
chan ch4 = [0] of {bool};

byte nextL1[MAX_L1_THREADS];
byte statusL1[MAX_L1_THREADS];
byte L1;

bool setup = false;
bool setup2 = false;
byte done=0;

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
#define L2_STATUS(id_7) statusL2[id_7]
#define L2_NEXT(id_8) nextL2[id_8]
#define HAS_VALID_L2_SUCC(id_9) nextL2[id_9] < MAX_L2_THREADS


#define MY_L1_NODE_ID(id) (id <= 2 -> id : 0)

#define MY_L2_NODE_ID(id) (id <= 2 -> 0 : (id <= 4 -> id - 2 : 0) )


#define SWAP(loc_SWAP, var_SWAP, val_SWAP) d_step{var_SWAP=loc_SWAP; loc_SWAP=val_SWAP;}


#define CAS(loc_CAS, oldVal_CAS, newVal_CAS, retOld_CAS) d_step{ \
              if \
              :: loc_CAS == oldVal_CAS -> retOld_CAS = loc_CAS; loc_CAS = newVal_CAS;\
              :: else -> retOld_CAS = loc_CAS;\
              fi\
            }

#define CAS_IN_ATOMIC(loc_CAS, oldVal_CAS, newVal_CAS, retOld_CAS)  \
              if \
              :: loc_CAS == oldVal_CAS -> retOld_CAS = loc_CAS; loc_CAS = newVal_CAS;\
              :: else -> retOld_CAS = loc_CAS;\
              fi\
            


#define BOOL_CAS(loc_BCAS, oldVal_BCAS, newVal_BCAS, retOld_BCAS) d_step{ \
              if \
              :: loc_BCAS == oldVal_BCAS -> retOld_BCAS = true; loc_BCAS = newVal_BCAS;\
              :: else -> retOld_BCAS = false;\
              fi \
            }


inline AcquireL2(abortedLevel_Acq_L2)
{
    byte prevStatus_Acq_L2;
    byte pred_Acq_L2;
    byte predStat_Acq_L2;
    byte tmpStatus;

/*atomic{
    if
    :: (_pid -1 ==  3) && (numRounds == 3) -> ch0 ! true; ch1 ! true; ch2 ! true;
    :: else -> skip;
    fi
};*/


    SWAP(MY_L2_STATUS, prevStatus_Acq_L2, WAIT);
atomic{
    if
    :: prevStatus_Acq_L2 == ABORTED -> /*goto START_SPIN_L2;*/ 
                      if 
                      :: MY_L2_STATUS == UNLOCKED ->  abortedLevel_Acq_L2 = NONE;
                      :: else -> MY_L2_STATUS = ABORTED; abortedLevel_Acq_L2 = 1;
                      fi;
                      goto DONE_ACQUIRE_L2;

    :: prevStatus_Acq_L2 == READY_TO_USE -> MY_L2_NEXT = NONE; goto USE_QNODE_L2;
    :: prevStatus_Acq_L2 == WAIT -> MY_L2_NEXT = NONE;goto USE_QNODE_L2;
    :: prevStatus_Acq_L2 == UNLOCKED -> 
                            CAS(MY_L2_STATUS, WAIT, UNLOCKED, tmpStatus);
                            if
                            :: tmpStatus != READY_TO_USE -> abortedLevel_Acq_L2 = 1; /* L2 */ goto DONE_ACQUIRE_L2;
                            :: else -> skip;
                            fi;
    :: else -> assert (false);
    fi
}; // end atomic

          /** executed only if prevStatus_Acq_L2 == UNLOCKED **/
                /*while(I->status != READY_TO_USE); No unbounded wait*/
                /* Not needed in spin */
          
    MY_L2_NEXT = NONE;

    USE_QNODE_L2: skip;
/*** already set        MY_L2_NEXT = NONE; ***/



/** Arrange such that we are in the middle ***/
atomic{
        if
        :: myL2Id == 0 && setup2 == false -> setup2  = true; run WorkLevel2MinimalLeftEdge(); ch0?true; SWAP(L2,pred_Acq_L2, myL2Id); run WorkLevel2MinimalRightEdge(); ch1?true;
        :: else -> SWAP(L2,pred_Acq_L2, myL2Id);  
        fi;
};
/**** COMMENTED TEMPORARILY SINCE IT IS CONSUMED IN THE ABOVE IF ****
        SWAP(L2,pred_Acq_L2, myL2Id);
****/

        if
        :: d_step{pred_Acq_L2 != NONE -> 
                    /* Avoid unbounded wait for I->next */
            SWAP(L2_NEXT(pred_Acq_L2), predStat_Acq_L2, myL2Id); };




            if
            :: d_step{predStat_Acq_L2 == CANT_WAIT_FOR_NEXT ->
                        L2_STATUS(pred_Acq_L2)= READY_TO_USE;};
                        d_step {MY_L2_STATUS = UNLOCKED; abortedLevel_Acq_L2 = NONE;};
            :: atomic { else -> 
            
    START_SPIN_L2:
 
/***************** ORIGINAL **************
                   if
                   :: d_step {MY_L2_STATUS == UNLOCKED -> abortedLevel_Acq_L2 = NONE;}; 
                   :: else -> 
		            SWAP(MY_L2_STATUS, prevStatus_Acq_L2 , ABORTED);
	                    d_step {
                              if
                	      :: prevStatus_Acq_L2 == UNLOCKED -> MY_L2_STATUS = UNLOCKED; abortedLevel_Acq_L2 = NONE;
                              :: else -> abortedLevel_Acq_L2 = 1;
                    	      fi;
                            };
                   fi
****************** SEMANTICALLY SAME *********/
                      if 
                      :: MY_L2_STATUS == UNLOCKED ->  abortedLevel_Acq_L2 = NONE;
                      :: else -> MY_L2_STATUS = ABORTED; abortedLevel_Acq_L2 = 1;
                      fi;
                   };
/****************** END SEMANTICALLY SAME *********/

/** TELL LEFT TO BEGIN RELEASE ***/
atomic{  
  if
  :: setup == false -> setup = true; assert (abortedLevel_Acq_L2 == 1); ch2!true;  ch3?true;
  :: else -> skip;
  fi
};

/** ************* ***/



            fi
        :: d_step {else -> MY_L2_STATUS = UNLOCKED;abortedLevel_Acq_L2 = NONE;};
        fi


/*SET_AND_FINISH_ACQUIRE_L2: skip;
d_step {
    MY_L2_STATUS = UNLOCKED;
    abortedLevel_Acq_L2 = NONE;
}*/
DONE_ACQUIRE_L2: skip;
}

inline HandleVerticalAbortionL2(abortedLevel_HVA_L2) {
    d_step{
        if
        :: abortedLevel_HVA_L2 == 1 /* L2 */ -> skip;
        :: else -> skip; /* Never happens HandleHorizontalAbortionL2(abortedLevel_HVA_L2); */
        fi
    };
}




inline DealWithRestOfLeveL2(me_DWR_L2 /* destroyed */ , prev /* destroyed and used by caller*/ ){
        bool retOld;
        byte tmpStatus;
	byte tmpSucc;

    do
    :: d_step{else ->
       BOOL_CAS(L2, me_DWR_L2, NONE, retOld);};        

       if 
       :: d_step{
            retOld == false -> 
            BOOL_CAS(L2_NEXT(me_DWR_L2), NONE, CANT_WAIT_FOR_NEXT, retOld); };
            if 
            ::d_step{retOld == false ->
              SWAP(L2_STATUS(L2_NEXT(me_DWR_L2)), tmpStatus, UNLOCKED);};
              if
              :: d_step{
                  tmpStatus == ABORTED ->
                  tmpSucc = L2_NEXT(me_DWR_L2);};
                  d_step{
                    L2_NEXT(me_DWR_L2) = prev;
                    prev = me_DWR_L2;
                    me_DWR_L2 =     tmpSucc;
                  }
               :: atomic{else -> L2_STATUS(me_DWR_L2) = READY_TO_USE; break;};
               fi    
            :: atomic{ else -> break; };
            fi
       :: atomic{else -> L2_STATUS(me_DWR_L2) = READY_TO_USE; break;};
       fi
     od
}

inline ReleaseL2()
{
    byte prev_Rel_L2 = NONE;
    byte curNode_Rel_L2 = myL2Id;
    byte prevStatus_Rel_L2;
    byte succ_Rel_L2;
    byte pprev_Rel_L2;



    do
    :: else ->
       if
       :: HAS_VALID_L2_SUCC(curNode_Rel_L2) -> 
          SWAP(L2_STATUS(L2_NEXT(curNode_Rel_L2)), prevStatus_Rel_L2 , UNLOCKED);
          if
          :: d_step{ prevStatus_Rel_L2 == ABORTED ->
                            succ_Rel_L2 = L2_NEXT(curNode_Rel_L2); };
                            d_step { 
                                L2_NEXT(curNode_Rel_L2) = prev_Rel_L2;
                                prev_Rel_L2 = curNode_Rel_L2;
                                curNode_Rel_L2 = succ_Rel_L2; 
                             };
          :: atomic{ else -> MY_L2_STATUS = READY_TO_USE; goto CLEANUP; };
          fi 
       :: else -> 
           DealWithRestOfLeveL2(curNode_Rel_L2, prev_Rel_L2);
           goto CLEANUP;
       fi
    od


CLEANUP:
    do
    :: d_step{ prev_Rel_L2 != NONE ->
            pprev_Rel_L2 = L2_NEXT(prev_Rel_L2); };
            d_step{
                L2_STATUS(prev_Rel_L2) = READY_TO_USE;
                prev_Rel_L2 = pprev_Rel_L2;
            };
    :: atomic{else -> break;}
    od
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


inline AcquireWrapperL2(acquired_AW_L2)
{
  byte abortedLevel_AW_L2 = NONE;
  AcquireL2(abortedLevel_AW_L2);
  if
  :: d_step{ abortedLevel_AW_L2==NONE -> 
        acquired_AW_L2=true; 
        inCS++;
      };
      d_step{ assert(inCS == 1); 
      inCS--;};
  :: d_step{else -> acquired_AW_L2=false;};
  fi
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
done == 5;
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
done == 5;
};
}

proctype  WorkLevel2MinimalRightEdge()
{
    byte myL2Id = MY_L2_NODE_ID(_pid-1);
    byte prevStatus_Acq_L2_WL2M;
    byte pred_Acq_L2_WL2M;
    byte predStat_Acq_L2_WL2M;
atomic{
    SWAP(MY_L2_STATUS, prevStatus_Acq_L2_WL2M, WAIT);
    MY_L2_NEXT = NONE; 
    SWAP(L2, pred_Acq_L2_WL2M, myL2Id);
/** Inform mid ***/
    ch1!true; 
/** Wait left and mid arrangements ***/
    ch4?true;  
}; // end atomic


            /* Avoid unbounded wait for I->next */
            SWAP(L2_NEXT(pred_Acq_L2_WL2M), predStat_Acq_L2_WL2M, myL2Id);
            if
            :: d_step{predStat_Acq_L2_WL2M == CANT_WAIT_FOR_NEXT ->
                        L2_STATUS(pred_Acq_L2_WL2M)= READY_TO_USE;};
                        d_step {MY_L2_STATUS = UNLOCKED;};
            :: atomic { else -> 
                      if 
                      :: MY_L2_STATUS == UNLOCKED ->  skip;
                      :: else -> MY_L2_STATUS = ABORTED;
                      fi;
               };
            fi;


	ReleaseL2();

atomic{
done++;
done == 5;
};
} 


inline DealWithRestOfLeveL2LeftEdge(me_DWR_L2_LE /* destroyed */ , prev_LE /* destroyed and used by caller*/ ){
        bool retOld_L2_LE;

    do
    :: d_step{else ->
       BOOL_CAS(L2, me_DWR_L2_LE, NONE, retOld_L2_LE);};        

       if 
       :: atomic{
            retOld_L2_LE == false -> 
            BOOL_CAS(L2_NEXT(me_DWR_L2_LE), NONE, CANT_WAIT_FOR_NEXT, retOld_L2_LE);
// let mid  and right to go on
   ch3!true;
   ch4!true;

            if 
            :: retOld_L2_LE == false -> assert(0);
            :: else -> break;
            fi
};
       :: atomic{else -> assert(0);};
       fi
     od
}



inline ReleaseL2LeftEdge()
{
    byte prev_Rel_L2_LE = NONE;
    byte curNode_Rel_L2_LE = myL2Id;
    byte prevStatus_Rel_L2_LE;
    byte succ_Rel_L2_LE;
    byte pprev_Rel_L2_LE;



    do
    :: else ->
       if
       :: HAS_VALID_L2_SUCC(curNode_Rel_L2_LE) -> 

          SWAP(L2_STATUS(L2_NEXT(curNode_Rel_L2_LE)), prevStatus_Rel_L2_LE, UNLOCKED);

          if
          :: d_step{ prevStatus_Rel_L2_LE == ABORTED ->
                            succ_Rel_L2_LE = L2_NEXT(curNode_Rel_L2_LE); };
                            d_step { 
                                L2_NEXT(curNode_Rel_L2_LE) = prev_Rel_L2_LE;
                                prev_Rel_L2_LE = curNode_Rel_L2_LE;
                                curNode_Rel_L2_LE = succ_Rel_L2_LE; 
                             };
          :: else -> atomic{ assert(0);};
          fi 
       :: else -> 
           DealWithRestOfLeveL2LeftEdge(curNode_Rel_L2_LE, prev_Rel_L2_LE);
           goto CLEANUP;
       fi
    od


CLEANUP:
    do
    :: d_step{ prev_Rel_L2_LE != NONE ->
            pprev_Rel_L2_LE = L2_NEXT(prev_Rel_L2_LE); };
            d_step{
                L2_STATUS(prev_Rel_L2_LE) = READY_TO_USE;
                prev_Rel_L2_LE = pprev_Rel_L2_LE;
            };
    :: atomic{else -> break;}
    od
}


proctype  WorkLevel2MinimalLeftEdge()
{
    byte myL2Id = MY_L2_NODE_ID(_pid-1);
    byte prevStatus_Acq_L2_WL2M;
    byte pred_Acq_L2_WL2M;
    byte predStat_Acq_L2_WL2M;
atomic{
    SWAP(MY_L2_STATUS, prevStatus_Acq_L2_WL2M, WAIT);
    MY_L2_NEXT = NONE; 
    SWAP(L2, pred_Acq_L2_WL2M, myL2Id);
    MY_L2_STATUS = UNLOCKED;
    ch0!true; 
    ch2?true;
}; // end atomic

ReleaseL2LeftEdge();

atomic{
done++;
done == 5;
};

} 



proctype  WorkLevel2() 
{ 
  bool acquired;
  byte myL1Id;
  byte myL2Id;

d_step{
  myL1Id = MY_L1_NODE_ID(_pid-1);
  myL2Id = MY_L2_NODE_ID(_pid-1);
};

    /* ROUND 1 */

  byte abortedLevel_AW_L2 = NONE;
  AcquireL2(abortedLevel_AW_L2);
  if
  :: d_step{ abortedLevel_AW_L2==NONE -> 
        inCS++;
      };
      d_step{ assert(inCS == 1); 
      inCS--;}; ReleaseL2();
  :: d_step{else -> skip;};
  fi
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
//run WorkLevel2(); 
};
} 




