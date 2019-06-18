----------------------------- MODULE rebalance -----------------------------
EXTENDS Integers

CONSTANT MaxId, MaxGeneration

CONSTANTS Consumers
\* Group state constants
Stable == 0 
PrepareRebalance == 1 
CompletingRebalance == 2
Dead == 3
Empty == 4
\* Member state constants
Unjoined == 5
Rebalancing == 6
Working == 7 
Fenced == 8

ValidGroupStates == {Stable, PrepareRebalance, CompletingRebalance, Dead, Empty}
ValidMemberStates == {Unjoined, Rebalancing, Stable, Fenced}
ValidInstanceIds == {"ins1", "ins2", "ins3"}
UNKNOWN_MEMBER_ID == 0

MemberInfo == [ memberId: 0..MaxId,
                instanceId: ValidInstanceIds, 
                state: ValidMemberStates,
                generation: 0..MaxGeneration]
          
\*MsgType == {JoinGroupRequest, JoinGroupResponse, SyncGroupRequest, SyncGroupResponse, LeaveGroupRequest, LeaveGroupResponse}
\*Messages == \* message queue containing server client interactions 
\*    [type : JoinGroupRequest, from : Consumer, id: MemberId, gen : Generation] 
\*      \cup
\*
\*    [type : JoinGroupResponse, from : Consumer, gen : Generation]  
\*      \cup
\*
\*    [type : SyncGroupRequest, from : Consumer, generation : Generation]  
\*
\*      \cup
\*    [type : SyncGroupResponse, from : Consumer, gen : Generation]
\*
\*      \cup
\*
\*    [type : LeaveGroupRequest, from : Consumer, gen : Generation]
\*
\*      \cup
\*
\*    [type : LeaveGroupResponse, ins : Consumer, gen : Generation]

-----------------------------------------------------------------------------

\* how many states you need to maintain? Local: member.id, instance.id, member state
\* remote member.id, instance.id -> member.id, group state, join callback, sync callback
VARIABLES groupState, 

          groupMembers, \* currently active members within the consumer map
          
          groupGeneration,
          
          memberIdSeq, \* the sequence number being assigned for every unknown join group

          allInstances,
          
          joinGroupCallback \* registered join group callback
            
\*          syncGroupCallback \* registered sync group callback

Is(state) == groupState = state
IsKnownMember(m) == allInstances[m].memberId /= UNKNOWN_MEMBER_ID

TypeOK == groupState \in ValidGroupStates

Init == /\ groupState = Empty 
        /\ groupMembers = [m \in Consumers |-> UNKNOWN_MEMBER_ID]
        /\ joinGroupCallback = [m \in Consumers |-> FALSE]
\*        /\ syncGroupCallback = [m \in Consumers |-> False]
        /\ memberIdSeq = UNKNOWN_MEMBER_ID + 1
        /\ allInstances = [m \in Consumers |-> [memberId |-> UNKNOWN_MEMBER_ID, state |-> Unjoined, generation |-> 0, instanceId |-> "ins1"]]
        /\ groupGeneration = 0

doUnknownJoin(m) == /\ groupState' = PrepareRebalance /\ groupMembers' = [groupMembers EXCEPT ![m] = memberIdSeq] 
/\ memberIdSeq' = memberIdSeq + 1 /\ joinGroupCallback' = [joinGroupCallback EXCEPT ![m] = TRUE] /\ UNCHANGED <<allInstances, groupGeneration>>    

JoinResp(m, memberId) == allInstances' = [allInstances EXCEPT ![m] = [memberId |-> memberId, state |-> Rebalancing]] 
    
JoinReq(m) == IF (~Is(Dead) /\ ~IsKnownMember(m))
    THEN doUnknownJoin(m)
    ELSE  
    JoinResp(m, allInstances[m].memberId) /\ UNCHANGED <<groupState, groupMembers, memberIdSeq, joinGroupCallback>>
        
allMemberJoined == \A m \in Consumers:joinGroupCallback[m] = TRUE    
CompleteJoin == /\ Is(PrepareRebalance) /\ allMemberJoined
/\ groupState' = CompletingRebalance /\ joinGroupCallback' = [m \in Consumers |-> FALSE] 
/\ groupGeneration' = groupGeneration + 1 /\ (\A m \in Consumers : JoinResp(m, groupMembers[m])) 
/\ UNCHANGED<<memberIdSeq, groupMembers>>

Next ==  \E m \in Consumers:JoinReq(m) \/ CompleteJoin

=============================================================================
\* Modification History
\* Last modified Mon Jun 17 23:59:56 PDT 2019 by boyang.chen
\* Created Mon Jun 10 22:20:01 PDT 2019 by boyang.chen
