\* right now only dynamic membership
----------------------------- MODULE rebalance -----------------------------
EXTENDS Integers

CONSTANT MaxId, MaxGeneration

CONSTANTS Consumers

DEFAULT_GENERATION_ID == -1

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

JoinGroupRequest == 20
JoinGroupResponse == 21
LeaveGroupRequest == 22
LeaveGroupResponse == 23

ValidGroupStates == {Stable, PrepareRebalance, CompletingRebalance, Dead, Empty}
ValidMemberStates == {Unjoined, Rebalancing, Stable, Fenced}

RequestTypes == {JoinGroupRequest, JoinGroupResponse, LeaveGroupRequest, LeaveGroupResponse, SyncGroupRequest, SyncGroupResponse}
UNKNOWN_MEMBER_ID == 0
DYNAMIC_MEMBER == "undefined_instance_id"

UNKNOWN_MEMBER == "unknown_member"
NO_ERROR == "no_error"
ErrorTypes == {UNKNOWN_MEMBER}

\* member local state
MemberState == [memberId: 0..MaxId,
                state: ValidMemberStates,
                generation: 0..MaxGeneration]   
           
\* member info stored on group coordinator           
MemberInfo == [memberId: 0..MaxId,
               joinCallback: {TRUE, FALSE}]
               
RespMetadata == [memberId: 0..MaxId,
                 leaderId: 0..MaxId,
                 generation: 0..MaxGeneration]

GroupMetadata == [
    state: ValidGroupStates,
    generation: 0..MaxGeneration,
    members: MemberInfo,
    memberIdSeq: 0..MaxId]  \* the sequence number being assigned for every unknown join group
           
 MessageType == [type: RequestType, from: Consumers, memberId: 0..MaxId] \cup 
                [type: ResponseType, to: Consumers, error: ErrorTypes, metadata: RespMetadata]

-----------------------------------------------------------------------------

\* how many states you need to maintain? Local: member.id, member state
\* remote member.id, group state, join callback, sync callback
VARIABLES group, 
          
          consumerLocalStates,
     
          messages \* communication messages, taking a format of 
\* type -> requestType           
\* consumerId -> real consumer id (from for request, to for response)
\* memberId -> current memberId for request, assigned member id from coordinator for response
\* error (response only) -> process error                  

Is(state) == group.state = state
IsKnownMember(m) == allInstances[m].memberId /= UNKNOWN_MEMBER_ID

replyAs(mtype) == CASE mtype = JoinGroupRequest -> JoinGroupResponse
                    [] mtype = LeaveGroupRequest -> LeaveGroupResponse 

TypeOK == groupState \in ValidGroupStates
  /\ consumerLocalStates \subseteq MemberState
  /\ messages \subseteq Messages
  /\ group \subseteq GroupMetadata
 
Init == /\ memberIdSeq = UNKNOWN_MEMBER_ID + 1
        /\ consumerLocalStates = [c \in Consumers |-> [memberId |-> UNKNOWN_MEMBER_ID, 
                                                       state |-> Unjoined, 
                                                       generation |-> DEFAULT_GENERATION_ID]]
        /\ group = [state |-> Empty,
                    generation |-> DEFAULT_GENERATION_ID,
                    members |-> [m \in Consumers |-> UNKNOWN_MEMBER_ID],
                    joinGroupCallback |-> {},
                    memberIdSeq |-> 1]

\* message related functions
-----------------------------------------------------------------------------
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
         msgs @@ (m :> 1)
         
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

Send(m) == messages' = WithMessage(m, messages)

Discard(m) == messages' = WithoutMessage(m, messages)

Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))
    
DropMessage(m) ==
    /\ Discard(m) /\ UNCHANGED<<memberIdSeq, groupMembers>>
-----------------------------------------------------------------------------

\* Handle incoming request/response

deadGroupResponse(m, g) == Is(Dead) 
                     /\ Reply([type |-> replyAs(m.type),
                              to |-> m.consumerId,
                              error |-> UNKNOWN_MEMBER,
                              metadata |-> [memberId |-> m.memberId,
                                            leaderId |-> g.leaderId,
                                            generation |-> g.generation                                            
                              ]], m)
                              
\* Join group logic

RequestJoin(c) == /\ consumerLocalStates[c].state = Unjoined 
                  /\ Send([type |-> JoinGroupRequest,
                          from |-> c,         
                          memberId |-> consumerLocalStates[c].memberId])

                                                                                      
doUnknownJoin(m) == /\ IsKnownMember(m) /\ groupState' = PrepareRebalance /\ groupMembers' = [groupMembers EXCEPT ![m] = memberIdSeq] 
   /\ memberIdSeq' = memberIdSeq + 1 /\ joinGroupCallback' = [joinGroupCallback EXCEPT ![m] = TRUE] /\ UNCHANGED <<allInstances, groupGeneration>>    
                              
HandleJoinGroupRequest(m) == deadGroupResponse(m) \/ doUnknownJoin(m)
    \/  Reply([type |-> JoinGroupResponse,
           consumerId |-> m.consumerId,
           error |-> NO_ERROR,
           memberId |-> m.memberId], m) /\ UNCHANGED <<groupState, groupMembers, memberIdSeq, joinGroupCallback>>
           
   
joinOnFailure(m, memberId, error) == /\ error \in Errors /\ allInstances' = [allInstances EXCEPT ![m].state = Unjoined]

joinOnSuccess(m, memberId) == allInstances' = [allInstances EXCEPT ![m] = [memberId |-> memberId, state |-> Stable]]

HandleJoinGroupResponse(m) == joinOnFailure(m.to, m.memberId, m.error) \/ joinOnSuccess(m.to, m.memberId)

doUnknownJoin(m) == /\ ~IsKnownMember(m.consumer) /\ groupState' = PrepareRebalance /\ groupMembers' = [groupMembers EXCEPT ![m] = memberIdSeq] 
/\ memberIdSeq' = memberIdSeq + 1 /\ joinGroupCallback' = [joinGroupCallback EXCEPT ![m] = TRUE] /\ UNCHANGED <<allInstances, groupGeneration>>

doknownJoin(m) ==  Reply([type |-> JoinGroupResponse,
                          consumerId |-> m.consumerId,
                          error |-> NO_ERROR,
                          memberId |-> m.memberId], m)  /\ UNCHANGED <<allInstances, groupGeneration, groupState>>



\* Sync group logic   
   
\*requestSync(c) ==   


\* leave group logic
-----------------------------------------------------------------------------

doUnknownLeave(m) == /\ ~IsKnownMember(m) /\ groupState' = PrepareRebalance /\ groupMembers' = [groupMembers EXCEPT ![m.memberId] = ] 

HandleLeaveGroupRequest(m) == deadGroupResponse(m) /\ ~IsKnownMember(m) /\ 
                Reply([type |-> LeaveGroupResponse,
                       consumerId |-> m.consumerId,
                  error |-> NO_ERROR,
                  memberId |-> m.memberId], m)

Receive(m) == 
\/ /\ m.type = JoinGroupRequest /\ HandleJoinGroupRequest(m)
\/ m.type = JoinGroupResponse /\ HandleJoinGroupResponse(m)
\/ m.type = LeaveGroupRequest /\ HandleLeaveGroupRequest(m)
\/ m.type = LeaveGroupResponse /\ HandleLeaveGroupResponse(m)
        
allMemberJoined == \A m \in Consumers:joinGroupCallback[m] = TRUE
    
CompleteJoin == /\ Is(PrepareRebalance) /\ allMemberJoined
/\ groupState' = CompletingRebalance /\ joinGroupCallback' = [m \in Consumers |-> FALSE] 
/\ groupGeneration' = groupGeneration + 1 /\ (\A m \in Consumers : JoinResp(m, groupMembers[m], NO_ERROR)) 
/\ UNCHANGED<<memberIdSeq, groupMembers>>

CompleteJoinTimeout == /\ Is(PrepareRebalance) /\ ~allMemberJoined /\ groupState' = CompletingRebalance 

SessionTimeout(m) == /\ groupMembers[m] /= UNKNOWN_MEMBER_ID /\ allInstances' = [allInstances EXCEPT ![m].state = Unjoined] 

Next ==  \E m \in Consumers: HandleJoinGroupRequest(m) \/ CompleteJoin \/ CompleteJoinTimeout

=============================================================================
\* Modification History
\* Last modified Tue Jul 23 17:40:20 PDT 2019 by boyang.chen
\* Created Mon Jun 10 22:20:01 PDT 2019 by boyang.chen
