---- MODULE AnthonyWilliamsStack ----

EXTENDS TLC, Sequences, Integers

(*--algorithm stack

variables
    StackVar = <<>>,
    MemoryOrderSeqLock = 0,

define
    \* invariant
    NoRaceCondition == MemoryOrderSeqLock <= 1
    \* temporal property
    FinishedEmpty == Len(StackVar) = 0
end define;

process worker \in 1..9
variables
    HeadPush = "",
    HeadPop = "",

begin
Push1:
    await MemoryOrderSeqLock = 0;
    MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
    if StackVar /= <<>> then
        HeadPush := Head(StackVar);
    else
        StackVar := Append(StackVar, Len(StackVar));
        goto PushUnlock2;
    end if;

PushUnlock1:
    MemoryOrderSeqLock := MemoryOrderSeqLock - 1;

Push2:
    \* CAS-loop
    await MemoryOrderSeqLock = 0;

    if StackVar = <<>> then
        goto Push1;
    else
        if HeadPush = Head(StackVar) then
            MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
            StackVar := Append(StackVar, Len(StackVar));
        else
            goto Push2;
        end if;
    end if;

PushUnlock2:
    MemoryOrderSeqLock := MemoryOrderSeqLock - 1;

Pop1:
    await MemoryOrderSeqLock = 0;
    MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
    if StackVar /= <<>> then
        HeadPop := Head(StackVar);
    else
        goto pop_unlock2;
    end if;

PopUnlock1:
    MemoryOrderSeqLock := MemoryOrderSeqLock - 1;

Pop2:
    \* CAS-loop
    await MemoryOrderSeqLock = 0;
    if StackVar = <<>> then
        goto Pop1;
    else
        if HeadPop = Head(StackVar) then
            MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
            StackVar := SubSeq(StackVar, 1, Len(StackVar) - 1);
        else
            goto Pop2;
        end if;
    end if;

pop_unlock2:
    MemoryOrderSeqLock := MemoryOrderSeqLock - 1;

end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "fef3b82a" /\ chksum(tla) = "e516c799")
VARIABLES StackVar, MemoryOrderSeqLock, pc

(* define statement *)
NoRaceCondition == MemoryOrderSeqLock <= 1

FinishedEmpty == Len(StackVar) = 0

VARIABLES HeadPush, HeadPop

vars == << StackVar, MemoryOrderSeqLock, pc, HeadPush, HeadPop >>

ProcSet == (1..9)

Init == (* Global variables *)
        /\ StackVar = <<>>
        /\ MemoryOrderSeqLock = 0
        (* Process worker *)
        /\ HeadPush = [self \in 1..9 |-> ""]
        /\ HeadPop = [self \in 1..9 |-> ""]
        /\ pc = [self \in ProcSet |-> "Push1"]

Push1(self) == /\ pc[self] = "Push1"
               /\ MemoryOrderSeqLock = 0
               /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
               /\ IF StackVar /= <<>>
                     THEN /\ HeadPush' = [HeadPush EXCEPT ![self] = Head(StackVar)]
                          /\ pc' = [pc EXCEPT ![self] = "PushUnlock1"]
                          /\ UNCHANGED StackVar
                     ELSE /\ StackVar' = Append(StackVar, Len(StackVar))
                          /\ pc' = [pc EXCEPT ![self] = "PushUnlock2"]
                          /\ UNCHANGED HeadPush
               /\ UNCHANGED HeadPop

PushUnlock1(self) == /\ pc[self] = "PushUnlock1"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = "Push2"]
                     /\ UNCHANGED << StackVar, HeadPush, HeadPop >>

Push2(self) == /\ pc[self] = "Push2"
               /\ MemoryOrderSeqLock = 0
               /\ IF StackVar = <<>>
                     THEN /\ pc' = [pc EXCEPT ![self] = "Push1"]
                          /\ UNCHANGED << StackVar, MemoryOrderSeqLock >>
                     ELSE /\ IF HeadPush[self] = Head(StackVar)
                                THEN /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                                     /\ StackVar' = Append(StackVar, Len(StackVar))
                                     /\ pc' = [pc EXCEPT ![self] = "PushUnlock2"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Push2"]
                                     /\ UNCHANGED << StackVar, 
                                                     MemoryOrderSeqLock >>
               /\ UNCHANGED << HeadPush, HeadPop >>

PushUnlock2(self) == /\ pc[self] = "PushUnlock2"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = "Pop1"]
                     /\ UNCHANGED << StackVar, HeadPush, HeadPop >>

Pop1(self) == /\ pc[self] = "Pop1"
              /\ MemoryOrderSeqLock = 0
              /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
              /\ IF StackVar /= <<>>
                    THEN /\ HeadPop' = [HeadPop EXCEPT ![self] = Head(StackVar)]
                         /\ pc' = [pc EXCEPT ![self] = "PopUnlock1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "pop_unlock2"]
                         /\ UNCHANGED HeadPop
              /\ UNCHANGED << StackVar, HeadPush >>

PopUnlock1(self) == /\ pc[self] = "PopUnlock1"
                    /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                    /\ pc' = [pc EXCEPT ![self] = "Pop2"]
                    /\ UNCHANGED << StackVar, HeadPush, HeadPop >>

Pop2(self) == /\ pc[self] = "Pop2"
              /\ MemoryOrderSeqLock = 0
              /\ IF StackVar = <<>>
                    THEN /\ pc' = [pc EXCEPT ![self] = "Pop1"]
                         /\ UNCHANGED << StackVar, MemoryOrderSeqLock >>
                    ELSE /\ IF HeadPop[self] = Head(StackVar)
                               THEN /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                                    /\ StackVar' = SubSeq(StackVar, 1, Len(StackVar) - 1)
                                    /\ pc' = [pc EXCEPT ![self] = "pop_unlock2"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Pop2"]
                                    /\ UNCHANGED << StackVar, 
                                                    MemoryOrderSeqLock >>
              /\ UNCHANGED << HeadPush, HeadPop >>

pop_unlock2(self) == /\ pc[self] = "pop_unlock2"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << StackVar, HeadPush, HeadPop >>

worker(self) == Push1(self) \/ PushUnlock1(self) \/ Push2(self)
                   \/ PushUnlock2(self) \/ Pop1(self) \/ PopUnlock1(self)
                   \/ Pop2(self) \/ pop_unlock2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..9: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

===================================
