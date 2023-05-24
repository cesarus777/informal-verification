---- MODULE AnthonyWilliamsStack ----

EXTENDS TLC, Sequences, Integers
CONSTANTS NTasks, Producers, Consumers
(*--algorithm stack

variables
    \* primary 0 stands for empty stack to check pop from empty stack
    Stack = <<0>>,
    MemoryOrderSeqLock = 0,
    NTasksLeft = NTasks,
    NTasksPopped = 0

define
    \* invariant
    NoRaceCondition == MemoryOrderSeqLock <= 1
    StackIsCorrect == Len(Stack) >= 1
    \* temporal property
    EmptyInTheEnd == <>(Len(Stack) = 1 /\ NTasksPopped = NTasks)
end define;

macro PushStack(Stack) begin
    Stack := Append(Stack, Len(Stack));
end macro;

macro PopStack(Stack) begin
    Stack := SubSeq(Stack, 1, Len(Stack) - 1);
end macro;

procedure Push()
variables CurrHead;
begin PushBegin:
    await MemoryOrderSeqLock = 0;
    MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
    if Len(Stack) = 1 then
        PushStack(Stack);
        UnlockPush1: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
        return;
    else
        CurrHead := Head(Stack);
    end if;
    UnlockPush2: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
    
PushCASLoop:
    while TRUE do
        await MemoryOrderSeqLock = 0;
        if Len(Stack) = 1 then
            MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
            PushStack(Stack);
            UnlockPush3: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
            return;
        elsif CurrHead = Head(Stack) then
            MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
            PushStack(Stack);
            UnlockPush4: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
            return;
        end if;
    end while;
end procedure;

procedure Pop()
variables CurrHead;
begin PopBegin:
    await MemoryOrderSeqLock = 0;
    MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
    if Len(Stack) = 1 then
        UnlockPop1: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
        goto PopBegin;
    end if;
    PopLoadCurrHead: CurrHead := Head(Stack);
    UnlockPop2: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;

PopCASLoop:
    while TRUE do
        await MemoryOrderSeqLock = 0;
        if Len(Stack) = 1 then
            goto PopCASLoop;
        elsif CurrHead = Head(Stack) then
            MemoryOrderSeqLock := MemoryOrderSeqLock + 1;
            PopStack(Stack);
            UnlockPop3: MemoryOrderSeqLock := MemoryOrderSeqLock - 1;
            return;
        end if;
    end while;
end procedure;

process prod \in Producers begin
Produce:
    while NTasksLeft > 0 do
        NTasksLeft := NTasksLeft - 1;
        call Push();
    end while;
end process;

process cons \in Consumers begin
Consume:
    while NTasksPopped < NTasks do
        NTasksPopped := NTasksPopped + 1;
        await Len(Stack) > 1;
        call Pop();
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e82d8c2b" /\ chksum(tla) = "47c9ab2f")
\* Procedure variable CurrHead of procedure Push at line 31 col 11 changed to CurrHead_
CONSTANT defaultInitValue
VARIABLES Stack, MemoryOrderSeqLock, NTasksLeft, NTasksPopped, pc, stack

(* define statement *)
NoRaceCondition == MemoryOrderSeqLock <= 1
StackIsCorrect == Len(Stack) >= 1

EmptyInTheEnd == <>(Len(Stack) = 1 /\ NTasksPopped = NTasks)

VARIABLES CurrHead_, CurrHead

vars == << Stack, MemoryOrderSeqLock, NTasksLeft, NTasksPopped, pc, stack, 
           CurrHead_, CurrHead >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ Stack = <<0>>
        /\ MemoryOrderSeqLock = 0
        /\ NTasksLeft = NTasks
        /\ NTasksPopped = 0
        (* Procedure Push *)
        /\ CurrHead_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Pop *)
        /\ CurrHead = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "Produce"
                                        [] self \in Consumers -> "Consume"]

PushBegin(self) == /\ pc[self] = "PushBegin"
                   /\ MemoryOrderSeqLock = 0
                   /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                   /\ IF Len(Stack) = 1
                         THEN /\ Stack' = Append(Stack, Len(Stack))
                              /\ pc' = [pc EXCEPT ![self] = "UnlockPush1"]
                              /\ UNCHANGED CurrHead_
                         ELSE /\ CurrHead_' = [CurrHead_ EXCEPT ![self] = Head(Stack)]
                              /\ pc' = [pc EXCEPT ![self] = "UnlockPush2"]
                              /\ Stack' = Stack
                   /\ UNCHANGED << NTasksLeft, NTasksPopped, stack, CurrHead >>

UnlockPush1(self) == /\ pc[self] = "UnlockPush1"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ CurrHead_' = [CurrHead_ EXCEPT ![self] = Head(stack[self]).CurrHead_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, CurrHead >>

UnlockPush2(self) == /\ pc[self] = "UnlockPush2"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = "PushCASLoop"]
                     /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, stack, 
                                     CurrHead_, CurrHead >>

PushCASLoop(self) == /\ pc[self] = "PushCASLoop"
                     /\ MemoryOrderSeqLock = 0
                     /\ IF Len(Stack) = 1
                           THEN /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                                /\ Stack' = Append(Stack, Len(Stack))
                                /\ pc' = [pc EXCEPT ![self] = "UnlockPush3"]
                           ELSE /\ IF CurrHead_[self] = Head(Stack)
                                      THEN /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                                           /\ Stack' = Append(Stack, Len(Stack))
                                           /\ pc' = [pc EXCEPT ![self] = "UnlockPush4"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "PushCASLoop"]
                                           /\ UNCHANGED << Stack, 
                                                           MemoryOrderSeqLock >>
                     /\ UNCHANGED << NTasksLeft, NTasksPopped, stack, 
                                     CurrHead_, CurrHead >>

UnlockPush3(self) == /\ pc[self] = "UnlockPush3"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ CurrHead_' = [CurrHead_ EXCEPT ![self] = Head(stack[self]).CurrHead_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, CurrHead >>

UnlockPush4(self) == /\ pc[self] = "UnlockPush4"
                     /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ CurrHead_' = [CurrHead_ EXCEPT ![self] = Head(stack[self]).CurrHead_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, CurrHead >>

Push(self) == PushBegin(self) \/ UnlockPush1(self) \/ UnlockPush2(self)
                 \/ PushCASLoop(self) \/ UnlockPush3(self)
                 \/ UnlockPush4(self)

PopBegin(self) == /\ pc[self] = "PopBegin"
                  /\ MemoryOrderSeqLock = 0
                  /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                  /\ IF Len(Stack) = 1
                        THEN /\ pc' = [pc EXCEPT ![self] = "UnlockPop1"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "PopLoadCurrHead"]
                  /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, stack, 
                                  CurrHead_, CurrHead >>

UnlockPop1(self) == /\ pc[self] = "UnlockPop1"
                    /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                    /\ pc' = [pc EXCEPT ![self] = "PopBegin"]
                    /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, stack, 
                                    CurrHead_, CurrHead >>

PopLoadCurrHead(self) == /\ pc[self] = "PopLoadCurrHead"
                         /\ CurrHead' = [CurrHead EXCEPT ![self] = Head(Stack)]
                         /\ pc' = [pc EXCEPT ![self] = "UnlockPop2"]
                         /\ UNCHANGED << Stack, MemoryOrderSeqLock, NTasksLeft, 
                                         NTasksPopped, stack, CurrHead_ >>

UnlockPop2(self) == /\ pc[self] = "UnlockPop2"
                    /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                    /\ pc' = [pc EXCEPT ![self] = "PopCASLoop"]
                    /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, stack, 
                                    CurrHead_, CurrHead >>

PopCASLoop(self) == /\ pc[self] = "PopCASLoop"
                    /\ MemoryOrderSeqLock = 0
                    /\ IF Len(Stack) = 1
                          THEN /\ pc' = [pc EXCEPT ![self] = "PopCASLoop"]
                               /\ UNCHANGED << Stack, MemoryOrderSeqLock >>
                          ELSE /\ IF CurrHead[self] = Head(Stack)
                                     THEN /\ MemoryOrderSeqLock' = MemoryOrderSeqLock + 1
                                          /\ Stack' = SubSeq(Stack, 1, Len(Stack) - 1)
                                          /\ pc' = [pc EXCEPT ![self] = "UnlockPop3"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "PopCASLoop"]
                                          /\ UNCHANGED << Stack, 
                                                          MemoryOrderSeqLock >>
                    /\ UNCHANGED << NTasksLeft, NTasksPopped, stack, CurrHead_, 
                                    CurrHead >>

UnlockPop3(self) == /\ pc[self] = "UnlockPop3"
                    /\ MemoryOrderSeqLock' = MemoryOrderSeqLock - 1
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ CurrHead' = [CurrHead EXCEPT ![self] = Head(stack[self]).CurrHead]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << Stack, NTasksLeft, NTasksPopped, CurrHead_ >>

Pop(self) == PopBegin(self) \/ UnlockPop1(self) \/ PopLoadCurrHead(self)
                \/ UnlockPop2(self) \/ PopCASLoop(self) \/ UnlockPop3(self)

Produce(self) == /\ pc[self] = "Produce"
                 /\ IF NTasksLeft > 0
                       THEN /\ NTasksLeft' = NTasksLeft - 1
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Push",
                                                                     pc        |->  "Produce",
                                                                     CurrHead_ |->  CurrHead_[self] ] >>
                                                                 \o stack[self]]
                            /\ CurrHead_' = [CurrHead_ EXCEPT ![self] = defaultInitValue]
                            /\ pc' = [pc EXCEPT ![self] = "PushBegin"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << NTasksLeft, stack, CurrHead_ >>
                 /\ UNCHANGED << Stack, MemoryOrderSeqLock, NTasksPopped, 
                                 CurrHead >>

prod(self) == Produce(self)

Consume(self) == /\ pc[self] = "Consume"
                 /\ IF NTasksPopped < NTasks
                       THEN /\ NTasksPopped' = NTasksPopped + 1
                            /\ Len(Stack) > 1
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Pop",
                                                                     pc        |->  "Consume",
                                                                     CurrHead  |->  CurrHead[self] ] >>
                                                                 \o stack[self]]
                            /\ CurrHead' = [CurrHead EXCEPT ![self] = defaultInitValue]
                            /\ pc' = [pc EXCEPT ![self] = "PopBegin"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << NTasksPopped, stack, CurrHead >>
                 /\ UNCHANGED << Stack, MemoryOrderSeqLock, NTasksLeft, 
                                 CurrHead_ >>

cons(self) == Consume(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Push(self) \/ Pop(self))
           \/ (\E self \in Producers: prod(self))
           \/ (\E self \in Consumers: cons(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
