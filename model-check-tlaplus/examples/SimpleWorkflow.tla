--------------------------- MODULE SimpleWorkflow ---------------------------
(*
 * Simple Approval Workflow
 * 
 * Demonstrates a basic state machine:
 *   Pending → Approved or Rejected
 *   Approved → Revoked (within time limit)
 *
 * Run with: tlc -config SimpleWorkflow.cfg SimpleWorkflow.tla
 *)

EXTENDS Integers

CONSTANTS
    MaxTime         \* Time limit for revocation

VARIABLES
    state,          \* Current workflow state
    time            \* Time elapsed since approval

vars == <<state, time>>

States == {"Pending", "Approved", "Rejected", "Revoked"}

TypeOK ==
    /\ state \in States
    /\ time \in 0..MaxTime+1

Init ==
    /\ state = "Pending"
    /\ time = 0

Approve ==
    /\ state = "Pending"
    /\ state' = "Approved"
    /\ time' = 0

Reject ==
    /\ state = "Pending"
    /\ state' = "Rejected"
    /\ UNCHANGED time

Revoke ==
    /\ state = "Approved"
    /\ time <= MaxTime
    /\ state' = "Revoked"
    /\ UNCHANGED time

Tick ==
    /\ state = "Approved"
    /\ time < MaxTime + 1
    /\ time' = time + 1
    /\ UNCHANGED state

Terminated ==
    /\ state \in {"Rejected", "Revoked"}
    /\ UNCHANGED vars

\* After revocation window, approval becomes final
Final ==
    /\ state = "Approved"
    /\ time > MaxTime
    /\ UNCHANGED vars

Next == Approve \/ Reject \/ Revoke \/ Tick \/ Terminated \/ Final

Fairness == WF_vars(Approve \/ Reject) /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* PROPERTIES *)

\* Safety: Can't be both approved and rejected
NeverApprovedAndRejected == ~(state = "Approved" /\ state = "Rejected")

\* Safety: Revocation only possible within time limit
RevocationRespected == state = "Revoked" => time <= MaxTime

\* Liveness: Pending requests eventually get decided
EventuallyDecided == <>(state # "Pending")

\* Liveness: System eventually reaches a final state
EventuallyFinal == <>(state \in {"Rejected", "Revoked"} \/ (state = "Approved" /\ time > MaxTime))

=============================================================================
