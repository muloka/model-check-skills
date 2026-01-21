# Example Outputs

This folder contains sample verification outputs from each tool.

## TLA+ (TLC) — Success

```
$ tlc -workers auto -config SimpleWorkflow.cfg SimpleWorkflow.tla

TLC2 Version 2.19 of 08 August 2024
Running breadth-first search Model-Checking with 10 workers.
Parsing file SimpleWorkflow.tla
Semantic processing of module SimpleWorkflow
Starting... (2025-01-21 10:30:45)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Checking temporal properties for the complete state space with 24 total distinct states
Model checking completed. No error has been found.
24 states generated, 24 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
Finished in 01s at (2025-01-21 10:30:46)
```

## TLA+ (TLC) — Counterexample

```
$ tlc -workers auto -config Buggy.cfg Buggy.tla

Error: Invariant BudgetRespected is violated.
Error: The following behavior constitutes a counterexample:

State 1: <Initial>
/\ state = "Idle"
/\ budget = 100

State 2:
/\ state = "Processing"
/\ budget = 50

State 3:
/\ state = "Processing"
/\ budget = 0

State 4:
/\ state = "Processing"
/\ budget = -50      << INVARIANT VIOLATED

Error: Invariant BudgetRespected is violated.
```

## Alloy — Success

```
$ alloy exec OrgStructure.als

00. check SingleOrg             UNSAT
01. check AdminBelongsToOrg     UNSAT
02. check MembersImpliesAdmin   UNSAT
03. check NoOrphanUsers         UNSAT
04. run   ShowSmallOrg          SAT
05. run   ShowMultipleOrgs      SAT
```

## Alloy — Counterexample

```
$ alloy exec Buggy.als

00. check UniqueIDs             SAT    << COUNTEREXAMPLE FOUND

Instance found:
  Entity0 { id: ID0 }
  Entity1 { id: ID0 }   << Same ID!
```

## Dafny — Success

```
$ dafny verify BinarySearch.dfy

Dafny program verifier finished with 4 verified, 0 errors
```

## Dafny — Failure

```
$ dafny verify Buggy.dfy

Buggy.dfy(15,4): Error: a postcondition could not be proved on this return path
   |
15 |     ensures result >= 0
   |     ^^^^^^^^^^^^^^^^^^^^

Buggy.dfy(23,8): Related location: this is the postcondition that could not be proved

Dafny program verifier finished with 0 verified, 1 error
```
