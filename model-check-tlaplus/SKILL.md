# model-check:tlaplus

Generate and verify TLA+ specifications from state machines, workflows, and protocols.

## When to Use

Use TLA+ when the system has:
- States and transitions
- Concurrency or parallelism
- Temporal properties ("eventually", "always", "never", "leads to")
- Distributed actors or processes
- Resource constraints that change over time

## When NOT to Use

- Pure data modeling with relationships → use Alloy
- Code with pre/post conditions → use Dafny
- Simple linear flows without branching → testing is sufficient

## Installation

**macOS (Homebrew):**
```bash
brew install tlaplus
```

**Verify:**
```bash
tlc -h
```

**Manual installation:**
```bash
# Download tla2tools.jar
curl -L -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Create tlc wrapper
cat > /usr/local/bin/tlc << 'EOF'
#!/bin/bash
java -XX:+UseParallelGC -jar /path/to/tla2tools.jar tlc2.TLC "$@"
EOF
chmod +x /usr/local/bin/tlc
```

Requires Java 11+.

## Generating TLA+ Specs

### Extract from Conversation

| Look for | Maps to |
|----------|---------|
| "starts as", "initial state" | Init predicate |
| "goes to", "transitions to", "becomes" | Actions |
| "can", "may", "either...or" | Non-deterministic choice |
| "never", "must not" | Safety invariant |
| "eventually", "must happen" | Liveness property |
| "always", "at all times" | Invariant |
| "if X then eventually Y" | Leads-to property |

### Spec Structure

```tla
--------------------------- MODULE Name ---------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxValue    \* Bound for model checking

VARIABLES
    state,      \* Current state
    data        \* Other state variables

vars == <<state, data>>

TypeOK ==
    /\ state \in {"State1", "State2", "State3"}
    /\ data \in 0..MaxValue

Init ==
    /\ state = "State1"
    /\ data = 0

Action1 ==
    /\ state = "State1"
    /\ state' = "State2"
    /\ data' = data + 1

Action2 ==
    /\ state = "State2"
    /\ \/ /\ data > 0
          /\ state' = "State3"
       \/ /\ data = 0
          /\ state' = "State1"
    /\ UNCHANGED data

Terminated ==
    /\ state = "State3"
    /\ UNCHANGED vars

Next == Action1 \/ Action2 \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: what must always be true
Safety == data >= 0

\* Liveness: what must eventually happen
Liveness == <>(state = "State3")

=============================================================================
```

### Config File

Always generate a `.cfg` file:

```
SPECIFICATION Spec

CONSTANTS
    MaxValue = 10

INVARIANTS
    TypeOK
    Safety

PROPERTIES
    Liveness
```

## Running TLC

```bash
tlc -workers auto -config Name.cfg Name.tla
```

**Flags:**
- `-workers auto` — Use all CPU cores
- `-deadlock` — Allow deadlock (don't treat as error)
- `-depth N` — Limit search depth

## Interpreting Output

**Success:**
```
Model checking completed. No error has been found.
N states generated, M distinct states found.
```

**Invariant violation:**
```
Error: Invariant Safety is violated.
Error: The following behavior constitutes a counterexample:

State 1: ...
State 2: ...
```

→ Extract the state trace. Explain each step. Identify where the invariant breaks.

**Liveness violation:**
```
Error: Temporal properties were violated.
Error: The following behavior constitutes a counterexample:
...
Error: Stuttering
```

→ System gets stuck. Identify the cycle. Explain why progress isn't being made.

**Deadlock:**
```
Error: Deadlock reached.
```

→ No actions are enabled. Show the terminal state. Explain what's blocked.

## Common Patterns

### Mutual Exclusion
```tla
MutualExclusion == ~(pc[1] = "critical" /\ pc[2] = "critical")
```

### Termination
```tla
Termination == <>(state = "Done")
```

### No Starvation
```tla
NoStarvation == \A p \in Processes: (pc[p] = "waiting") ~> (pc[p] = "critical")
```

### Budget/Resource Exhaustion
```tla
BudgetRespected == budget >= 0
```

### Progress
```tla
Progress == [](state = "Working" => <>(state \in {"Done", "Failed"}))
```

## Presenting Results

Always translate TLA+ output into plain English:

**Bad:** "Invariant TypeOK violated at state 7"

**Good:** 
```
The system can reach an invalid state.

Path to failure:
1. Started in Idle with budget=100
2. Processed request, budget=50
3. Processed another request, budget=0  
4. Tried to process again → budget=-50 ← INVALID

The system allows processing even when budget is exhausted.
Fix: Add guard `budget >= cost` to the Process action.
```
