# model-check

Generate and verify formal models from system descriptions in conversation.

## Purpose

This skill extracts formal models from systems described in conversation and verifies them using model checking tools. It generates the specifications automatically — users describe their system in natural language, not TLA+ or Alloy syntax.

## When to Use

Use this skill when the conversation contains:
- State machines or workflows with transitions
- Concurrent or distributed systems
- Protocols with multiple actors
- Data models with relational constraints
- Code with correctness requirements

## When NOT to Use

Decline gracefully if:
- No system is described → "I don't see a state machine, workflow, or formal structure to model. Can you describe what you're building?"
- System is too trivial → "This is a simple linear flow — model checking won't add value here."
- Requirements are ambiguous → "I see a workflow but the transitions aren't clear. What triggers X → Y?"

## Tool Selection (Auto Mode)

| Pattern in Conversation | Tool | Why |
|-------------------------|------|-----|
| States, transitions, concurrency, temporal properties ("eventually", "always", "never") | TLA+ | Best for behavioral/temporal properties |
| Entities, relationships, set constraints, taxonomies, "every X has exactly one Y" | Alloy | Best for structural/relational properties |
| Functions, pre/post conditions, loop invariants, "this function should return..." | Dafny | Best for code verification |
| Unclear | Ask user which aspect they want to verify |

## Workflow

```
1. Analyze conversation for modelable system
2. If nothing found → decline gracefully
3. Select appropriate tool (or ask user)
4. Check if tool is installed
5. If not installed → provide installation instructions, stop
6. Generate specification from system description
7. Run verification
8. Parse results
9. If counterexample found → explain the failure path clearly
10. If verified → report success
11. If verification failed for other reasons → explain and suggest fixes
```

## Installation Check

Before running any tool, verify it's available:

```bash
# TLA+ (TLC)
tlc -h 2>/dev/null || echo "TLA+ not installed"

# Alloy
alloy --help 2>/dev/null || echo "Alloy not installed"

# Dafny
dafny --help 2>/dev/null || echo "Dafny not installed"
```

If the required tool is not installed, provide the appropriate installation instructions below and stop. Do not attempt to generate or verify without the tool.

---

## Installation Instructions

### Dafny (Easiest)

**macOS (Homebrew):**
```bash
brew install dafny
```

**Linux/Windows:**
```bash
# Requires .NET 6.0+ runtime
dotnet tool install --global dafny
```

**Verify installation:**
```bash
dafny --version
```

---

### Alloy

**macOS (Homebrew):**
```bash
brew install alloy
```

**Linux/Windows:**

Download from https://github.com/AlloyTools/org.alloytools.alloy/releases

```bash
# Download the jar
curl -L -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar

# Run with Java (requires Java 11+)
java -jar alloy.jar
```

For CLI usage, create a wrapper script:
```bash
#!/bin/bash
java -jar /path/to/alloy.jar "$@"
```

**Verify installation:**
```bash
alloy --help
# or
java -jar alloy.jar --help
```

**Note:** Alloy's CLI is less mature than its GUI. The `alloy exec` command runs all checks in a file.

---

### TLA+ (TLC)

**Option 1: VS Code Extension (Recommended for beginners)**

Install "TLA+ Nightly" extension in VS Code. Includes TLC.

**Option 2: Homebrew (macOS)**
```bash
brew install tlaplus
```

**Option 3: Manual installation**

Download TLA+ Toolbox from https://github.com/tlaplus/tlaplus/releases

For CLI usage, download `tla2tools.jar`:
```bash
curl -L -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Create wrapper script
echo '#!/bin/bash
java -XX:+UseParallelGC -jar /path/to/tla2tools.jar "$@"' > tlc
chmod +x tlc
sudo mv tlc /usr/local/bin/
```

**Verify installation:**
```bash
tlc -h
```

**Common issues:**
- Requires Java 11+
- On macOS, may need to allow in Security & Privacy settings
- The `tlc` command specifically runs the model checker; `tla2tools.jar` contains multiple tools

---

## Generating Specifications

### From State Machines / Workflows → TLA+

Extract:
- States (as a set)
- Initial state
- Transitions (as actions)
- Invariants ("X should never happen")
- Liveness properties ("Y should eventually happen")

Template:
```tla
---- MODULE SystemName ----
EXTENDS Integers, Sequences

VARIABLES state, ...

Init == state = "Initial" /\ ...

ActionName ==
    /\ state = "FromState"
    /\ state' = "ToState"
    /\ ...

Next == ActionOne \/ ActionTwo \/ ...

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"State1", "State2", ...}

Safety == ...
Liveness == <>(...) 

====
```

### From Data Models / Taxonomies → Alloy

Extract:
- Entities (as signatures)
- Relationships (as relations)
- Constraints ("every X has at least one Y")
- Properties to verify

Template:
```alloy
module SystemName

sig Entity1 {
    relation: set Entity2
}

sig Entity2 {}

fact Constraints {
    all e: Entity1 | some e.relation
}

assert PropertyName {
    ...
}

check PropertyName for 5
run Example {} for 3
```

### From Code → Dafny

Extract:
- Function signatures
- Preconditions (requires)
- Postconditions (ensures)
- Loop invariants

Template:
```dafny
method MethodName(param: Type) returns (result: Type)
    requires precondition
    ensures postcondition
{
    // implementation
}
```

---

## Presenting Results

### Verification Succeeded

```
✓ Model verified

TLC explored [N] states and found no errors.

Properties verified:
- TypeOK: all states have valid types
- Safety: [property description]
- Liveness: [property description]
```

### Counterexample Found

```
✗ Property violated: [PropertyName]

The model checker found a failure path:

State 1 (initial):
  → state = "Idle"
  → budget = 100

State 2:
  → state = "Processing"
  → budget = 50

State 3:
  → state = "Processing"  ← stuck here
  → budget = 0

Problem: The system can reach a state where it's Processing 
but has no budget to continue, causing a deadlock.

Suggested fix: Add a transition from Processing → Failed 
when budget is exhausted.
```

### Nothing to Model

```
I don't see a formal system to model in our conversation.

Model checking is useful for:
- State machines with transitions
- Workflows with branching/concurrency  
- Protocols with multiple actors
- Data models with constraints

Can you describe what you're building?
```

### Too Trivial

```
This looks like a simple linear flow (A → B → C) with no 
branching, loops, or concurrency.

Model checking shines when there are:
- Multiple possible paths
- Concurrent operations
- Resource constraints
- Temporal requirements

For a linear flow, standard testing is sufficient.
```

---

## Examples

### Example 1: Workflow from Conversation

**User says:** "I'm building an approval workflow. Requests start as pending, then go to either approved or rejected. Approved requests can be revoked within 24 hours."

**Skill extracts:**
- States: Pending, Approved, Rejected, Revoked
- Transitions: Pending→Approved, Pending→Rejected, Approved→Revoked (time-bounded)
- Implicit property: No request should be both approved and rejected

**Skill generates:** TLA+ spec with temporal constraint on revocation

---

### Example 2: Data Model from Conversation

**User says:** "Every user belongs to exactly one organization. Organizations have admins, and every org must have at least one admin."

**Skill extracts:**
- Entities: User, Organization, Admin (subset of User)
- Relations: User→Organization (exactly one), Organization→Admin (at least one)

**Skill generates:** Alloy spec with multiplicity constraints

---

### Example 3: No System Found

**User says:** "How do I center a div in CSS?"

**Skill response:** "I don't see a state machine, workflow, or formal structure to model. Model checking is for verifying systems with states and transitions — it won't help with CSS layout. Is there something else you're working on that involves workflows or state management?"

---

## Tool-Specific Variants

If the user invokes a specific variant:

- `/model-check-tlaplus` — Skip tool selection, use TLA+
- `/model-check-alloy` — Skip tool selection, use Alloy
- `/model-check-dafny` — Skip tool selection, use Dafny

Still check installation and decline gracefully if nothing to model.
