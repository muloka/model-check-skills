# model-check:alloy

Generate and verify Alloy specifications from data models, taxonomies, and relational constraints.

## When to Use

Use Alloy when the system has:
- Entities and relationships
- Set constraints ("every X has at least one Y")
- Taxonomies or classifications
- Structural invariants
- Relational queries to validate

## When NOT to Use

- Temporal properties, state transitions → use TLA+
- Code with pre/post conditions → use Dafny
- Dynamic behavior over time → use TLA+

Alloy is for *structure*, not *behavior*.

## Installation

**macOS (Homebrew):**
```bash
brew install alloy
```

**Verify:**
```bash
alloy --help
```

**Manual installation:**
```bash
# Download jar (requires Java 11+)
curl -L -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar

# Create wrapper script
cat > /usr/local/bin/alloy << 'EOF'
#!/bin/bash
java -jar /path/to/alloy.jar "$@"
EOF
chmod +x /usr/local/bin/alloy
```

## Running Alloy

```bash
alloy exec Model.als
```

Output format:
```
00. check AssertionName     UNSAT    ← No counterexample (assertion holds)
01. check OtherAssertion    SAT      ← Counterexample found (assertion violated)
02. run   ExampleInstance   SAT      ← Instance found
```

- `UNSAT` on a `check` = good (no counterexample)
- `SAT` on a `check` = bad (counterexample exists)
- `SAT` on a `run` = good (valid instance exists)

## Generating Alloy Specs

### Extract from Conversation

| Look for | Maps to |
|----------|---------|
| "there are", "entities", "types" | `sig` declarations |
| "has", "contains", "belongs to" | Relations (fields) |
| "exactly one", "at most one" | `one` multiplicity |
| "at least one", "one or more" | `some` multiplicity |
| "zero or more", "any number" | `set` multiplicity |
| "every X has Y" | `fact` with `all` quantifier |
| "no X can be Y" | `fact` with negation |
| "X should imply Y" | `assert` |
| "is a kind of", "subtype" | `extends` |

### Spec Structure

```alloy
module Name

--------------------------------------------------------------------------------
-- SIGNATURES (entities)
--------------------------------------------------------------------------------

abstract sig Entity {}

sig ConcreteEntity extends Entity {
    relation: set OtherEntity,
    singleRef: one AnotherEntity
}

sig OtherEntity {}
sig AnotherEntity {}

--------------------------------------------------------------------------------
-- FACTS (constraints that always hold)
--------------------------------------------------------------------------------

fact NoSelfReference {
    no e: ConcreteEntity | e in e.relation
}

fact AtLeastOneRelation {
    all e: ConcreteEntity | some e.relation
}

--------------------------------------------------------------------------------
-- ASSERTIONS (properties to verify)
--------------------------------------------------------------------------------

assert PropertyName {
    all e: ConcreteEntity | e.singleRef not in e.relation
}

--------------------------------------------------------------------------------
-- COMMANDS
--------------------------------------------------------------------------------

check PropertyName for 5
run ShowExample {} for 3
```

### Multiplicity Reference

| Alloy | Meaning |
|-------|---------|
| `one` | Exactly one |
| `lone` | Zero or one |
| `some` | One or more |
| `set` | Zero or more |

### Relation Syntax

```alloy
sig Person {
    spouse: lone Person,      -- 0 or 1
    parents: set Person,      -- 0 or more  
    employer: one Company,    -- exactly 1
    friends: some Person      -- 1 or more
}
```

## Common Patterns

### Mutual Exclusion (Categories)
```alloy
abstract sig Category {}
one sig A, B, C extends Category {}

sig Item {
    category: one Category
}

-- Item belongs to exactly one category (enforced by `one`)
```

### Taxonomy Completeness
```alloy
abstract sig BlameCategory {}
one sig Positive, Negative, Temporal, Structural, Authority extends BlameCategory {}

assert FiveCategoriesExist {
    #BlameCategory = 5
}
check FiveCategoriesExist for 5
```

### Referential Integrity
```alloy
sig Department {
    employees: set Employee
}

sig Employee {
    department: one Department
}

fact Consistency {
    all e: Employee, d: Department | 
        e in d.employees <=> e.department = d
}
```

### Acyclic Relations
```alloy
sig Node {
    children: set Node
}

fact Acyclic {
    no n: Node | n in n.^children  -- no cycles via transitive closure
}
```

### Unique Identifiers
```alloy
sig Entity {
    id: one ID
}

sig ID {}

fact UniqueIDs {
    all disj e1, e2: Entity | e1.id != e2.id
}
```

## Interpreting Output

**All checks pass:**
```
check AssertionName    UNSAT
```
→ "No counterexample found — the assertion holds for all instances up to scope 5."

**Check fails:**
```
check AssertionName    SAT
```
→ Counterexample exists. Run in GUI to visualize, or add a `run` to see instances.

**Run succeeds:**
```
run Example    SAT
```
→ Valid instance exists. The model is satisfiable.

**Run fails:**
```
run Example    UNSAT
```
→ No valid instances exist. Constraints may be too tight or contradictory.

## Presenting Results

**Success:**
```
✓ All assertions verified

Alloy checked 3 assertions against all instances up to scope 5.
No counterexamples found.

Verified properties:
- CategoryCompleteness: every failure maps to exactly one category
- EveryFailureHasFix: every category has a fix strategy
- DistinctFixStrategies: no two categories share the same fix
```

**Counterexample found:**
```
✗ Assertion violated: UniqueIDs

Alloy found a counterexample:

  Entity1 { id: ID_0 }
  Entity2 { id: ID_0 }  ← Same ID as Entity1

Two entities share the same identifier, violating uniqueness.

Fix: Add a fact enforcing distinct IDs:
  fact { all disj e1, e2: Entity | e1.id != e2.id }
```

**Unsatisfiable model:**
```
✗ No valid instances exist

The constraints are contradictory. For example:
- Fact 1 requires: all X have at least one Y
- Fact 2 requires: no Y exist

These cannot both be true. Review the constraints for conflicts.
```

## Tips

1. **Start with small scope** — `for 3` is often enough to find bugs
2. **Use `run` to sanity check** — make sure valid instances exist before checking assertions
3. **Name your facts** — makes debugging easier
4. **One assertion per property** — easier to isolate failures
5. **Use `disj` for distinctness** — `all disj x, y: Sig` means x ≠ y
