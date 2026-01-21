# model-check:dafny

Generate and verify Dafny specifications from code with correctness requirements.

## When to Use

Use Dafny when:
- Functions have preconditions and postconditions
- Loops need invariants
- Data structures have representation invariants
- Algorithms need correctness proofs
- Code has "should return X when given Y" requirements

## When NOT to Use

- State machines, workflows → use TLA+
- Data models with relationships → use Alloy
- Concurrent/distributed systems → use TLA+

Dafny is for *sequential code correctness*, not system-level behavior.

## Installation

**macOS/Linux/Windows:**
```bash
# Requires .NET 6.0+
dotnet tool install --global dafny
```

**Verify:**
```bash
dafny --version
```

**Alternative (macOS Homebrew):**
```bash
brew install dafny
```

Dafny is the easiest of the three tools to install.

## Running Dafny

```bash
dafny verify Program.dfy
```

Output:
```
Dafny program verifier finished with 3 verified, 0 errors
```

Or on failure:
```
Program.dfy(15,4): Error: postcondition might not hold
```

## Generating Dafny Specs

### Extract from Conversation

| Look for | Maps to |
|----------|---------|
| "given X, returns Y" | Method with ensures |
| "assumes", "input must be" | requires (precondition) |
| "guarantees", "output will be" | ensures (postcondition) |
| "loop until", "iterate" | Loop with invariant |
| "sorted", "unique", "positive" | Predicates |
| "pure function", "no side effects" | function (vs method) |

### Spec Structure

```dafny
// Predicates for common properties
predicate Sorted(a: seq<int>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate HasElement(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}

// Method with pre/post conditions
method BinarySearch(a: seq<int>, key: int) returns (index: int)
    requires Sorted(a)
    ensures index >= 0 ==> 0 <= index < |a| && a[index] == key
    ensures index < 0 ==> !HasElement(a, key)
{
    var lo, hi := 0, |a|;
    
    while lo < hi
        invariant 0 <= lo <= hi <= |a|
        invariant forall i :: 0 <= i < lo ==> a[i] < key
        invariant forall i :: hi <= i < |a| ==> a[i] > key
    {
        var mid := (lo + hi) / 2;
        if a[mid] < key {
            lo := mid + 1;
        } else if a[mid] > key {
            hi := mid;
        } else {
            return mid;
        }
    }
    return -1;
}
```

### Functions vs Methods

```dafny
// Pure function - no side effects, can be used in specs
function Sum(a: seq<int>): int
{
    if |a| == 0 then 0 else a[0] + Sum(a[1..])
}

// Method - can have side effects, imperative
method ComputeSum(a: seq<int>) returns (s: int)
    ensures s == Sum(a)
{
    s := 0;
    for i := 0 to |a|
        invariant s == Sum(a[..i])
    {
        s := s + a[i];
    }
}
```

## Common Patterns

### Array Bounds
```dafny
method Access(a: array<int>, i: int) returns (v: int)
    requires 0 <= i < a.Length
    ensures v == a[i]
{
    v := a[i];
}
```

### Loop Invariant for Sum
```dafny
method Sum(a: array<int>) returns (s: int)
    ensures s == SumSeq(a[..])
{
    s := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant s == SumSeq(a[..i])
    {
        s := s + a[i];
        i := i + 1;
    }
}
```

### Result is in Input
```dafny
method Max(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures m in a[..]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
{
    m := a[0];
    for i := 1 to a.Length
        invariant m in a[..i]
        invariant forall j :: 0 <= j < i ==> a[j] <= m
    {
        if a[i] > m {
            m := a[i];
        }
    }
}
```

### Modifies Clause
```dafny
method Swap(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
    ensures a[i] == old(a[j]) && a[j] == old(a[i])
    ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    var tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
}
```

### Termination (Decreases)
```dafny
method Countdown(n: nat)
    decreases n
{
    if n > 0 {
        print n, "\n";
        Countdown(n - 1);
    }
}
```

## Interpreting Output

**Success:**
```
Dafny program verifier finished with 5 verified, 0 errors
```
→ All methods and functions verify. Pre/post conditions are satisfied.

**Precondition failure:**
```
Error: precondition might not hold
    requires x > 0
```
→ Caller doesn't guarantee the precondition. Add checks before call.

**Postcondition failure:**
```
Error: postcondition might not hold
    ensures result >= 0
```
→ Method body doesn't guarantee the postcondition. Fix implementation or weaken postcondition.

**Loop invariant failure (entry):**
```
Error: loop invariant might not hold on entry
```
→ Invariant isn't established before the loop starts.

**Loop invariant failure (maintenance):**
```
Error: loop invariant might not be maintained
```
→ Loop body breaks the invariant. Fix the body or strengthen the invariant.

**Termination failure:**
```
Error: cannot prove termination
```
→ Add a `decreases` clause showing what gets smaller each iteration.

## Presenting Results

**Success:**
```
✓ All methods verified

Dafny proved:
- BinarySearch: returns correct index when element exists
- BinarySearch: returns -1 when element not found  
- BinarySearch: terminates on all inputs

The implementation matches its specification.
```

**Postcondition failure:**
```
✗ Verification failed: ComputeMax

Error at line 15:
    ensures result >= 0

The method might return a negative value.

Example: if input array is [-5, -3, -1], the maximum is -1, 
which violates `result >= 0`.

Fix options:
1. Weaken postcondition: ensures forall i :: 0 <= i < a.Length ==> result >= a[i]
2. Strengthen precondition: requires forall i :: 0 <= i < a.Length ==> a[i] >= 0
```

**Loop invariant failure:**
```
✗ Verification failed: Sum

Error at line 12:
    invariant s == SumSeq(a[..i])
    
Loop invariant might not be maintained.

The invariant holds before the loop, but after executing the body
with i=2, the verifier can't prove s still equals SumSeq(a[..i]).

Check: Is the loop body updating both s and i correctly?
Current body updates s before incrementing i — this breaks the invariant.

Fix: Update i after the invariant-dependent computation:
    s := s + a[i];
    i := i + 1;  // not the other way around
```

## Tips

1. **Start with postconditions** — what should be true when the method returns?
2. **Add preconditions as needed** — what must be true for the method to work?
3. **Loop invariants are the hard part** — they must be true before, during, and after
4. **Use `assert` to debug** — `assert P;` helps locate where proofs fail
5. **Predicates simplify specs** — extract common properties into named predicates
6. **`old()` for before/after** — `old(x)` refers to x's value at method entry
