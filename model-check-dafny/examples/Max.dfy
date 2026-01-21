/*
 * Find Maximum Element with Verification
 *
 * Demonstrates array handling and loop invariants.
 *
 * Run with: dafny verify Max.dfy
 */

// Find maximum element in non-empty array
method FindMax(a: array<int>) returns (max: int)
    requires a.Length > 0
    ensures max in a[..]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
{
    max := a[0];
    var i := 1;

    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant max in a[..i]
        invariant forall j :: 0 <= j < i ==> a[j] <= max
    {
        if a[i] > max {
            max := a[i];
        }
        i := i + 1;
    }
}

// Find minimum element in non-empty array
method FindMin(a: array<int>) returns (min: int)
    requires a.Length > 0
    ensures min in a[..]
    ensures forall i :: 0 <= i < a.Length ==> a[i] >= min
{
    min := a[0];
    var i := 1;

    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant min in a[..i]
        invariant forall j :: 0 <= j < i ==> a[j] >= min
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }
}

// Swap two elements in an array
method Swap(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length
    requires 0 <= j < a.Length
    modifies a
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
    ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    var tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
}

// Example usage
method Main()
{
    var a := new int[5][3, 1, 4, 1, 5];
    var max := FindMax(a);
    print "Max: ", max, "\n";

    var min := FindMin(a);
    print "Min: ", min, "\n";
}
