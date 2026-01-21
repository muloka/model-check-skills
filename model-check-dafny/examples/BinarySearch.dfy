/*
 * Binary Search with Verification
 * 
 * Demonstrates pre/post conditions and loop invariants.
 * 
 * Run with: dafny verify BinarySearch.dfy
 */

// Predicate: sequence is sorted
predicate Sorted(a: seq<int>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Predicate: element exists in sequence
predicate Contains(a: seq<int>, key: int)
{
    exists i :: 0 <= i < |a| && a[i] == key
}

// Binary search: returns index if found, -1 if not found
method BinarySearch(a: seq<int>, key: int) returns (index: int)
    requires Sorted(a)
    ensures index >= 0 ==> 0 <= index < |a| && a[index] == key
    ensures index == -1 ==> !Contains(a, key)
{
    if |a| == 0 {
        return -1;
    }
    
    var lo := 0;
    var hi := |a|;
    
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

// Example usage (run with: dafny run BinarySearch.dfy)
method Main()
{
    var arr := [1, 3, 5, 7, 9, 11, 13];
    var idx := BinarySearch(arr, 7);
    if idx >= 0 {
        print "Found 7 at index ", idx, "\n";
    } else {
        print "7 not found\n";
    }
}
