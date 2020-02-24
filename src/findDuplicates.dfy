/**
 * A simple proof that given an array of at least n+1 elements in the 
 * range 1..n (inclusive) there must be at least one duplicate.  This 
 * is a classic interview question!
 * @author David J .Pearce, Feb 2020
 */

/**
 * Holds if a duplicate exists in a given array starting from a given 
 * position in that array.
 */
predicate dup(a: array<int>, n: int) 
requires n >= 0
reads a {
    exists i,j :: n <= i < j < a.Length && a[i] == a[j]
}

/**
 * Holds if a given element occurs more than once in the given array 
 * (i.e. that element is a duplicate of the array).
 */
predicate dupOf(a: array<int>, v: int) 
reads a {
    exists i,j :: 0 <= i < j < a.Length && a[i] == v && a[j] == v
}

lemma lemma_pigeonhole(a: seq<int>, n:int) 
// At least n+1 elements are given
requires 0 < n < |a|
// All elements between one and n (inclusive)
requires forall k :: 0 <= k < |a| ==> (1 <= a[k] <= n)
// At least n is contained 
ensures n in a {
    if n == 1 {
        // Base case
        assert a[0] == n;
    } else if a[0] != n {
        // Inductivee case
        lemma_pigeonhole(a[1..],n);
    }
}

lemma lemma_dup(a: array<int>, n:int) 
// At least n+1 elements are given
requires 0 < n < a.Length 
// All elements between one and n (inclusive)
requires forall k :: 0 <= k < a.Length ==> (1 <= a[k] <= n) 
// 
ensures dup(a,0) {
    //
    if n == 1 {
       // Base case
       assert a[0] == 1;
       assert a[1] == 1;
    } else if dupOf(a,n) {
       // Simple case
    } else {
        // Inductive case
        //assert contains(a,n);
        //a = removeAll(a,n);
    }
}

method removeAll(a: array<int>, v: int) {

}

/**
 * Given an array which is known to hold one or more duplicates, find 
 * a pair of duplicate indices.
 */
method findDup(a: array<int>) returns (first: int, second: int)
// A duplicate must exist in the input array
requires dup(a,0)
// Ensuress return values are distinct (but valid) indices
ensures 0 <= first < second < a.Length
// Ensures return values identify duplicate
ensures a[first] == a[second] {
    var i : int := 0;
    
    while i < a.Length 
    decreases (a.Length - i) 
    invariant i >= 0 && dup(a,i) {
        var j : int := i + 1;
        while j < a.Length
        invariant 0 <= i < j <= a.Length
        invariant forall k :: i+1 <= k < j ==> a[i] != a[k]
        decreases (a.Length - j) {
            if a[i] == a[j] {
                return i,j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // Should be impossible to get here, since array originally 
    // contained a duplicate.  Therefore, we must have found something 
    // in the loop above and terminated already.
    assert false;
}