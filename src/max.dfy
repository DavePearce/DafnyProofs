/**
 * An example proof for the classic algorithm which finds the maximum 
 * element of a non-empty array. 
 * 
 * @author David J Pearce, Feb 2020
 */
 method max(items:array<int>) returns (m:int)
 // Input array cannot be empty.
 requires items.Length > 0
 // Item returned must be in original array.
 ensures exists k :: 0 <= k < items.Length && items[k] == m
 // Item returned cannot be smaller than any item in array
 ensures forall k :: 0 <= k < items.Length ==> items[k] <= m {
     // Initialise with first element
     m := items[0];
     // Iterate remainder
     var i := 1;
     //
     while i < items.Length 
     decreases items.Length - i
     // i is never negative
     invariant i >= 0 && i <= items.Length
     // Candidate is one of elements seen so far
     invariant exists k :: 0 <= k < i && items[k] == m 
     // Candidate above every element seen so far
     invariant forall k :: 0 <= k < i ==> items[k] <= m {
         if items[i] > m {
             m := items[i];
         }
         i := i + 1;
     }
     return m;
 }