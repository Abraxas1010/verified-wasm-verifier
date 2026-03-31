import HeytingLean.LeanCP.Bench.ScalarArithmetic
import HeytingLean.LeanCP.Examples.BinarySearch
import HeytingLean.LeanCP.Examples.FreeList
import HeytingLean.LeanCP.Examples.ListMerge
import HeytingLean.LeanCP.Examples.ListReverse
import HeytingLean.LeanCP.Examples.Strlen
import HeytingLean.LeanCP.Examples.Swap
import HeytingLean.LeanCP.Examples.TreeInsert
import HeytingLean.LeanCP.Examples.ArraySumVerified
import HeytingLean.LeanCP.Examples.BinarySearchVerified
import HeytingLean.LeanCP.Examples.BlockScopeVerified
import HeytingLean.LeanCP.Examples.CallerVerified
import HeytingLean.LeanCP.Examples.CountdownVerified
import HeytingLean.LeanCP.Examples.FactorialVerified
import HeytingLean.LeanCP.Examples.FreeListVerified
import HeytingLean.LeanCP.Examples.HashTableVerified
import HeytingLean.LeanCP.Examples.IncrementVerified
import HeytingLean.LeanCP.Examples.InsertionSortVerified
import HeytingLean.LeanCP.Examples.ListMergeVerified
import HeytingLean.LeanCP.Examples.ListReverseVerified
import HeytingLean.LeanCP.Examples.MaxVerified
import HeytingLean.LeanCP.Examples.MutualRecursionVerified
import HeytingLean.LeanCP.Examples.StackVerified
import HeytingLean.LeanCP.Examples.StrlenVerified
import HeytingLean.LeanCP.Examples.SwapVerified
import HeytingLean.LeanCP.Examples.TreeInsertVerified
import HeytingLean.LeanCP.Examples.TwoSumVerified

namespace HeytingLean.LeanCP.Bench

def mkEntry
    (id moduleName : String)
    (domain : BenchDomain)
    (theoremDecl programDecl : Lean.Name)
    (proofKind : BenchProofKind)
    (generality : BenchGenerality) : BenchEntry :=
  { id := id
  , domain := domain
  , moduleName := moduleName
  , theoremDecl := theoremDecl
  , programDecl := programDecl
  , entryKind := "topLevel"
  , proofKind := proofKind
  , generality := generality
  , usesAnnotations := false
  , countsTowardPhase8 := true }

def existingSeedEntries : List BenchEntry :=
  [ mkEntry "max_verified" "HeytingLean.LeanCP.Examples.MaxVerified" .scalarArith
      ``HeytingLean.LeanCP.Examples.max_verified
      ``HeytingLean.LeanCP.Examples.maxBody .symbolic .parametric
  , mkEntry "max_executes" "HeytingLean.LeanCP.Examples.MaxVerified" .scalarArith
      ``HeytingLean.LeanCP.Examples.max_executes
      ``HeytingLean.LeanCP.Examples.maxBody .operational .concreteOperational
  , mkEntry "twoSum_verified" "HeytingLean.LeanCP.Examples.TwoSumVerified" .scalarArith
      ``HeytingLean.LeanCP.Examples.twoSum_verified
      ``HeytingLean.LeanCP.Examples.twoSumVerifiedBody .symbolic .parametric
  , mkEntry "twoSum_executes" "HeytingLean.LeanCP.Examples.TwoSumVerified" .scalarArith
      ``HeytingLean.LeanCP.Examples.twoSum_executes
      ``HeytingLean.LeanCP.Examples.twoSumVerifiedBody .operational .concreteOperational

  , mkEntry "arraySum_correct" "HeytingLean.LeanCP.Examples.ArraySumVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.arraySum_correct
      ``HeytingLean.LeanCP.Examples.arraySumProgram .invariant .familyGeneric
  , mkEntry "binarySearch_correct" "HeytingLean.LeanCP.Examples.BinarySearchVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.binarySearch_correct
      ``HeytingLean.LeanCP.Examples.binarySearchBody .invariant .familyGeneric
  , mkEntry "binarySearch_executes" "HeytingLean.LeanCP.Examples.BinarySearchVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.binarySearch_executes
      ``HeytingLean.LeanCP.Examples.binarySearchBody .operational .concreteOperational
  , mkEntry "binarySearch_init_verified" "HeytingLean.LeanCP.Examples.BinarySearchVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.binarySearch_init_verified
      ``HeytingLean.LeanCP.Examples.binarySearchBody .symbolic .concreteOperational
  , mkEntry "insertionSort_correct" "HeytingLean.LeanCP.Examples.InsertionSortVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.insertionSort_correct
      ``HeytingLean.LeanCP.Examples.insertionSortBody .invariant .familyGeneric
  , mkEntry "insertionSort_executes" "HeytingLean.LeanCP.Examples.InsertionSortVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.insertionSort_executes
      ``HeytingLean.LeanCP.Examples.insertionSortBody .operational .concreteOperational
  , mkEntry "insertionSort_verified" "HeytingLean.LeanCP.Examples.InsertionSortVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.insertionSort_verified
      ``HeytingLean.LeanCP.Examples.insertionSortBody .symbolic .concreteOperational
  , mkEntry "insertionSort_forward_verified" "HeytingLean.LeanCP.Examples.InsertionSortVerified" .arraySearchSort
      ``HeytingLean.LeanCP.Examples.insertionSort_forward_verified
      ``HeytingLean.LeanCP.Examples.insertionSortBody .callAware .concreteOperational

  , mkEntry "listRev_correct" "HeytingLean.LeanCP.Examples.ListReverseVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.listRev_correct
      ``HeytingLean.LeanCP.Examples.listReverseBody .invariant .familyGeneric
  , mkEntry "merge_correct" "HeytingLean.LeanCP.Examples.ListMergeVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.merge_correct
      ``HeytingLean.LeanCP.Examples.mergeBody .symbolic .familyGeneric
  , mkEntry "merge_executes" "HeytingLean.LeanCP.Examples.ListMergeVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.merge_executes
      ``HeytingLean.LeanCP.Examples.mergeBody .operational .concreteOperational
  , mkEntry "freeList_correct" "HeytingLean.LeanCP.Examples.FreeListVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.freeList_correct
      ``HeytingLean.LeanCP.Examples.freeListBody .invariant .familyGeneric
  , mkEntry "freeList_executes" "HeytingLean.LeanCP.Examples.FreeListVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.freeList_executes
      ``HeytingLean.LeanCP.Examples.freeListBody .operational .concreteOperational
  , mkEntry "stackPushPop_correct" "HeytingLean.LeanCP.Examples.StackVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.stackPushPop_correct
      ``HeytingLean.LeanCP.Examples.stackPushPopBody .invariant .familyGeneric
  , mkEntry "stackPushPop_executes_from_state" "HeytingLean.LeanCP.Examples.StackVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.stackPushPop_executes_from_state
      ``HeytingLean.LeanCP.Examples.stackPushPopBody .operational .parametric
  , mkEntry "stackPushPop_executes" "HeytingLean.LeanCP.Examples.StackVerified" .linkedHeap
      ``HeytingLean.LeanCP.Examples.stackPushPop_executes
      ``HeytingLean.LeanCP.Examples.stackPushPopBody .operational .concreteOperational

  , mkEntry "treeInsert_base_executes_from_state" "HeytingLean.LeanCP.Examples.TreeInsertVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.treeInsert_base_executes_from_state
      ``HeytingLean.LeanCP.Examples.bstInsertBaseCase .operational .parametric
  , mkEntry "treeInsert_correct" "HeytingLean.LeanCP.Examples.TreeInsertVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.treeInsert_correct
      ``HeytingLean.LeanCP.Examples.bstInsertBaseCase .symbolic .familyGeneric
  , mkEntry "treeInsert_executes" "HeytingLean.LeanCP.Examples.TreeInsertVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.treeInsert_executes
      ``HeytingLean.LeanCP.Examples.bstInsertBaseCase .operational .concreteOperational
  , mkEntry "treeInsert_forward_verified" "HeytingLean.LeanCP.Examples.TreeInsertVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.treeInsert_forward_verified
      ``HeytingLean.LeanCP.Examples.bstInsertBaseCase .callAware .concreteOperational
  , mkEntry "hashInsert_executes_from_state" "HeytingLean.LeanCP.Examples.HashTableVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.hashInsert_executes_from_state
      ``HeytingLean.LeanCP.Examples.hashInsertBody .operational .parametric
  , mkEntry "hashInsert_correct" "HeytingLean.LeanCP.Examples.HashTableVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.hashInsert_correct
      ``HeytingLean.LeanCP.Examples.hashInsertBody .symbolic .familyGeneric
  , mkEntry "hashTable_executes" "HeytingLean.LeanCP.Examples.HashTableVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.hashTable_executes
      ``HeytingLean.LeanCP.Examples.hashInsertBody .operational .concreteOperational
  , mkEntry "hashTable_forward_verified" "HeytingLean.LeanCP.Examples.HashTableVerified" .treeHash
      ``HeytingLean.LeanCP.Examples.hashTable_forward_verified
      ``HeytingLean.LeanCP.Examples.hashInsertBody .callAware .concreteOperational

  , mkEntry "blockAdd_verified" "HeytingLean.LeanCP.Examples.BlockScopeVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.blockAdd_verified
      ``HeytingLean.LeanCP.Examples.blockAddProgram .symbolic .parametric
  , mkEntry "blockAdd_executes" "HeytingLean.LeanCP.Examples.BlockScopeVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.blockAdd_executes
      ``HeytingLean.LeanCP.Examples.blockAddProgram .operational .concreteOperational
  , mkEntry "countdown_verified" "HeytingLean.LeanCP.Examples.CountdownVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.countdown_verified
      ``HeytingLean.LeanCP.Examples.countdownBody .invariant .concreteOperational
  , mkEntry "countdown_executes" "HeytingLean.LeanCP.Examples.CountdownVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.countdown_executes
      ``HeytingLean.LeanCP.Examples.countdownProgram .operational .concreteOperational
  , mkEntry "callerFunEnv_sound" "HeytingLean.LeanCP.Examples.CallerVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.callerFunEnv_sound
      ``HeytingLean.LeanCP.Examples.callerBody .callAware .parametric
  , mkEntry "caller_executes" "HeytingLean.LeanCP.Examples.CallerVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.caller_executes
      ``HeytingLean.LeanCP.Examples.callerBody .operational .parametric
  , mkEntry "factorial_executes" "HeytingLean.LeanCP.Examples.FactorialVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.factorial_executes
      ``HeytingLean.LeanCP.Examples.factorialBody .recursive .parametric
  , mkEntry "mutual_recursion_executes" "HeytingLean.LeanCP.Examples.MutualRecursionVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.mutual_recursion_executes
      ``HeytingLean.LeanCP.Examples.isEvenBody .recursive .concreteOperational
  , mkEntry "isEven_executes" "HeytingLean.LeanCP.Examples.MutualRecursionVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.isEven_executes
      ``HeytingLean.LeanCP.Examples.isEvenBody .recursive .parametric
  , mkEntry "isOdd_executes" "HeytingLean.LeanCP.Examples.MutualRecursionVerified" .callsControlRec
      ``HeytingLean.LeanCP.Examples.isOdd_executes
      ``HeytingLean.LeanCP.Examples.isOddBody .recursive .parametric

  , mkEntry "incr_verified" "HeytingLean.LeanCP.Examples.IncrementVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.incr_verified
      ``HeytingLean.LeanCP.Examples.incrBody .symbolic .parametric
  , mkEntry "incr_executes" "HeytingLean.LeanCP.Examples.IncrementVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.incr_executes
      ``HeytingLean.LeanCP.Examples.incrBody .operational .concreteOperational
  , mkEntry "caller_increment_executes" "HeytingLean.LeanCP.Examples.CallerVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.increment_executes
      ``HeytingLean.LeanCP.Examples.incrementBody .operational .parametric
  , mkEntry "strlen_correct" "HeytingLean.LeanCP.Examples.StrlenVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.strlen_correct
      ``HeytingLean.LeanCP.Examples.strlenBody .invariant .familyGeneric
  , mkEntry "strlen_executes" "HeytingLean.LeanCP.Examples.StrlenVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.strlen_executes
      ``HeytingLean.LeanCP.Examples.strlenBody .operational .concreteOperational
  , mkEntry "strlen_verified" "HeytingLean.LeanCP.Examples.StrlenVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.strlen_verified
      ``HeytingLean.LeanCP.Examples.strlenBody .symbolic .concreteOperational
  , mkEntry "strlen_forward_verified" "HeytingLean.LeanCP.Examples.StrlenVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.strlen_forward_verified
      ``HeytingLean.LeanCP.Examples.strlenBody .callAware .concreteOperational
  , mkEntry "swap_verified" "HeytingLean.LeanCP.Examples.SwapVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.swap_verified
      ``HeytingLean.LeanCP.Examples.swapBody .symbolic .parametric
  , mkEntry "swap_executes" "HeytingLean.LeanCP.Examples.SwapVerified" .stringMemorySystem
      ``HeytingLean.LeanCP.Examples.swap_executes
      ``HeytingLean.LeanCP.Examples.swapBody .operational .concreteOperational
  ]

def seedEntries : List BenchEntry :=
  ScalarArithmetic.scalarEntries ++ existingSeedEntries

end HeytingLean.LeanCP.Bench
