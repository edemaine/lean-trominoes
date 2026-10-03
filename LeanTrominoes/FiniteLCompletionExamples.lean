/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteLCompletionDecision
namespace LeanTrominoes.Tromino.FiniteL
open FiniteWitness
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

example : Valid Tromino.L (box 0) ∅ {twoBottom 0 0} := by decide +kernel
example : decideCompletion ∅=true := by decide +kernel
example : decideCompletion {{(0,0)}}=false := by decide +kernel

-- Each of the three nontrivial boundary patterns gets the appropriate tile.
example : rowPatches ∅ 0 0 2={twoBottom 0 0} := by decide +kernel
example : rowPatches {(1,0)} 0 0 2={bottomLeft 0 0} := by decide +kernel
example : rowPatches {(0,0)} 0 0 2={bottomRight 0 0} := by decide +kernel
example : rowPatches {(0,0),(1,0)} 0 0 2=∅ := by decide +kernel
-- At an odd-width endpoint, the unused column acts as occupied.
example : rowPatches ∅ 0 0 1={bottomLeft 0 0} := by decide +kernel

end LeanTrominoes.Tromino.FiniteL
