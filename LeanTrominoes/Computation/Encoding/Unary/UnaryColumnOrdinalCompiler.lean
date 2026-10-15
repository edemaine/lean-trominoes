/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSignedEncoding

/-! # Dense row ordinals from a compiled unary column -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing
variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol] [DecidableEq Row]
  {rows : List Symbol → List Row} {value : List Symbol → Row → Nat}

def ordinal (column : Compiler rows value) (unique : ∀ s, (rows s).Nodup) :
    Compiler rows (fun s row => (rows s).idxOf row) := by
  let physical := naturalRange (countRows column)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_range,List.getElem_map]
    exact ((unique s).idxOf_getElem index (by simpa using leftBound)).symm

end LeanTrominoes.UnaryColumn
end
