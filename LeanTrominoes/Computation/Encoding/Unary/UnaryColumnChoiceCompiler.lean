/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnFilterCompiler
import LeanTrominoes.Computation.Encoding.Aligned.AlignedUnaryBooleanChoiceOccurrenceSemantics

/-! # Conditional choice between aligned compiled unary columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing
variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Row} {predicate : List Symbol → Row → Bool}
  {first second weight : List Symbol → Row → Nat}

def choose (controls : TM2ComputableInPolyTime id id (fun s => (rows s).map (predicate s)))
    (firstColumn : Compiler rows first) (secondColumn : Compiler rows second) :
    Compiler rows (fun s row => if predicate s row then second s row else first s row) := by
  let physical := AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime id
    (fun s => (rows s).map (predicate s)) (fun s => (rows s).map (first s))
    (fun s => (rows s).map (second s)) (fun s => by simp) (fun s => by simp)
    controls firstColumn secondColumn
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [AlignedUnaryBooleanChoice.selectedValues_eq_pointwiseSelected _ _ _ (by simp) (by simp)]
  induction rows s with
  | nil => rfl
  | cons row rows ih => simpa [AlignedUnaryBooleanChoice.pointwiseSelected] using ih

def chooseThree (weights : Compiler rows weight) (firstColumn : Compiler rows first) (secondColumn : Compiler rows second) :
    Compiler rows (fun s row => if weight s row = 3 then second s row else first s row) := by
  let controls := TM2CompositionMachine.computableInPolyTime weights threeControlsCompiler
  let physical := choose (predicate := fun s row => decide (weight s row = 3))
    (TM2ComputableInPolyTime.of_eq controls (fun s => by simp [threeControls,List.map_map])) firstColumn secondColumn
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp)

end LeanTrominoes.UnaryColumn
end
