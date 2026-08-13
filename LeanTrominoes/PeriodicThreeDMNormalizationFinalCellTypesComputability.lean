/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCellLookupComputability

/-! # Computability of the normalized row-major cell array -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def natCell (indices : Nat × Nat) : Cell :=
  (Int.ofNat indices.1, Int.ofNat indices.2)

theorem natCell_primrec : Primrec natCell :=
  (Primrec.pair
    (int_ofNat_primrec.comp Primrec.fst)
    (int_ofNat_primrec.comp Primrec.snd)).of_eq fun _ => rfl

def finalCellTypeAtIndicesInput
    (input : Input × (Nat × Nat)) : Input × Cell :=
  (input.1, natCell input.2)

theorem finalCellTypeAtIndicesInput_primrec :
    Primrec finalCellTypeAtIndicesInput :=
  (Primrec.pair Primrec.fst
    (natCell_primrec.comp Primrec.snd)).of_eq fun _ => rfl

def finalCellTypeAtIndices
    (input : Input × (Nat × Nat)) : OrthogonalCellType :=
  finalCellTypeAt input.1 (natCell input.2)

theorem finalCellTypeAtIndices_primrec :
    Primrec finalCellTypeAtIndices :=
  (finalCellTypeAt_primrec.comp
    finalCellTypeAtIndicesInput_primrec).of_eq fun _ => rfl

def finalCellAtRowIndexInput
    (input : (Input × Nat) × Nat) : Input × (Nat × Nat) :=
  (input.1.1, (input.2, input.1.2))

theorem finalCellAtRowIndexInput_primrec :
    Primrec finalCellAtRowIndexInput :=
  (Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair Primrec.snd
      (Primrec.snd.comp Primrec.fst))).of_eq fun _ => rfl

def finalCellAtRowIndex
    (input : (Input × Nat) × Nat) : OrthogonalCellType :=
  finalCellTypeAtIndices (finalCellAtRowIndexInput input)

theorem finalCellAtRowIndex_primrec :
    Primrec finalCellAtRowIndex :=
  (finalCellTypeAtIndices_primrec.comp
    finalCellAtRowIndexInput_primrec).of_eq fun _ => rfl

def finalCellRow (input : Input × Nat) :
    List OrthogonalCellType :=
  (List.range (finalNormalizationPeriod input.1)).map fun horizontal =>
    finalCellAtRowIndex (input, horizontal)

theorem finalCellRow_primrec : Primrec finalCellRow := by
  have horizontalRange : Primrec fun input : Input × Nat =>
      List.range (finalNormalizationPeriod input.1) :=
    Primrec.list_range.comp
      (finalNormalizationPeriod_primrec.comp Primrec.fst)
  exact (Primrec.list_map horizontalRange
    finalCellAtRowIndex_primrec.to₂).of_eq fun _ => rfl

theorem finalCellTypes_primrec : Primrec finalCellTypes := by
  have verticalRange : Primrec fun input : Input =>
      List.range (finalNormalizationPeriod input) :=
    Primrec.list_range.comp finalNormalizationPeriod_primrec
  exact (Primrec.list_flatMap verticalRange
    finalCellRow_primrec.to₂).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
