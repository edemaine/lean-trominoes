/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentsComputability
import LeanTrominoes.PeriodicThreeDMNormalizationCellLookupComputability
import LeanTrominoes.PeriodicThreeDMNormalizationFinalCellTypesComputability

/-! # Computability of the rectangular row-major cell array -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem finalStripHeight_primrec : Primrec finalStripHeight := by
  have threePeriods : Primrec fun input : Input =>
      3 * finalNormalizationPeriod input :=
    Primrec.nat_mul.comp (Primrec.const 3)
      finalNormalizationPeriod_primrec
  exact (Primrec.nat_add.comp threePeriods
    (Primrec.const 1)).of_eq fun _ => rfl

def finalStripCellLookupInput
    (input : Input × Cell) :
    Cell × List NormalizedCellAssignment :=
  (input.2, finalStripCellAssignments input.1)

theorem finalStripCellLookupInput_primrec :
    Primrec finalStripCellLookupInput :=
  (Primrec.pair Primrec.snd
    (finalStripCellAssignments_primrec.comp Primrec.fst)).of_eq fun _ => rfl

theorem finalStripCellTypeAt_primrec :
    Primrec fun input : Input × Cell =>
      finalStripCellTypeAt input.1 input.2 :=
  (cellTypeFromLookup_primrec.comp
    (lookupAssignment_primrec.comp
      finalStripCellLookupInput_primrec)).of_eq fun _ => rfl

def finalStripCellTypeAtIndicesInput
    (input : Input × (Nat × Nat)) : Input × Cell :=
  (input.1, natCell input.2)

theorem finalStripCellTypeAtIndicesInput_primrec :
    Primrec finalStripCellTypeAtIndicesInput :=
  (Primrec.pair Primrec.fst
    (natCell_primrec.comp Primrec.snd)).of_eq fun _ => rfl

def finalStripCellTypeAtIndices
    (input : Input × (Nat × Nat)) : OrthogonalCellType :=
  finalStripCellTypeAt input.1 (natCell input.2)

theorem finalStripCellTypeAtIndices_primrec :
    Primrec finalStripCellTypeAtIndices :=
  (finalStripCellTypeAt_primrec.comp
    finalStripCellTypeAtIndicesInput_primrec).of_eq fun _ => rfl

def finalStripCellAtRowIndexInput
    (input : (Input × Nat) × Nat) : Input × (Nat × Nat) :=
  (input.1.1, (input.2, input.1.2))

theorem finalStripCellAtRowIndexInput_primrec :
    Primrec finalStripCellAtRowIndexInput :=
  (Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.pair Primrec.snd
      (Primrec.snd.comp Primrec.fst))).of_eq fun _ => rfl

def finalStripCellAtRowIndex
    (input : (Input × Nat) × Nat) : OrthogonalCellType :=
  finalStripCellTypeAtIndices (finalStripCellAtRowIndexInput input)

theorem finalStripCellAtRowIndex_primrec :
    Primrec finalStripCellAtRowIndex :=
  (finalStripCellTypeAtIndices_primrec.comp
    finalStripCellAtRowIndexInput_primrec).of_eq fun _ => rfl

def finalStripCellRow (input : Input × Nat) :
    List OrthogonalCellType :=
  (List.range (finalNormalizationPeriod input.1)).map fun horizontal =>
    finalStripCellAtRowIndex (input, horizontal)

theorem finalStripCellRow_primrec : Primrec finalStripCellRow := by
  have horizontalRange : Primrec fun input : Input × Nat =>
      List.range (finalNormalizationPeriod input.1) :=
    Primrec.list_range.comp
      (finalNormalizationPeriod_primrec.comp Primrec.fst)
  exact (Primrec.list_map horizontalRange
    finalStripCellAtRowIndex_primrec.to₂).of_eq fun _ => rfl

theorem finalStripCellTypes_primrec :
    Primrec finalStripCellTypes := by
  have verticalRange : Primrec fun input : Input =>
      List.range (finalStripHeight input) :=
    Primrec.list_range.comp finalStripHeight_primrec
  exact (Primrec.list_flatMap verticalRange
    finalStripCellRow_primrec.to₂).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
