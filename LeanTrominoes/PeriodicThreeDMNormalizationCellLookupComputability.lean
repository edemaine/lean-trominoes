/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationFinalAssignmentsComputability

/-! # Computability of normalized cell lookup -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def finalCellLookupInput
    (input : Input × Cell) :
    Cell × List NormalizedCellAssignment :=
  (input.2, finalCellAssignments input.1)

theorem finalCellLookupInput_primrec :
    Primrec finalCellLookupInput :=
  (Primrec.pair Primrec.snd
    (finalCellAssignments_primrec.comp Primrec.fst)).of_eq fun _ => rfl

def lookupAssignment
    (input : Cell × List NormalizedCellAssignment) :
    Option OrthogonalCellType :=
  input.2.lookup input.1

theorem lookupCell_decidableEq_eq
    (location : Cell)
    (assignments : List NormalizedCellAssignment) :
    @List.lookup Cell OrthogonalCellType instBEqOfDecidableEq
        location assignments =
      assignments.lookup location := by
  induction assignments with
  | nil => rfl
  | cons assignment rest induction =>
      simp only [List.lookup]
      have comparison :
          @BEq.beq Cell instBEqOfDecidableEq location assignment.1 =
            @BEq.beq Cell instBEqProd location assignment.1 := by
        simp
      rw [comparison, induction]

theorem lookupAssignment_primrec :
    Primrec lookupAssignment :=
  (Primrec.listLookup.comp Primrec.fst Primrec.snd).of_eq fun input => by
    unfold lookupAssignment
    exact lookupCell_decidableEq_eq input.1 input.2

def cellTypeFromLookup
    (cellType : Option OrthogonalCellType) : OrthogonalCellType :=
  cellType.getD .blank

theorem cellTypeFromLookup_primrec :
    Primrec cellTypeFromLookup :=
  (Primrec.option_getD.comp Primrec.id
    (Primrec.const OrthogonalCellType.blank)).of_eq fun _ => rfl

theorem finalCellTypeAt_primrec :
    Primrec fun input : Input × Cell =>
      finalCellTypeAt input.1 input.2 :=
  (cellTypeFromLookup_primrec.comp
    (lookupAssignment_primrec.comp
      finalCellLookupInput_primrec)).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
