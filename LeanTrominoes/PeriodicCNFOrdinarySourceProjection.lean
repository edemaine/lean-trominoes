/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData

/-! # Selecting the original ordinary SAT incidences from exact-one records -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation

/-- Only these records terminate at an inherited ordinary source variable. -/
def inheritedSlot (header : Header) : Option SourceLiteralSlot :=
  match header.polarity.operation, header.figurePrefix with
  | .compatible, .inherited slot _ | .complementOriginal, .inherited slot _ => some slot
  | _, _ => none

def selectedIndex (profile : DirectedClauseProfile) (slot : SourceLiteralSlot) : Nat :=
  (sourceClauseHeaders profile).findIdx (fun header => inheritedSlot header == some slot)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem inheritedSlot_present : ∀ (profile : DirectedClauseProfile) (slot : SourceLiteralSlot),
    sourceSlotNat slot < profile.taggedLiterals.length →
      some slot ∈ (sourceClauseHeaders profile).map inheritedSlot := by
  intro profile slot
  cases profile with
  | unary a d => revert a d slot; decide +kernel
  | binary a d b e => revert a d b e slot; decide +kernel
  | ternary a d b e c f => revert a d b e c f slot; decide +kernel

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
