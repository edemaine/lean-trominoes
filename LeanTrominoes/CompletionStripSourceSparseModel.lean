/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionSparseDrawing
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentBounds
import LeanTrominoes.PeriodicCNFStripDirectExecutableFields
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentLookup

/-! # The actual PSPACE source records satisfy the sparse drawing model -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Gadget Gadget.PeriodicOrthogonalDrawing PeriodicCNFStripReduction
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem position_nat_eq (d : PeriodicOrthogonalDrawing) (c : Cell)
    (hc : 0 ≤ c.1 ∧ c.1 < d.horizontalPeriod ∧ 0 ≤ c.2 ∧ c.2 < d.verticalPeriod) :
    (((d.positionAt c).1.val:Int),((d.positionAt c).2.val:Int)) = c := by
  have hx : c.1 % (d.horizontalPeriod:Int) = c.1 := Int.emod_eq_of_lt hc.1 hc.2.1
  have hy : c.2 % (d.verticalPeriod:Int) = c.2 := Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2
  apply Prod.ext <;> simp only [positionAt,residue]
  · change ((c.1%(d.horizontalPeriod:Int)).toNat:Int) = c.1
    rw [hx,Int.toNat_of_nonneg hc.1]
  · change ((c.2%(d.verticalPeriod:Int)).toNat:Int) = c.2
    rw [hy,Int.toNat_of_nonneg hc.2.2.1]

private theorem planar_lookup {problem : PeriodicThreeDM} (p : problem.PlanarPresentation)
    (c : Cell) (hc : 0 ≤ c.1 ∧ c.1 < p.stripNormalizedOrthogonalDrawing.horizontalPeriod ∧
      0 ≤ c.2 ∧ c.2 < p.stripNormalizedOrthogonalDrawing.verticalPeriod) :
    p.stripNormalizedOrthogonalDrawing.getAt c = (p.finalStripCellAssignments.lookup c).getD .blank := by
  unfold getAt
  rw [p.stripNormalizedOrthogonalDrawing_get,position_nat_eq _ c hc]
  rfl

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
  {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)
local instance sourceModelStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

theorem source_sparseModel (symbols : List encoding.Γ) :
    SparseModel (directCompiledStripDrawingOfSymbols decider symbols)
      (directSparseAssignmentsOfSymbols decider symbols) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let continuous := presentation source
  let p := continuous.toPlanarPresentation
  have drawingEq : directCompiledStripDrawingOfSymbols decider symbols = p.stripNormalizedOrthogonalDrawing := by
    exact compiledStripDrawing_eq_stripDrawing source
  have entriesEq : directSparseAssignmentsOfSymbols decider symbols = p.finalStripCellAssignments := by
    unfold directSparseAssignmentsOfSymbols directSparseNormalizationInputOfSymbols normalizationInput
    rw [PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments_inputOfPresentation]
  rw [drawingEq,entriesEq]
  have bounds (a : DrawingEntry) (ha : a ∈ p.finalStripCellAssignments) :
      0 ≤ a.1.1 ∧ a.1.1 < p.stripNormalizedOrthogonalDrawing.horizontalPeriod ∧
      0 ≤ a.1.2 ∧ a.1.2 < p.stripNormalizedOrthogonalDrawing.verticalPeriod := by
    have bx := p.finalStripCellAssignment_horizontal_bounds ha
    have by' := continuous.finalStripCellAssignment_vertical_interior
      continuous.problemWellFormed (problem_degreeTwoOrThree source) (problem_isOneDimensional source)
      (presentation_routePointsInExpandedVerticalBand source) ha
    have wx : p.stripNormalizedOrthogonalDrawing.horizontalPeriod = p.finalNormalizationPeriod :=
      p.stripNormalizedOrthogonalDrawing_periods.1
    have hy : p.stripNormalizedOrthogonalDrawing.verticalPeriod = p.finalStripHeight :=
      p.stripNormalizedOrthogonalDrawing_periods.2
    change 0 ≤ a.1.1 ∧ a.1.1 < (p.finalNormalizationPeriod:Int) at bx
    change 0 < a.1.2 ∧ a.1.2 < 3*(p.finalNormalizationPeriod:Int) at by'
    have hh : p.finalStripHeight = 3*p.finalNormalizationPeriod+1 := rfl
    rw [wx,hy,hh]
    exact ⟨bx.1,bx.2,by omega,by omega⟩
  refine ⟨bounds,?_,planar_lookup p⟩
  intro a ha
  rw [planar_lookup p a.1 (bounds a ha)]
  have collision := continuous.finalStripAssignmentsCollisionFree continuous.problemWellFormed
    (problem_degreeTwoOrThree source) (presentation_separated source) (presentation_routesSimple source)
  exact p.finalStripCellTypeAt_eq_of_mem collision ha
end LeanTrominoes.CompletionPattern.Runtime
