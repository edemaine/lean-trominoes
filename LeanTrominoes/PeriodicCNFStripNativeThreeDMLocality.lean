/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMGeometry
import LeanTrominoes.PeriodicCNFStripHorizontalProblem
import LeanTrominoes.PeriodicThreeDMLineDecision

/-! # Graph locality of the native horizontal 3DM reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Gadget PeriodicThreeDM
attribute [local instance] sourceVariableDecidableEq
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

private theorem translated_offset_bound (p target offset : Int) (positive : 0 < p)
    (inside : 0 < target ∧ target < p)
    (halo : -p < target + p*offset ∧ target+p*offset < 2*p) : offset.natAbs ≤ 1 := by
  have lower : -1 ≤ offset := by
    by_contra h
    have hm := Int.mul_le_mul_of_nonneg_left (show offset ≤ -2 by omega) (show 0 ≤ p by omega)
    omega
  have upper : offset ≤ 1 := by
    by_contra h
    have hm := Int.mul_le_mul_of_nonneg_left (show 2 ≤ offset by omega) (show 0 ≤ p by omega)
    omega
  omega

theorem nativeThreeDM_horizontal (s : List encoding.Γ) : (nativeThreeDMProblem decider s).IsOneDimensional := by
  rw [nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact problem_isOneDimensional _

theorem nativeThreeDMDrawing_halo (s : List encoding.Γ) :
    (nativeThreeDMDrawing decider s).RoutePointsInExpandedSquare := by
  rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing]
  apply PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints
  · exact PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
      (sourceFormula _) (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq _) (sourceFormula_clausesNonempty _)
  · intro route member
    exact PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
      (problem _).incidenceGraph (presentation _).drawing
      (presentation _).toPlanarPresentation.compatible
      (problem _).incidenceGraph_edgesAreLoopless member

theorem nativeThreeDM_local (s : List encoding.Γ) : (nativeThreeDMProblem decider s).IsLocal := by
  intro triple member color
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp member
  let tag : IncidenceTag := ⟨i,color⟩
  have ht : tag ∈ nativeThreeDMIncidences decider s := by
    rw [nativeThreeDMIncidences,incidenceTags_eq_range_flatMap]
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr hi,?_⟩
    cases color <;> simp [tag,tripleIncidenceTags,incidenceColors]
  have routeMember : nativeThreeDMRoute decider s tag ∈ (nativeThreeDMDrawing decider s).edgeRoutes := by
    simp only [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_edgeRoutes,
      horizontalThreeDMEdgeRoutesComputed,horizontalThreeDMIncidenceTagsComputed]
    exact List.mem_map.mpr ⟨tag,ht,rfl⟩
  have halo := nativeThreeDMDrawing_halo decider s _ routeMember _
    (mem_of_getLast?_eq_some (nativeThreeDMRoute_endpoints decider s tag ht).2)
  have inside := nativeThreeDMTargetPoint_inside decider s tag ht
  rw [PeriodicGridDrawing.PositionInExpandedSquare,nativeThreeDMDrawing_period] at halo
  rw [PeriodicGridDrawing.PositionInFundamentalSquare,nativeThreeDMDrawing_period] at inside
  have bx := translated_offset_bound (nativeThreeDMPeriod decider s)
    (nativeThreeDMTargetPoint decider s tag).1 (nativeThreeDMReference decider s tag).offset.1
    (by exact_mod_cast nativeThreeDMPeriod_positive decider s) ⟨inside.1,inside.2.1⟩ ⟨halo.1,halo.2.1⟩
  have vertical := nativeThreeDM_horizontal decider s _ (List.getElem_mem hi) color
  simpa only [nativeThreeDMReference,tag,List.getD_eq_getElem _ _ hi,vertical,Int.natAbs_zero,Nat.add_zero] using bx

end LeanTrominoes.PeriodicCNFStripReduction
end
