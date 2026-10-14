/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationLocalCompleteness
import LeanTrominoes.TrichromaticGraphOrientationLineDecision
import LeanTrominoes.PeriodicThreeDMLineHardness

/-! # Correctness and locality of the ordinary graph PSPACE reduction

This module establishes semantics. Polynomial-time compilation of the native
graph records is a separate obligation.
-/
namespace LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
open Gadget

theorem input_isOneDimensional {problem : PeriodicThreeDM} (horizontal : problem.IsOneDimensional) :
    TrichromaticGraphOrientation.IsOneDimensional (input problem) := by
  intro record member
  obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
  have incidences := contractedEdge_incidence_members_of_mem problem edgeMember
  have sourceZero := incidence_offset_vertical_eq_zero horizontal edge.color edge.atom incidences.1
  have targetZero := incidence_offset_vertical_eq_zero horizontal edge.color edge.atom incidences.2.1
  cases edge with
  | retained color atom incidence => exact sourceZero
  | through color atom first second =>
    change first.offset.2 = 0 at sourceZero
    change second.offset.2 = 0 at targetZero
    simp [edgeRecord,ContractedEdge.toPeriodicEdge,Cell.sub,sourceZero,targetZero]

end LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicOrthocrossing PeriodicThreeDM
attribute [local instance] sourceVariableDecidableEq
set_option synthInstance.maxSize 2048
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem problem_incidenceOffsetsComparable (source : PeriodicCNF Nat) :
    (problem source).IncidenceOffsetsComparable := by
  unfold problem retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
  apply PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_incidenceOffsetsComparable
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
    (sourceFormula source) (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)

variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

theorem nativeThreeDM_incidenceOffsetsComparable (symbols : List encoding.Γ) :
    (nativeThreeDMProblem decider symbols).IncidenceOffsetsComparable := by
  rw [nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact problem_incidenceOffsetsComparable _

def nativeOrientationGraph (symbols : List encoding.Γ) : TrichromaticGraphOrientation.Input :=
  GraphOrientationEncoding.input (nativeThreeDMProblem decider symbols)

theorem nativeOrientationGraph_isLocal (symbols : List encoding.Γ) :
    TrichromaticGraphOrientation.IsLocal (nativeOrientationGraph decider symbols) :=
  GraphOrientationEncoding.input_isLocal (contractedGraph_isLocal
    (nativeThreeDM_local decider symbols) (nativeThreeDM_incidenceOffsetsComparable decider symbols))

theorem nativeOrientationGraph_isOneDimensional (symbols : List encoding.Γ) :
    TrichromaticGraphOrientation.IsOneDimensional (nativeOrientationGraph decider symbols) :=
  GraphOrientationEncoding.input_isOneDimensional (nativeThreeDM_horizontal decider symbols)

theorem nativeOrientationGraph_correct (symbols : List encoding.Γ) :
    TrichromaticGraphOrientation.LocalLineProblem (nativeOrientationGraph decider symbols) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  rw [TrichromaticGraphOrientation.LocalLineProblem,TrichromaticGraphOrientation.LocalProblem,
    and_iff_left (nativeOrientationGraph_isOneDimensional decider symbols),
    and_iff_right (nativeOrientationGraph_isLocal decider symbols)]
  change TrichromaticGraphOrientation.Problem
    (GraphOrientationEncoding.input (nativeThreeDMProblem decider symbols)) ↔ _
  rw [GraphOrientationEncoding.problem_iff _ (nativeThreeDMWellFormed decider symbols) (nativeThreeDMDegree decider symbols),
    nativeThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact (problem_correct _).symm

end LeanTrominoes.PeriodicCNFStripReduction
end
