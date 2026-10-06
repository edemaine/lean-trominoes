/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case0
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case1
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case2
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case3
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case4
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case5
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case6
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case7
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case8
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case9
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case10
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case11
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case12
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case13
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case14
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case15
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case16
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case17
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case18
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificates.Case19

/-! # Parent indices of actual final clauses

One pre-Figure-9 clause descriptor can expand into many polarity-normalized
final clauses.  This compiler marks the boundary of every such final clause
inside each finite descriptor block and takes prefix sums of those markers.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderFinalClauseParentIndex

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering

private theorem finalClauseParentMarkersCheck_first_correct
    (first : LeanTrominoes.PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile)
    (direction : AxisDirection) : firstDirectedProfileCheck finalClauseParentMarkersCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact finalClauseParentMarkersCheck_case0
  · exact finalClauseParentMarkersCheck_case1
  · exact finalClauseParentMarkersCheck_case2
  · exact finalClauseParentMarkersCheck_case3
  · exact finalClauseParentMarkersCheck_case4
  · exact finalClauseParentMarkersCheck_case5
  · exact finalClauseParentMarkersCheck_case6
  · exact finalClauseParentMarkersCheck_case7
  · exact finalClauseParentMarkersCheck_case8
  · exact finalClauseParentMarkersCheck_case9
  · exact finalClauseParentMarkersCheck_case10
  · exact finalClauseParentMarkersCheck_case11
  · exact finalClauseParentMarkersCheck_case12
  · exact finalClauseParentMarkersCheck_case13
  · exact finalClauseParentMarkersCheck_case14
  · exact finalClauseParentMarkersCheck_case15
  · exact finalClauseParentMarkersCheck_case16
  · exact finalClauseParentMarkersCheck_case17
  · exact finalClauseParentMarkersCheck_case18
  · exact finalClauseParentMarkersCheck_case19

private theorem finalClauseParentMarkersCheck_correct (profile : DirectedClauseProfile) :
    finalClauseParentMarkersCheck profile = true :=
  firstDirectedProfileCheck_sound finalClauseParentMarkersCheck finalClauseParentMarkersCheck_first_correct profile

/-- Every finite descriptor block has exactly as many ending boundaries as
actual final clauses.  This audit includes all unary, binary, and ternary
directed profiles and all finite route-direction choices. -/
theorem tokenMarkers_count_true_eq_topMarkers (token : Token) :
    (tokenMarkers token).count true =
      (tokenTopMarkers token).count true := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      have checked := finalClauseParentMarkersCheck_correct profile
      simp only [finalClauseParentMarkersCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.1

/-- More strongly, the boundary detector is exactly the ordinary
block-ending marker stream of the boundary-preserving final-clause frames. -/
theorem tokenMarkers_eq_blockMarkers (token : Token) :
    tokenMarkers token =
      FiniteBlockIndices.markers List.length
        (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token) := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      have checked := finalClauseParentMarkersCheck_correct profile
      simp only [finalClauseParentMarkersCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.2

/-- Globally, final-clause ends and final-clause starts have the same count. -/
theorem markers_count_true_eq_topMarkers (source : List Token) :
    (markers source).count true =
      (source.flatMap tokenTopMarkers).count true := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change (tokenMarkers token ++ markers source).count true =
        (tokenTopMarkers token ++ source.flatMap tokenTopMarkers).count true
      rw [List.count_append, List.count_append,
        tokenMarkers_count_true_eq_topMarkers, induction]

/-- The complete boundary stream is the block-ending stream of all actual
final clauses with their boundaries retained. -/
theorem markers_eq_blockMarkers (source : List Token) :
    markers source =
      FiniteBlockIndices.markers List.length
        (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source) := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change tokenMarkers token ++ markers source =
        FiniteBlockIndices.markers List.length
          (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token ++
            HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source)
      unfold FiniteBlockIndices.markers
      rw [List.flatMap_append]
      change tokenMarkers token ++ markers source =
        FiniteBlockIndices.markers List.length
            (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token) ++
          FiniteBlockIndices.markers List.length
            (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source)
      rw [tokenMarkers_eq_blockMarkers, induction]

/-- Prefix summation of the finite boundary detector is exactly the generic
actual-clause block-index stream. -/
theorem parentIndices_eq_blockIndices (source : List Token) :
    parentIndices source =
      FiniteBlockIndices.indices List.length
        (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source) := by
  unfold parentIndices increments FiniteBlockIndices.indices
    FiniteBlockIndices.increments
  rw [markers_eq_blockMarkers]

/-- Thus the computed index is each actual final clause's ordinal repeated
over every occurrence frame in that clause. -/
theorem parentIndices_eq_expected (source : List Token) :
    parentIndices source =
      FiniteBlockIndices.expected List.length
        (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks source) := by
  rw [parentIndices_eq_blockIndices]
  exact FiniteBlockIndices.indices_eq_expected List.length _

theorem markers_length (source : List Token) :
    (markers source).length =
      (HorizontalRoutedRouteHeaderClauseFrame.output source).length := by
  simp [markers, HorizontalRoutedRouteHeaderClauseFrame.output]

theorem increments_length (source : List Token) :
    (increments source).length =
      (HorizontalRoutedRouteHeaderClauseFrame.output source).length := by
  unfold increments FiniteUnaryFieldMap.values
  rw [List.length_map, markers_length]

/-- There is exactly one actual parent-clause index per final occurrence. -/
theorem parentIndices_length (source : List Token) :
    (parentIndices source).length =
      (HorizontalRoutedRouteHeaderClauseFrame.output source).length := by
  simp [parentIndices, increments_length]

noncomputable def markersComputableInPolyTime :
    TM2ComputableInPolyTime id id markers :=
  FiniteBlockTransducer.computableInPolyTime tokenMarkers

noncomputable def incrementsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields increments := by
  unfold increments
  exact TM2CompositionMachine.computableInPolyTime
    markersComputableInPolyTime
    (FiniteUnaryFieldMap.computableInPolyTime Bool.toNat)

/-- Actual final-clause parent indices are polynomial-time computable as
unary fields. -/
noncomputable def parentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields parentIndices := by
  unfold parentIndices
  exact TM2CompositionMachine.computableInPolyTime
    incrementsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime

end HorizontalRoutedRouteHeaderFinalClauseParentIndex
end PeriodicCNFStripReduction
end LeanTrominoes

end
