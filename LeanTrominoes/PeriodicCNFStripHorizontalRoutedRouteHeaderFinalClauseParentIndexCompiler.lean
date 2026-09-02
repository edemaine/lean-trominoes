/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

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

abbrev Frame := HorizontalRoutedRouteHeaderClauseFrame.Data

/-- Mark the last occurrence frame of every actual final clause.  A new
clause starts at a `.top` frame; the final frame of a descriptor block is
always a clause end. -/
def endingMarkers : List Frame → List Bool
  | [] => []
  | _ :: [] => [true]
  | _ :: next :: remaining =>
      decide (next.group = .top) :: endingMarkers (next :: remaining)

/-- Actual-final-clause boundaries contributed by one finite descriptor. -/
def tokenMarkers (token : Token) : List Bool :=
  endingMarkers (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token)

/-- Clause-start markers on the same finite frame block. -/
def tokenTopMarkers (token : Token) : List Bool :=
  (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token).map fun frame =>
    decide (frame.group = .top)

/-- One boundary marker per final occurrence frame. -/
def markers (source : List Token) : List Bool :=
  source.flatMap tokenMarkers

def increments (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values Bool.toNat (markers source)

/-- Zero-based actual final-clause index, repeated at every occurrence of
that clause. -/
def parentIndices (source : List Token) : List Nat :=
  PrefixSums.starts (increments source)

@[simp] theorem endingMarkers_length (frames : List Frame) :
    (endingMarkers frames).length = frames.length := by
  induction frames with
  | nil => rfl
  | cons frame frames induction =>
      cases frames with
      | nil => rfl
      | cons next remaining =>
          simp only [endingMarkers, List.length_cons, induction]

@[simp] theorem tokenMarkers_length (token : Token) :
    (tokenMarkers token).length =
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlock token).length := by
  simp [tokenMarkers]

/-- Every finite descriptor block has exactly as many ending boundaries as
actual final clauses.  This audit includes all unary, binary, and ternary
directed profiles and all finite route-direction choices. -/
theorem tokenMarkers_count_true_eq_topMarkers (token : Token) :
    (tokenMarkers token).count true =
      (tokenTopMarkers token).count true := by
  cases token with
  | «variable» => rfl
  | clause profile => cases profile <;> native_decide +revert

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
