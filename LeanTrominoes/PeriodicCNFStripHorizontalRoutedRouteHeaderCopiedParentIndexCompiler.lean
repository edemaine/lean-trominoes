/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Parent indices of copied-clause occurrence blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderCopiedParentIndex

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering

/-- A block-ending marker of the requested length.  Prefix sums of these
markers are constant throughout one nonempty block and advance immediately
after it. -/
def endingMarkers : Nat → List Bool
  | 0 => []
  | count + 1 => List.replicate count false ++ [true]

def tokenMarkers : Token → List Bool
  | .variable => []
  | .clause profile =>
      endingMarkers
        (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
          (.clause profile)).length

/-- One final-position marker per copied occurrence, true exactly at the end
of each nonempty parent-clause block. -/
def markers (source : List Token) : List Bool :=
  source.flatMap tokenMarkers

def increments (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values Bool.toNat (markers source)

/-- Zero-based parent clause index, repeated at every final occurrence of
that parent. -/
def parentIndices (source : List Token) : List Nat :=
  PrefixSums.starts (increments source)

def nextParent (parent count : Nat) : Nat :=
  if count = 0 then parent else parent + 1

/-- Direct block semantics of the parent-index column. -/
def expectedAux : Nat → List Token → List Nat
  | _, [] => []
  | parent, .variable :: source => expectedAux parent source
  | parent, .clause profile :: source =>
      let count :=
        (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
          (.clause profile)).length
      List.replicate count parent ++
        expectedAux (nextParent parent count) source

def expected (source : List Token) : List Nat :=
  expectedAux 0 source

@[simp] theorem endingMarkers_length (count : Nat) :
    (endingMarkers count).length = count := by
  cases count <;> simp [endingMarkers]

@[simp] theorem tokenMarkers_length (token : Token) :
    (tokenMarkers token).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock token).length := by
  cases token <;> simp [tokenMarkers]

theorem markers_length (source : List Token) :
    (markers source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  simp [markers, HorizontalRoutedRouteHeaderOccurrenceBlock.output]

theorem increments_length (source : List Token) :
    (increments source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold increments FiniteUnaryFieldMap.values
  rw [List.length_map, markers_length]

/-- There is exactly one parent index per final copied occurrence. -/
theorem parentIndices_length (source : List Token) :
    (parentIndices source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  simp [parentIndices, increments_length]

private theorem startsAux_replicate_zero_append
    (start count : Nat) (remaining : List Nat) :
    PrefixSums.startsAux start
        (List.replicate count 0 ++ remaining) =
      List.replicate count start ++
        PrefixSums.startsAux start remaining := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append,
        PrefixSums.startsAux_cons]
      simp only [Nat.add_zero]
      rw [induction, List.replicate_succ]
      simp

private theorem startsAux_endingMarkers_append
    (start count : Nat) (remaining : List Nat) :
    PrefixSums.startsAux start
        ((endingMarkers count).map Bool.toNat ++ remaining) =
      List.replicate count start ++
        PrefixSums.startsAux (nextParent start count) remaining := by
  cases count with
  | zero => rfl
  | succ count =>
      rw [show (endingMarkers (count + 1)).map Bool.toNat =
          List.replicate count 0 ++ [1] by
        simp [endingMarkers, List.map_append]]
      rw [List.append_assoc,
        startsAux_replicate_zero_append]
      rw [show List.replicate (count + 1) start =
          List.replicate count start ++ [start] by
        simp [List.replicate_add]]
      simp [nextParent, List.append_assoc]

private theorem startsAux_markers (parent : Nat)
    (source : List Token) :
    PrefixSums.startsAux parent
        ((markers source).map Bool.toNat) =
      expectedAux parent source := by
  induction source generalizing parent with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [markers, tokenMarkers, expectedAux] using induction parent
      | clause profile =>
          let count :=
            (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
              (.clause profile)).length
          change PrefixSums.startsAux parent
              ((endingMarkers count ++ markers source).map Bool.toNat) = _
          rw [List.map_append, startsAux_endingMarkers_append,
            induction]
          rfl

/-- Prefix summation implements the direct blockwise parent-index
specification on every descriptor stream. -/
theorem parentIndices_eq_expected (source : List Token) :
    parentIndices source = expected source := by
  exact startsAux_markers 0 source

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

/-- Parent-clause indices for the complete copied occurrence stream are
polynomial-time computable as unary fields. -/
noncomputable def parentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields parentIndices := by
  unfold parentIndices
  exact TM2CompositionMachine.computableInPolyTime
    incrementsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime

end HorizontalRoutedRouteHeaderCopiedParentIndex
end PeriodicCNFStripReduction
end LeanTrominoes

end
