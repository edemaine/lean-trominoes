/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Source indices broadcast over finite output blocks -/

noncomputable section

namespace LeanTrominoes.FiniteBlockIndices

open Computability Turing

/-- A block-ending marker of the requested length. -/
def endingMarkers : Nat → List Bool
  | 0 => []
  | count + 1 => List.replicate count false ++ [true]

/-- One marker per emitted block position, true only at a nonempty block's
last position. -/
def itemMarkers {Source : Type*} (blockLength : Source → Nat)
    (item : Source) : List Bool :=
  endingMarkers (blockLength item)

def markers {Source : Type*} (blockLength : Source → Nat)
    (source : List Source) : List Bool :=
  source.flatMap (itemMarkers blockLength)

def increments {Source : Type*} (blockLength : Source → Nat)
    (source : List Source) : List Nat :=
  FiniteUnaryFieldMap.values Bool.toNat (markers blockLength source)

/-- The zero-based nonempty-block index, broadcast over every position of
that block. -/
def indices {Source : Type*} (blockLength : Source → Nat)
    (source : List Source) : List Nat :=
  PrefixSums.starts (increments blockLength source)

def nextIndex (index count : Nat) : Nat :=
  if count = 0 then index else index + 1

def expectedAux {Source : Type*} (blockLength : Source → Nat) :
    Nat → List Source → List Nat
  | _, [] => []
  | index, item :: source =>
      let count := blockLength item
      List.replicate count index ++
        expectedAux blockLength (nextIndex index count) source

def expected {Source : Type*} (blockLength : Source → Nat)
    (source : List Source) : List Nat :=
  expectedAux blockLength 0 source

@[simp] theorem endingMarkers_length (count : Nat) :
    (endingMarkers count).length = count := by
  cases count <;> simp [endingMarkers]

@[simp] theorem itemMarkers_length {Source : Type*}
    (blockLength : Source → Nat) (item : Source) :
    (itemMarkers blockLength item).length = blockLength item := by
  simp [itemMarkers]

theorem markers_length {Source : Type*}
    (blockLength : Source → Nat) (source : List Source) :
    (markers blockLength source).length =
      (source.map blockLength).sum := by
  simp [markers]

theorem increments_length {Source : Type*}
    (blockLength : Source → Nat) (source : List Source) :
    (increments blockLength source).length =
      (source.map blockLength).sum := by
  unfold increments FiniteUnaryFieldMap.values
  rw [List.length_map, markers_length]

@[simp] theorem indices_length {Source : Type*}
    (blockLength : Source → Nat) (source : List Source) :
    (indices blockLength source).length =
      (source.map blockLength).sum := by
  simp [indices, increments_length]

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
        PrefixSums.startsAux (nextIndex start count) remaining := by
  cases count with
  | zero => rfl
  | succ count =>
      rw [show (endingMarkers (count + 1)).map Bool.toNat =
          List.replicate count 0 ++ [1] by
        simp [endingMarkers, List.map_append]]
      rw [List.append_assoc, startsAux_replicate_zero_append]
      rw [show List.replicate (count + 1) start =
          List.replicate count start ++ [start] by
        simp [List.replicate_add]]
      simp [nextIndex, List.append_assoc]

private theorem startsAux_markers {Source : Type*}
    (blockLength : Source → Nat) (index : Nat)
    (source : List Source) :
    PrefixSums.startsAux index
        ((markers blockLength source).map Bool.toNat) =
      expectedAux blockLength index source := by
  induction source generalizing index with
  | nil => rfl
  | cons item source induction =>
      change PrefixSums.startsAux index
          (((endingMarkers (blockLength item)) ++
            markers blockLength source).map Bool.toNat) = _
      rw [List.map_append, startsAux_endingMarkers_append,
        induction]
      rfl

/-- Prefix summation realizes the blockwise index specification. -/
theorem indices_eq_expected {Source : Type*}
    (blockLength : Source → Nat) (source : List Source) :
    indices blockLength source = expected blockLength source := by
  exact startsAux_markers blockLength 0 source

private theorem expectedAux_mem_lt {Source : Type*}
    (blockLength : Source → Nat) (source : List Source)
    (start value : Nat)
    (member : value ∈ expectedAux blockLength start source) :
    value < start + source.length := by
  induction source generalizing start with
  | nil => simp [expectedAux] at member
  | cons item source induction =>
      rw [expectedAux, List.mem_append] at member
      rcases member with member | member
      · have equal : value = start := List.eq_of_mem_replicate member
        subst value
        simp
      · have bound := induction
          (nextIndex start (blockLength item)) member
        simp only [List.length_cons]
        by_cases empty : blockLength item = 0
        · simp [nextIndex, empty] at bound
          omega
        · simp [nextIndex, empty] at bound
          omega

/-- Every emitted query is below the source-list length, even when some
source items emit empty blocks. -/
theorem mem_indices_lt_length {Source : Type*}
    (blockLength : Source → Nat) (source : List Source)
    (value : Nat) (member : value ∈ indices blockLength source) :
    value < source.length := by
  rw [indices_eq_expected] at member
  simpa using expectedAux_mem_lt blockLength source 0 value member

noncomputable def markersComputableInPolyTime
    {Source : Type} [Fintype Source]
    (blockLength : Source → Nat) :
    TM2ComputableInPolyTime id id (markers blockLength) :=
  FiniteBlockTransducer.computableInPolyTime (itemMarkers blockLength)

noncomputable def incrementsComputableInPolyTime
    {Source : Type} [Fintype Source]
    (blockLength : Source → Nat) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (increments blockLength) := by
  unfold increments
  exact TM2CompositionMachine.computableInPolyTime
    (markersComputableInPolyTime blockLength)
    (FiniteUnaryFieldMap.computableInPolyTime Bool.toNat)

/-- Broadcast source indices over finite output blocks in polynomial time. -/
noncomputable def indicesComputableInPolyTime
    {Source : Type} [Fintype Source]
    (blockLength : Source → Nat) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (indices blockLength) := by
  unfold indices
  exact TM2CompositionMachine.computableInPolyTime
    (incrementsComputableInPolyTime blockLength)
    UnaryPrefixSumsMachine.computableInPolyTime

end LeanTrominoes.FiniteBlockIndices

end
