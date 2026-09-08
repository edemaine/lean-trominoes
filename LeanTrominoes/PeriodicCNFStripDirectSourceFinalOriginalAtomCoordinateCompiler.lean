/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripOriginalAtomCoordinateLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Original-atom coordinates in the exact final occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

local instance finalOriginalCoordinateVariableDecidableEq : DecidableEq Variable :=
  originalAtomWordVariableDecidableEq

private theorem input_eq_mk {input : DelimitedBinaryWords.Input} {words : List (List Bool)}
    (equal : input.words = words) : input = ⟨words⟩ :=
  DelimitedBinaryWords.eq_of_words_eq equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance finalOriginalCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The actual final five-family atom presentation, including repeated occurrences. -/
def directSourceFinalCoordinateAtoms (symbols : List encoding.Γ) :
    List (WrappedPeriodicPlanarSATVariable Variable) :=
  (directSourceFinalFiveFamilyClauses decider symbols).flatMap fun clause =>
    clause.map fun literal => literal.atom

/-- The already compiled compact key stream names these exact occurrence atoms. -/
theorem directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms
    (symbols : List encoding.Γ) :
    directSourceFinalCompactOccurrenceAtomWords decider symbols =
      ⟨(directSourceFinalCoordinateAtoms decider symbols).map
        (directSourceFinalCompactAtomWord (directSourceFormula decider symbols))⟩ := by
  apply DelimitedBinaryWords.eq_of_words_eq
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_fiveFamilies]
  simp [directSourceFinalCoordinateAtoms, List.map_flatMap, List.map_map, Function.comp_def]

/-- Original-atom coordinates selected in the final occurrence order, with
zeros in positions belonging to other constructor families. -/
def directSourceFinalOriginalAtomCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)
    (directSourceOriginalAtomWords decider symbols)
    (directSourceOriginalAtomCoordinates decider horizontal keepPositive symbols)

/-- Every input decider has an actual polynomial-time compiler for this
occurrence-aligned coordinate contribution. -/
noncomputable def directSourceFinalOriginalAtomCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOriginalAtomCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOriginalAtomCoordinates
    exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime
      (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceOriginalAtomWords decider)
      (directSourceOriginalAtomCoordinates decider horizontal keepPositive)
      (fun symbols => (directSourceOriginalAtomWords_length_coordinates
        decider horizontal keepPositive symbols).symm)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
      (directSourceOriginalAtomWordsComputableInPolyTime decider)
      (directSourceOriginalAtomCoordinatesComputableInPolyTime decider horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- Each occurrence receives its exact canonical original-atom coordinate
contribution, with no ordering or source-emission assumption. -/
theorem directSourceFinalOriginalAtomCoordinates_eq_contributions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalOriginalAtomCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map
        (originalAtomCoordinateContribution (directSourceFormula decider symbols)
          horizontal keepPositive) := by
  have keysEq := input_eq_mk (directSourceOriginalAtomWords_eq_compactWords decider symbols)
  have coordinatesEq : directSourceOriginalAtomCoordinates decider horizontal keepPositive symbols =
      (directSourceFormula decider symbols).variableOccurrences.dedup.map fun atom =>
        originalAtomCoordinateField (directSourceFormula decider symbols)
          horizontal keepPositive ⟨.atom atom⟩ := by
    exact directSourceOriginalAtomCoordinates_eq_positions decider horizontal keepPositive symbols
  unfold directSourceFinalOriginalAtomCoordinates
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_coordinateAtoms, keysEq, coordinatesEq]
  exact originalAtomCoordinateLookup_eq_contributions (directSourceFormula decider symbols)
    (directSourceFinalCoordinateAtoms decider symbols) horizontal keepPositive

/-- All four contributions align with the same complete occurrence presentation. -/
theorem directSourceFinalOriginalAtomCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalOriginalAtomCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCoordinateAtoms decider symbols).length := by
  rw [directSourceFinalOriginalAtomCoordinates_eq_contributions, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
