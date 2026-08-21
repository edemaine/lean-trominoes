/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenData
import LeanTrominoes.PeriodicThreeSATThree

/-! # Binary atom pairs for promised-source occurrence enumeration -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomPairs

open Turing

/-- Canonical Boolean word carried by one natural-valued atom field. -/
def atomWord (atom : Nat) : List Bool :=
  (PartrecToTM2.trNat atom).map SourceOccurrenceTokens.nativeBit

@[simp] theorem nativeBit_partrecBit (bit : Bool) :
    SourceOccurrenceTokens.nativeBit (Complexity.partrecBit bit) = bit := by
  cases bit <;> rfl

@[simp] theorem atomWord_eq_encodeNat (atom : Nat) :
    atomWord atom = _root_.Computability.encodeNat atom := by
  unfold atomWord
  rw [Complexity.partrec_trNat_eq_map_encodeNat]
  simp [List.map_map, Function.comp_def]

theorem atomWord_injective : Function.Injective atomWord := by
  intro first second equality
  rw [atomWord_eq_encodeNat, atomWord_eq_encodeNat] at equality
  have decoded := congrArg _root_.Computability.decodeNat equality
  simpa using decoded

theorem decide_atomWord_eq (first second : Nat) :
    decide (atomWord first = atomWord second) = decide (first = second) := by
  by_cases equality : first = second
  · subst second
    simp
  · have wordNe : atomWord first ≠ atomWord second := fun wordEq =>
      equality (atomWord_injective wordEq)
    simp only [wordNe, equality, decide_false]

/-- Atom bitstrings in literal-presentation order, including repetitions. -/
def occurrenceAtomWords (formula : PeriodicCNF Nat) : List (List Bool) :=
  (PeriodicThreeSATThree.taggedLiterals formula).map fun tagged =>
    atomWord tagged.1.atom

/-- Row-major ordered product of one occurrence-word list with itself. -/
def orderedPairs (words : List (List Bool)) :
    List (List Bool × List Bool) :=
  words.flatMap fun first => words.map fun second => (first, second)

/-- Delimited comparator input for every ordered pair of source
occurrences. -/
def input (formula : PeriodicCNF Nat) : DelimitedBinaryWordPairs.Input :=
  ⟨orderedPairs (occurrenceAtomWords formula)⟩

theorem equalities_orderedPairs (words : List (List Bool)) :
    DelimitedBinaryWordPairs.equalities ⟨orderedPairs words⟩ =
      words.flatMap fun first =>
        words.map fun second => decide (first = second) := by
  unfold DelimitedBinaryWordPairs.equalities orderedPairs
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro first firstMem
  simp [List.map_map, Function.comp_def]

/-- Semantic row-major atom-equality matrix in literal-presentation order. -/
def atomEqualityMatrix (formula : PeriodicCNF Nat) : List Bool :=
  (PeriodicThreeSATThree.taggedLiterals formula).flatMap fun first =>
    (PeriodicThreeSATThree.taggedLiterals formula).map fun second =>
      decide (first.1.atom = second.1.atom)

@[simp] theorem equalities_input (formula : PeriodicCNF Nat) :
    DelimitedBinaryWordPairs.equalities (input formula) =
      atomEqualityMatrix formula := by
  unfold input
  rw [equalities_orderedPairs]
  unfold occurrenceAtomWords atomEqualityMatrix
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first firstMem
  rw [List.map_map]
  apply List.map_congr_left
  intro second secondMem
  exact decide_atomWord_eq first.1.atom second.1.atom

end SourceOccurrenceAtomPairs
end PeriodicCNF
end LeanTrominoes
