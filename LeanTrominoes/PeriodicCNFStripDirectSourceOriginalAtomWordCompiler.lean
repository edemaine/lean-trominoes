/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordAffixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceOriginalAtomCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Compact original-atom keys aligned with their coordinate columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

-- Match the structural equality used when the original source keys were defined.
local instance originalAtomWordVariableDecidableEq : DecidableEq Variable :=
  instDecidableEqProd

/-- The source-atom constructor, indexed-source tag, and terminated unary index. -/
def directSourceOriginalAtomIndexWord (index : Nat) : List Bool :=
  [true, false, false] ++ CarrierKeyWords.natField index

private theorem originalAtomIndexWords_eq_compactWords
    (source : PeriodicCNF Variable) :
    (List.range source.variableOccurrences.dedup.length).map directSourceOriginalAtomIndexWord =
      source.variableOccurrences.dedup.map fun atom =>
        directSourceFinalCompactAtomWord source ⟨.atom atom⟩ := by
  rw [← List.map_idxOf_self_eq_range_beq _ (List.nodup_dedup _), List.map_map]
  apply List.map_congr_left
  intro atom atomMember
  simp [directSourceOriginalAtomIndexWord, directSourceFinalCompactAtomWord,
    RetainedCompactAtomWords.word, DirectSourceFinalIndexedAtomWords.sourceVariableWord,
    List.mem_dedup.mp atomMember]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directOriginalAtomWordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One exact compact key per original atom, in coordinate-column order. -/
def directSourceOriginalAtomWords (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWordAffix.words [true, false, false] [true]
    (UnaryFieldBinaryWords.words (directSourceOriginalAtomIndices decider symbols))

noncomputable def directSourceOriginalAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token id DelimitedBinaryWords.finEncoding.encode
      (directSourceOriginalAtomWords decider) := by
  change TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
    (fun symbols => DelimitedBinaryWordAffix.words [true, false, false] [true]
      (UnaryFieldBinaryWords.words (directSourceOriginalAtomIndices decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directSourceOriginalAtomIndicesComputableInPolyTime decider)
      UnaryFieldBinaryWords.wordsComputableInPolyTime)
    (DelimitedBinaryWordAffix.computableInPolyTime [true, false, false] [true])

theorem directSourceOriginalAtomWords_eq_indices (symbols : List encoding.Γ) :
    (directSourceOriginalAtomWords decider symbols).words =
      (directSourceOriginalAtomIndices decider symbols).map directSourceOriginalAtomIndexWord := by
  simp [directSourceOriginalAtomWords, DelimitedBinaryWordAffix.words,
    UnaryFieldBinaryWords.words, UnaryFieldBinaryWords.word,
    directSourceOriginalAtomIndexWord, CarrierKeyWords.natField,
    List.map_map, Function.comp_def]

/-- The keys are precisely the compact words already used by the final
occurrence-identity compiler. -/
theorem directSourceOriginalAtomWords_eq_compactWords (symbols : List encoding.Γ) :
    (directSourceOriginalAtomWords decider symbols).words =
      (directSourceFormula decider symbols).variableOccurrences.dedup.map fun atom =>
        directSourceFinalCompactAtomWord (directSourceFormula decider symbols) ⟨.atom atom⟩ := by
  rw [directSourceOriginalAtomWords_eq_indices, directSourceOriginalAtomIndices_eq_range]
  exact originalAtomIndexWords_eq_compactWords (directSourceFormula decider symbols)

/-- Distinct original atoms have distinct dictionary keys. -/
theorem directSourceOriginalAtomWords_nodup (symbols : List encoding.Γ) :
    (directSourceOriginalAtomWords decider symbols).words.Nodup := by
  rw [directSourceOriginalAtomWords_eq_indices, directSourceOriginalAtomIndices_eq_range]
  apply List.Nodup.map _ List.nodup_range
  intro first second wordsEq
  have lengthsEq := congrArg List.length wordsEq
  simpa [directSourceOriginalAtomIndexWord, CarrierKeyWords.natField] using lengthsEq

/-- Every key has exactly one aligned entry in each signed coordinate column. -/
theorem directSourceOriginalAtomWords_length_coordinates
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceOriginalAtomWords decider symbols).words.length =
      (directSourceOriginalAtomCoordinates decider horizontal keepPositive symbols).length := by
  rw [directSourceOriginalAtomWords_eq_indices, directSourceOriginalAtomCoordinates_length,
    List.length_map, directSourceOriginalAtomIndices_eq_range, List.length_range]

end LeanTrominoes.PeriodicCNFStripReduction

end
