/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeOriginalOccurrenceOrder

/-!
# Ordered original occurrences through unit elimination

Unit elimination preserves the presentation order of every original
exact-one literal.  A unit literal moves into the first generated ternary
clause and is negated; every non-unit clause is lifted pointwise into one
generated clause.  This file records those cases as an explicit pairing of
tagged output and source occurrences.

The resulting lookup theorem identifies each output occurrence slot with
the identical source slot, ready for pointwise transport of inherited route
directions.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

abbrev OriginalOccurrencePair (Variable : Type*) :=
  PeriodicOneInThreeToThreeDM.TaggedOccurrence
      (OneInThreeNoUnitVariable Variable) ×
    PeriodicOneInThreeToThreeDM.TaggedOccurrence Variable

def originalOccurrencePairIf
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (outputLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable))
    (outputClauseIndex outputLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceClauseIndex sourceLiteralIndex : Nat) :
    List (OriginalOccurrencePair Variable) :=
  if sourceLiteral.atom = atom then
    [((outputLiteral, outputClauseIndex, outputLiteralIndex),
      (sourceLiteral, sourceClauseIndex, sourceLiteralIndex))]
  else
    []

def mappedClauseOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputClauseIndex sourceClauseIndex : Nat) :
    Nat → PeriodicClause Variable →
      List (OriginalOccurrencePair Variable)
  | _, [] => []
  | literalIndex, literal :: rest =>
      originalOccurrencePairIf atom
          (liftLiteral literal) outputClauseIndex literalIndex
          literal sourceClauseIndex literalIndex ++
        mappedClauseOriginalOccurrencePairs atom
          outputClauseIndex sourceClauseIndex
          (literalIndex + 1) rest

theorem mappedClauseOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (outputClauseIndex sourceClauseIndex literalIndex : Nat)
    (source : PeriodicClause Variable) :
    (mappedClauseOriginalOccurrencePairs atom outputClauseIndex
        sourceClauseIndex literalIndex source).map Prod.fst =
      (source.zipIdx literalIndex |>.map fun taggedLiteral =>
        (liftLiteral taggedLiteral.1,
          outputClauseIndex, taggedLiteral.2)).filter
        (fun tagged => tagged.1.atom = Sum.inl atom) := by
  induction source generalizing literalIndex with
  | nil =>
      rfl
  | cons literal rest induction =>
      by_cases literalAtom : literal.atom = atom
      · simp [mappedClauseOriginalOccurrencePairs,
          originalOccurrencePairIf, literalAtom,
          liftLiteral, induction]
      · simp [mappedClauseOriginalOccurrencePairs,
          originalOccurrencePairIf, literalAtom,
          liftLiteral, induction]

theorem mappedClauseOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (outputClauseIndex sourceClauseIndex literalIndex : Nat)
    (source : PeriodicClause Variable) :
    (mappedClauseOriginalOccurrencePairs atom outputClauseIndex
        sourceClauseIndex literalIndex source).map Prod.snd =
      (source.zipIdx literalIndex |>.map fun taggedLiteral =>
        (taggedLiteral.1,
          sourceClauseIndex, taggedLiteral.2)).filter
        (fun tagged => tagged.1.atom = atom) := by
  induction source generalizing literalIndex with
  | nil =>
      rfl
  | cons literal rest induction =>
      by_cases literalAtom : literal.atom = atom
      · simp [mappedClauseOriginalOccurrencePairs,
          originalOccurrencePairIf, literalAtom, induction]
      · simp [mappedClauseOriginalOccurrencePairs,
          originalOccurrencePairIf, literalAtom, induction]

def clauseOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat) :
    PeriodicClause Variable → List (OriginalOccurrencePair Variable)
  | [] => []
  | [literal] =>
      originalOccurrencePairIf atom
        (PeriodicOneInThree.negate (liftLiteral literal))
        outputStart 0 literal sourceClauseIndex 0
  | first :: second :: rest =>
      mappedClauseOriginalOccurrencePairs atom
        outputStart sourceClauseIndex 0
        (first :: second :: rest)

theorem clauseOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.fst =
      (PeriodicOneInThree.taggedLiteralsFrom outputStart
        (clauseClauses sourceClauseIndex source)).filter
          (fun tagged => tagged.1.atom = Sum.inl atom) := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseOriginalOccurrencePairs,
      PeriodicOneInThree.taggedLiteralsFrom,
      clauseClauses, auxiliary]
  · rcases rest with _ | ⟨second, rest⟩
    · by_cases firstAtom : first.atom = atom
      · simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom,
          PeriodicOneInThree.taggedLiteralsFrom,
          clauseClauses, auxiliary, liftLiteral,
          PeriodicOneInThree.negate]
      · simp [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, firstAtom,
          PeriodicOneInThree.taggedLiteralsFrom,
          clauseClauses, auxiliary, liftLiteral,
          PeriodicOneInThree.negate]
    · simpa [clauseOriginalOccurrencePairs,
        PeriodicOneInThree.taggedLiteralsFrom,
        clauseClauses, List.zipIdx_map,
        Function.comp_def] using
        mappedClauseOriginalOccurrencePairs_fst
          atom outputStart sourceClauseIndex 0
          (first :: second :: rest)

theorem clauseOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable) :
    (clauseOriginalOccurrencePairs
        atom outputStart sourceClauseIndex source).map Prod.snd =
      (source.zipIdx.map fun taggedLiteral =>
        (taggedLiteral.1, sourceClauseIndex, taggedLiteral.2)).filter
          (fun tagged => tagged.1.atom = atom) := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · by_cases firstAtom : first.atom = atom
      <;> simp [clauseOriginalOccurrencePairs,
        originalOccurrencePairIf, firstAtom]
    · simpa [clauseOriginalOccurrencePairs] using
        mappedClauseOriginalOccurrencePairs_snd
          atom outputStart sourceClauseIndex 0
          (first :: second :: rest)

def formulaOriginalOccurrencePairsFrom
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) :
    Nat → Nat → List (PeriodicClause Variable) →
      List (OriginalOccurrencePair Variable)
  | _, _, [] => []
  | outputStart, sourceStart, clause :: rest =>
      clauseOriginalOccurrencePairs
          atom outputStart sourceStart clause ++
        formulaOriginalOccurrencePairsFrom atom
          (outputStart +
            (clauseClauses sourceStart clause).length)
          (sourceStart + 1) rest

theorem formulaOriginalOccurrencePairsFrom_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart clauses).map Prod.fst =
      (PeriodicOneInThree.taggedLiteralsFrom outputStart
        (formulaClausesFrom sourceStart clauses)).filter
          (fun tagged => tagged.1.atom = Sum.inl atom) := by
  induction clauses generalizing outputStart sourceStart with
  | nil =>
      rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom,
        List.map_append,
        clauseOriginalOccurrencePairs_fst]
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.taggedLiteralsFrom_append]
      rw [List.filter_append, induction]

theorem formulaOriginalOccurrencePairsFrom_snd
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart clauses).map Prod.snd =
      (PeriodicOneInThree.taggedLiteralsFrom
        sourceStart clauses).filter
          (fun tagged => tagged.1.atom = atom) := by
  induction clauses generalizing outputStart sourceStart with
  | nil =>
      rfl
  | cons clause rest induction =>
      rw [formulaOriginalOccurrencePairsFrom,
        List.map_append,
        clauseOriginalOccurrencePairs_snd]
      rw [show
        PeriodicOneInThree.taggedLiteralsFrom
            sourceStart (clause :: rest) =
          (clause.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, sourceStart, taggedLiteral.2)) ++
            PeriodicOneInThree.taggedLiteralsFrom
              (sourceStart + 1) rest by
          simp [PeriodicOneInThree.taggedLiteralsFrom]]
      rw [List.filter_append,
        induction
          (outputStart +
            (clauseClauses sourceStart clause).length)
          (sourceStart + 1)]

def formulaOriginalOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List (OriginalOccurrencePair Variable) :=
  formulaOriginalOccurrencePairsFrom atom 0 0 source.clauses

theorem formulaOriginalOccurrencePairs_fst
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (formulaOriginalOccurrencePairs source atom).map Prod.fst =
      PeriodicOneInThreeToThreeDM.occurrencesOf
        (formula source) (Sum.inl atom) := by
  simpa [formulaOriginalOccurrencePairs,
    PeriodicOneInThree.taggedLiteralsFrom,
    PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals, formula,
    formulaClausesFrom] using
    formulaOriginalOccurrencePairsFrom_fst atom 0 0 source.clauses

theorem formulaOriginalOccurrencePairs_snd
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (formulaOriginalOccurrencePairs source atom).map Prod.snd =
      PeriodicOneInThreeToThreeDM.occurrencesOf source atom := by
  simpa [formulaOriginalOccurrencePairs,
    PeriodicOneInThree.taggedLiteralsFrom,
    PeriodicOneInThreeToThreeDM.occurrencesOf,
    PeriodicThreeSATThree.taggedLiterals] using
    formulaOriginalOccurrencePairsFrom_snd
      atom 0 0 source.clauses

/-- Every ordered occurrence of an embedded source variable is paired with
the source occurrence in the same occurrence slot. -/
theorem exists_source_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (output :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeNoUnitVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source) (Sum.inl atom) slot =
        some output) :
    ∃ sourceOccurrence,
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source atom slot = some sourceOccurrence ∧
        (output, sourceOccurrence) ∈
          formulaOriginalOccurrencePairs source atom := by
  let pairs := formulaOriginalOccurrencePairs source atom
  have outputLookup :
      (pairs.map Prod.fst)[slot.index]? = some output := by
    rw [show
      pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (formula source) (Sum.inl atom) by
        simpa [pairs] using
          formulaOriginalOccurrencePairs_fst source atom]
    exact lookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at outputLookup
  rcases outputLookup with
    ⟨pair, pairLookup, pairFst⟩
  have sourceLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          source atom slot = some pair.2 := by
    change
      (PeriodicOneInThreeToThreeDM.occurrencesOf
        source atom)[slot.index]? = some pair.2
    rw [← formulaOriginalOccurrencePairs_snd source atom,
      List.getElem?_map, pairLookup]
    rfl
  refine ⟨pair.2, sourceLookup, ?_⟩
  rw [← pairFst]
  exact List.mem_iff_getElem?.mpr ⟨slot.index, pairLookup⟩

end PeriodicOneInThreeNoUnits
end LeanTrominoes
