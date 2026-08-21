/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomWordData

/-! # Formula semantics of extracted source atom words -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomWords

theorem tokens_flatMap {α : Type} (values : List α)
    (function : α → List SourceOccurrenceTokens.Token) :
    tokens (values.flatMap function) =
      values.flatMap fun value => tokens (function value) := by
  unfold tokens
  exact List.flatMap_assoc

theorem tokens_clauseTokens (clause : PeriodicClause Nat) :
    tokens (SourceOccurrenceTokens.clauseTokens clause) =
      clause.zipIdx.flatMap fun tagged =>
        DelimitedBinaryWords.wordTokens
          (SourceOccurrenceAtomPairs.atomWord tagged.1.atom) := by
  unfold SourceOccurrenceTokens.clauseTokens
  change tokens
      ([.clause (SourceOccurrenceTokens.clauseArity clause.length)] ++
        (clause.zipIdx.flatMap fun tagged =>
          SourceOccurrenceTokens.literalTokens tagged.2 tagged.1)) = _
  rw [tokens_append, tokens_flatMap]
  simp only [tokens, block, List.flatMap_singleton, List.nil_append]
  apply List.flatMap_congr
  intro tagged taggedMem
  exact tokens_literalTokens tagged.2 tagged.1

theorem occurrenceAtomWords_eq_clauses (formula : PeriodicCNF Nat) :
    SourceOccurrenceAtomPairs.occurrenceAtomWords formula =
      formula.clauses.flatMap fun clause =>
        clause.zipIdx.map fun tagged =>
          SourceOccurrenceAtomPairs.atomWord tagged.1.atom := by
  unfold SourceOccurrenceAtomPairs.occurrenceAtomWords
    PeriodicThreeSATThree.taggedLiterals
  rw [List.map_flatMap]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 formula.clauses]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMem
  simp [List.map_map, Function.comp_def]

/-- The fixed block map extracts exactly the canonical encoded list of atom
words in literal-presentation order. -/
theorem tokens_formulaTokens (formula : PeriodicCNF Nat) :
    tokens (SourceOccurrenceTokens.formulaTokens formula) =
      DelimitedBinaryWords.encode
        ⟨SourceOccurrenceAtomPairs.occurrenceAtomWords formula⟩ := by
  unfold SourceOccurrenceTokens.formulaTokens
    DelimitedBinaryWords.encode
  rw [tokens_flatMap, occurrenceAtomWords_eq_clauses,
    List.flatMap_assoc]
  apply List.flatMap_congr
  intro clause clauseMem
  rw [tokens_clauseTokens]
  rw [List.flatMap_map]

end SourceOccurrenceAtomWords
end PeriodicCNF
end LeanTrominoes
