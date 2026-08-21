/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataSize
import LeanTrominoes.PeriodicThreeSATThree

/-! # Copied incidence data for occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Lift one source incidence to the matching incidence of its copied
occurrence clause. -/
def occurrenceIncidence {Variable : Type*}
    (incidence : CNFIncidence Variable) :
    CNFIncidence (ThreeOccurrenceVariable Variable) where
  clauseIndex := incidence.clauseIndex
  clause := occurrenceClause incidence.clauseIndex incidence.clause
  literalIndex := incidence.literalIndex
  literal := occurrenceLiteral incidence.clauseIndex
    incidence.literalIndex incidence.literal

/-- The copied incidences, still in the source formula's exact presentation
order. -/
def occurrenceIncidences {Variable : Type*}
    (source : PeriodicCNF Variable) :
    List (CNFIncidence (ThreeOccurrenceVariable Variable)) :=
  (PeriodicCNF.incidencesWithMetadata source).map occurrenceIncidence

@[simp] theorem occurrenceIncidence_clauseIndex
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).clauseIndex =
      incidence.clauseIndex := rfl

@[simp] theorem occurrenceIncidence_clause
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).clause =
      occurrenceClause incidence.clauseIndex incidence.clause := rfl

@[simp] theorem occurrenceIncidence_literalIndex
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).literalIndex =
      incidence.literalIndex := rfl

@[simp] theorem occurrenceIncidence_literal
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).literal =
      occurrenceLiteral incidence.clauseIndex
        incidence.literalIndex incidence.literal := rfl

@[simp] theorem occurrenceIncidence_atom
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).literal.atom =
      (incidence.literal.atom, incidence.clauseIndex,
        incidence.literalIndex) := rfl

@[simp] theorem occurrenceIncidence_literal_offset
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).literal.offset =
      incidence.literal.offset := rfl

@[simp] theorem occurrenceIncidence_literal_value
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    (occurrenceIncidence incidence).literal.value =
      incidence.literal.value := rfl

/-- Copying variables preserves the anchor of each presented clause. -/
@[simp] theorem clauseAnchor_occurrenceClause
    {Variable : Type*} (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    PeriodicCNF.clauseAnchor (occurrenceClause clauseIndex clause) =
      PeriodicCNF.clauseAnchor clause := by
  cases clause <;> rfl

/-- The copied prefix contains exactly one incidence per source literal. -/
@[simp] theorem occurrenceIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceIncidences source).length =
      PeriodicCNF.presentationLiteralCount source := by
  simp [occurrenceIncidences]

end PeriodicThreeSATThree
end LeanTrominoes
