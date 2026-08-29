/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordStreamSemantics
import LeanTrominoes.RetainedAngularFanNormalizedClauseRouteTailRecordSemantics

/-! # Direct-record correctness over normalized final clause sublists -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

private theorem finalCoordinatedSource_clause_of_normalizedIndexedMember
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedMember :
      taggedClause ∈ (deduplicatedClauses formula).zipIdx) :
    ∃ positionedClause,
      (positionedClause, taggedClause.2) ∈
          (finalCoordinatedSource formula).clauses.zipIdx ∧
        positionedClause.literals = taggedClause.1 := by
  have normalizedLookup :
      (deduplicatedClauses formula)[taggedClause.2]? =
        some taggedClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMember
  have mappedLookup :
      ((finalCoordinatedSource formula).clauses.map
        PositionedPeriodicClause.literals)[taggedClause.2]? =
          some taggedClause.1 := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact normalizedLookup
  rw [List.getElem?_map] at mappedLookup
  generalize positionedLookup :
      (finalCoordinatedSource formula).clauses[taggedClause.2]? =
        positionedOption at mappedLookup
  cases positionedOption with
  | none => simp at mappedLookup
  | some positionedClause =>
      simp only [Option.map_some, Option.some.injEq] at mappedLookup
      exact ⟨positionedClause,
        (List.mem_zipIdx_iff_getElem?).mpr positionedLookup,
        mappedLookup⟩

/-- Pointwise direct-choice correctness over an indexed normalized clause
sublist. The actual retained clause position is recovered internally and is
irrelevant to the record word. -/
theorem retainedFinalNormalizedClauseRouteTailRecordStream_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (start : Nat)
    (clauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (clausesMember :
      ∀ taggedClause ∈ clauses.zipIdx start,
        taggedClause ∈ (deduplicatedClauses formula).zipIdx)
    (clausesNonempty :
      ∀ taggedClause ∈ clauses.zipIdx start,
        taggedClause.1 ≠ [])
    (clausesWidth :
      ∀ taggedClause ∈ clauses.zipIdx start,
        taggedClause.1.length ≤ 3)
    (choicesSome :
      ∀ taggedClause ∈ clauses.zipIdx start,
        ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
          ∃ choice,
            retainedFinalDirectSourceRouteChoice?
                formula taggedClause.2 taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordStream
        ((clauses.zipIdx start).map fun taggedClause =>
          retainedFinalDirectClauseRouteTailRecordQuery
            formula taggedClause.2 ⟨(0, 0), taggedClause.1⟩) =
      retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
        formula start clauses := by
  unfold retainedDirectClauseRouteTailRecordStream
    retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
    retainedFinalDirectClauseSemanticRouteTailRecordTokens
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedMember
  rcases finalCoordinatedSource_clause_of_normalizedIndexedMember
      formula taggedClause (clausesMember taggedClause taggedMember) with
    ⟨positionedClause, positionedMember, literalsEq⟩
  have correct := retainedFinalDirectClauseRouteTailRecordTokens_eq
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty positionedMember
    (by simpa only [literalsEq] using
      clausesNonempty taggedClause taggedMember)
    (by simpa only [literalsEq] using
      clausesWidth taggedClause taggedMember)
    (by
      intro taggedLiteral taggedLiteralMember
      apply choicesSome taggedClause taggedMember taggedLiteral
      simpa only [literalsEq] using taggedLiteralMember)
  rcases positionedClause with ⟨position, literals⟩
  simp only at literalsEq
  subst literals
  exact correct

end PeriodicEightOccurrenceSplit
end LeanTrominoes
