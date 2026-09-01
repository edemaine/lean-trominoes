/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalBendTaggedBendInputLookup
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Recovering occurrences from tagged final-bend literal evidence -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Recover the positioned final occurrence selected by a tagged bend
literal. -/
noncomputable def FinalBendTaggedLiteralInput.occurrence
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Fin 2}
    (input : FinalBendTaggedLiteralInput source taggedBend clauseIndex
      literal literalIndex) :
    FinalBendIndexedOccurrence Variable := by
  let retained := PeriodicThreeSATThree.formula source
  let normalizedClause := normalizedBendClauseAt retained taggedBend
  have mappedLookup :
      ((finalCoordinatedSource retained).clauses.map
          PositionedPeriodicClause.literals)[clauseIndex]? =
        some normalizedClause := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact input.bendInput.clauseLookup
  rw [List.getElem?_map] at mappedLookup
  generalize positionedLookup :
      (finalCoordinatedSource retained).clauses[clauseIndex]? =
        positionedOption at mappedLookup
  cases positionedOption with
  | none => simp at mappedLookup
  | some positionedClause =>
      simp only [Option.map_some, Option.some.injEq] at mappedLookup
      have positionedLiteralMember :
          (literal, literalIndex.val) ∈
            positionedClause.literals.zipIdx := by
        rw [mappedLookup]
        simpa only [retained, normalizedClause] using input.literalMember
      exact
        { source := source
          sourceLocal :=
            input.bendInput.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
          sourceWidth :=
            input.bendInput.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
          sourceClausesNonempty :=
            input.bendInput.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty
          positiveOffsets :=
            input.bendInput.sourceInput.sourceFacts.positiveOffsets
          taggedBend := taggedBend
          clauseIndex := clauseIndex
          taggedBendIndexed := input.bendInput.taggedBendIndexed
          clause := positionedClause
          clauseMember :=
            (List.mem_zipIdx_iff_getElem?).mpr positionedLookup
          literal := literal
          literalIndex := literalIndex
          literalMember := positionedLiteralMember }

end PeriodicEightOccurrenceSplit
end LeanTrominoes
