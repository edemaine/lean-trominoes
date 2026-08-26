/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectChoiceFromMetadata
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceDirectionQuery
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses

/-! # Direct semantics of one final copied-source direction query -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- At a genuine literal of a final clause, a known raw direct-atlas lookup
determines the exact finite query emitted by the final copied source. -/
theorem retainedFinalCopiedSourceDirectionQuery_eq_direct_of_metadata_raw
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ sourceClause ∈ formula.clauses, sourceClause ≠ [])
    (clauseIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseLookup :
      (deduplicatedClauses formula)[clauseIndex]? = some clause)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (literalIndex : Nat)
    (literalMember : (literal, literalIndex) ∈ clause.zipIdx)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some metadata)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source = .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex))
    (rawChoice : RetainedDirectSourceRouteChoice)
    (rawLookup :
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex = some rawChoice) :
    retainedFinalCopiedSourceDirectionQuery
        formula clauseIndex literalIndex literal =
      .direct rawChoice.normalizedDirectionQuery := by
  have mappedClauseLookup :
      ((finalCoordinatedSource formula).clauses.map
          PositionedPeriodicClause.literals)[clauseIndex]? =
        some clause := by
    rw [finalCoordinatedSource_clauseLiterals_eq]
    exact clauseLookup
  rw [List.getElem?_map] at mappedClauseLookup
  generalize finalClauseLookup :
      (finalCoordinatedSource formula).clauses[clauseIndex]? =
        finalClauseOption at mappedClauseLookup
  cases finalClauseOption with
  | none => simp at mappedClauseLookup
  | some finalClause =>
      simp only [Option.map_some, Option.some.injEq]
        at mappedClauseLookup
      have finalClauseMember :
          (finalClause, clauseIndex) ∈
            (finalCoordinatedSource formula).clauses.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr finalClauseLookup
      have finalLiteralMember :
          (literal, literalIndex) ∈ finalClause.literals.zipIdx := by
        rw [mappedClauseLookup]
        exact literalMember
      rcases
          exists_finalDirectChoiceRaw_of_metadata_direct
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty finalClauseMember finalLiteralMember
            metadata metadataLookup directCases with
        ⟨choice, selectedRawChoice, choiceLookup,
          selectedRawLookup, choiceEq⟩
      have selectedRawChoiceEq : selectedRawChoice = rawChoice :=
        Option.some.inj (selectedRawLookup.symm.trans rawLookup)
      subst selectedRawChoice
      unfold retainedFinalCopiedSourceDirectionQuery
      rw [choiceLookup]
      simp only
      rw [choiceEq]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
