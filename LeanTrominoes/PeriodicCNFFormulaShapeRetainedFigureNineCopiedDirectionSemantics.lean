/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData

/-! # Semantics of finite retained Figure 9 copied-clause directions -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The semantic final route of every genuine copied source incidence exposes
exactly the finite direction used by `copiedClauseDescriptors`. -/
theorem normalizedCopiedRoute_firstDirection_eq_copiedFirstDirection
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source clauseIndex literalIndex) =
      copiedFirstDirection source clauseIndex literalIndex literal := by
  change _ =
    retainedFinalCopiedSourceFirstDirection
      source clauseIndex literalIndex literal
  exact
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_copied_firstDirection
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Substituting the finite copied-incidence direction lookup into one
genuine route-based copied clause leaves its exact descriptor unchanged. -/
theorem routedCopiedClauseProfile_eq_copiedClauseProfile
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource source).clauses.zipIdx) :
    routedCopiedClauseProfile source clauseIndex clause =
      copiedClauseProfile source clauseIndex clause := by
  unfold routedCopiedClauseProfile copiedClauseProfile
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.ext_getElem
  · simp [copiedOccurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceClause]
  · intro index leftBound rightBound
    have indexLt : index < clause.literals.length := by
      simpa [copiedOccurrenceClause,
        PeriodicEightOccurrenceSplit.occurrenceClause] using rightBound
    let literal := clause.literals[index]'indexLt
    have literalMember :
        (literal, index) ∈ clause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨indexLt, rfl⟩
    have directionEq :=
      normalizedCopiedRoute_firstDirection_eq_copiedFirstDirection
        (source := source)
        (sourceLocal := sourceLocal)
        (sourceWidth := sourceWidth)
        (sourceOccurrences := sourceOccurrences)
        (sourceClausesNonempty := sourceClausesNonempty)
        (clause := clause)
        (clauseIndex := clauseIndex)
        (clauseMember := clauseMember)
        (literal := literal)
        (literalIndex := index)
        (literalMember := literalMember)
    simp only [copiedOccurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceClause,
      List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    apply Prod.ext
    · rfl
    · simpa only [literal] using directionEq

/-- The complete semantic copied-clause descriptor prefix is exactly the
finite direct/fallback descriptor prefix. -/
theorem routedCopiedClauseDescriptors_eq_copiedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    routedCopiedClauseDescriptors source =
      copiedClauseDescriptors source := by
  unfold routedCopiedClauseDescriptors copiedClauseDescriptors
  apply List.map_congr_left
  intro taggedClause taggedClauseMember
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  exact routedCopiedClauseProfile_eq_copiedClauseProfile
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty taggedClauseMember

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
