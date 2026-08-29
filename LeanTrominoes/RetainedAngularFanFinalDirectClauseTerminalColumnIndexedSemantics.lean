/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnSemantics
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation

/-! # Indexed semantics of direct final terminal columns -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

private theorem retainedFinalDirectClauseTerminalCoordinates_ofList
    (items : List
      (PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile ×
        RetainedFinalCopiedSourceDirectionQuery))
    (width : items.length ≤ 3) :
    retainedFinalDirectClauseTerminalCoordinates
        (RetainedFinalCopiedClauseQuery.ofList items) =
      items.flatMap fun item =>
        (retainedFinalDirectTerminalCoordinate? item.2).toList := by
  rcases items with _ | ⟨first, rest⟩
  · rfl
  rcases rest with _ | ⟨second, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList,
      retainedFinalDirectClauseTerminalCoordinates]
  rcases rest with _ | ⟨third, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    rcases second with ⟨secondProfile, secondQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList,
      retainedFinalDirectClauseTerminalCoordinates]
  rcases rest with _ | ⟨fourth, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    rcases second with ⟨secondProfile, secondQuery⟩
    rcases third with ⟨thirdProfile, thirdQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList,
      retainedFinalDirectClauseTerminalCoordinates]
  · simp only [List.length_cons] at width
    omega

/-- For a width-three literal list, packing a final clause query preserves
the presentation order of every successful direct terminal query. -/
theorem retainedFinalDirectClauseTerminalCoordinates_queryOfLiterals
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (width : literals.length ≤ 3) :
    retainedFinalDirectClauseTerminalCoordinates
        (retainedFinalCopiedClauseQueryOfLiterals
          formula clauseIndex literals) =
      literals.zipIdx.flatMap fun taggedLiteral =>
        (retainedFinalDirectTerminalCoordinate?
          (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex taggedLiteral.2 taggedLiteral.1)).toList := by
  unfold retainedFinalCopiedClauseQueryOfLiterals
  rw [retainedFinalDirectClauseTerminalCoordinates_ofList]
  · rw [List.flatMap_map]
  · simpa using width

/-- If every incidence in a width-three clause has a successful direct
choice, the packed query column is its actual unscaled terminal column. -/
theorem retainedFinalDirectClauseTerminalCoordinates_queryOfLiterals_eq_actual
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (width : literals.length ≤ 3)
    (choices : ∀ taggedLiteral ∈ literals.zipIdx,
      ∃ choice,
        retainedFinalDirectSourceRouteChoice?
            formula clauseIndex taggedLiteral.2 =
          some choice) :
    retainedFinalDirectClauseTerminalCoordinates
        (retainedFinalCopiedClauseQueryOfLiterals
          formula clauseIndex literals) =
      literals.zipIdx.map fun taggedLiteral =>
        ofLex (retainedOccurrenceTerminalCoordinate
          (finalCoordinatedSourceRoutes formula)
          (taggedLiteral.1.atom, clauseIndex, taggedLiteral.2)) := by
  rw [retainedFinalDirectClauseTerminalCoordinates_queryOfLiterals
    formula clauseIndex literals width]
  calc
    _ = literals.zipIdx.flatMap (fun taggedLiteral =>
          [ofLex (retainedOccurrenceTerminalCoordinate
            (finalCoordinatedSourceRoutes formula)
            (taggedLiteral.1.atom, clauseIndex, taggedLiteral.2))]) := by
      apply List.flatMap_congr
      intro taggedLiteral taggedLiteralMember
      rcases choices taggedLiteral taggedLiteralMember with
        ⟨choice, choiceLookup⟩
      rw [retainedFinalDirectTerminalCoordinate?_sourceQuery,
        choiceLookup]
      rfl
    _ = _ := by
      simpa [Function.comp_def] using
        (List.flatMap_pure_eq_map
          (fun taggedLiteral =>
            ofLex (retainedOccurrenceTerminalCoordinate
              (finalCoordinatedSourceRoutes formula)
              (taggedLiteral.1.atom, clauseIndex, taggedLiteral.2)))
          literals.zipIdx)

/-- A whole explicitly indexed direct family contributes exactly its actual
unscaled terminal coordinates. -/
theorem retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (clauses :
      List (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (choices : ∀ taggedClause ∈ clauses.zipIdx start,
      ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
        ∃ choice,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 =
            some choice) :
    retainedFinalDirectTerminalCoordinates
        (retainedFinalIndexedClauseQueriesFrom
          formula start clauses) =
      retainedFinalTerminalCoordinatesFrom
        (finalCoordinatedSourceRoutes formula) start clauses := by
  unfold retainedFinalDirectTerminalCoordinates
    retainedFinalIndexedClauseQueriesFrom
    retainedFinalTerminalCoordinatesFrom
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  exact
    retainedFinalDirectClauseTerminalCoordinates_queryOfLiterals_eq_actual
      formula taggedClause.2 taggedClause.1
      (width taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
      (choices taggedClause taggedClauseMember)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
