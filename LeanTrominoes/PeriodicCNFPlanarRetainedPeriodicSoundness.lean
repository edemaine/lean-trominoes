import LeanTrominoes.PeriodicCNFPlanarRetainedVariableSoundness
import LeanTrominoes.PeriodicCNFPlanarPeriodicSoundness

/-!
# Boolean correctness of retained periodic planarization

The retained carrier formula differs from the original planarization only in
which periodic representatives encode straight-wire equality.  Complete
retained-route soundness now allows the original clause reconstruction
argument to go through unchanged.  Conversely, the canonical periodic
assignment used for ordinary planarization also satisfies the retained route
core.  Thus retained planarization preserves satisfiability exactly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- Local retained soundness: a satisfying periodic planar assignment makes
each represented neighboring source clause true under its induced finite
atom assignment. -/
theorem retainedDrawingPeriodicPlanarSATFormula_source_clause_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (blockTranslate : Cell)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMem :
      taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate) :
    taggedClause.1.Holds
      (finitePlanarSATAtomAssignment
        (planarSATFiniteAssignmentAt
          formula assignment blockTranslate))
      (Cell.sub translate
        (PeriodicCNF.clauseAnchor taggedClause.1)) := by
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula assignment blockTranslate
  have finiteHolds :
      FormulaHolds finiteAssignment
        (retainedDrawingPlanarSATFormula formula) :=
    (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp satisfies blockTranslate
  have components :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mp finiteHolds
  have siteMem :
      (taggedClause.2, translate) ∈
        drawingClauseRouteSites formula := by
    apply List.mem_flatMap.mpr
    refine ⟨taggedClause, taggedClauseMem, ?_⟩
    exact List.mem_map.mpr
      ⟨translate,
        (mem_neighborTranslations_iff translate).mpr
          translateNeighbor,
        rfl⟩
  have routedClauseHolds :=
    (drawingRoutedClauseFormula_holds_iff
      formula
      (finiteAssignment ∘ planarSATExternalVariableMap)).mp
        components.2.1
        (taggedClause.2, translate) siteMem
  rcases routedClauseHolds with
    ⟨routedLiteral, routedLiteralMem, routedLiteralHolds⟩
  rcases List.mem_map.mp routedLiteralMem with
    ⟨occurrence, occurrenceAtMem, routedLiteralEq⟩
  subst routedLiteral
  have occurrenceDrawingMem :
      occurrence ∈ drawingCNFRouteOccurrences formula :=
    clauseRouteOccurrence_mem_drawing formula
      (taggedClause.2, translate)
      occurrenceAtMem translateNeighbor
  have sourceEqAtom :=
    retainedDrawingPeriodicPlanarSATFormula_source_eq_atom
      formula wellFormed degree isLocal occurrences
      assignment satisfies blockTranslate occurrenceDrawingMem
  have atomValue :
      finiteAssignment
          (.inl (.atom occurrence.variableOccurrence)) =
        occurrence.incidence.literal.value :=
    sourceEqAtom.symm.trans routedLiteralHolds
  rcases clauseRouteOccurrence_literal_data
      formula taggedClause taggedClauseMem translate
      occurrenceAtMem with
    ⟨taggedLiteral, taggedLiteralMem, literalEq,
      incidenceClauseEq, occurrenceTranslateEq⟩
  refine
    ⟨taggedLiteral.1,
      List.fst_mem_of_mem_zipIdx taggedLiteralMem, ?_⟩
  rw [← literalEq]
  change
    finiteAssignment
        (.inl (.atom
          (occurrence.incidence.literal.atom,
            Cell.add
              (Cell.sub translate
                (PeriodicCNF.clauseAnchor taggedClause.1))
              occurrence.incidence.literal.offset))) =
      occurrence.incidence.literal.value
  rw [show
    Cell.add
        (Cell.sub translate
          (PeriodicCNF.clauseAnchor taggedClause.1))
        occurrence.incidence.literal.offset =
      occurrence.variableOccurrence.2 by
    simpa [CNFRouteOccurrence.variableOccurrence,
      CNFRouteOccurrence.edge, CNFIncidence.edge,
      PeriodicCNF.incidenceEdge, incidenceClauseEq,
      occurrenceTranslateEq] using
        Cell.sub_add_eq_add_sub translate
          (PeriodicCNF.clauseAnchor taggedClause.1)
          occurrence.incidence.literal.offset]
  exact atomValue

/-- Periodic retained soundness under the geometric and occurrence-three
premises needed by route propagation and the variable duplicators. -/
theorem satisfies_of_retainedDrawingPeriodicPlanarSATFormula_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (planarHolds :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment) :
    formula.Satisfies
      (sourceAssignmentOfPeriodicPlanarSAT assignment) := by
  intro sourceTranslate clause clauseMem
  have mappedClauseMem :
      clause ∈ formula.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMem
  rcases List.mem_map.mp mappedClauseMem with
    ⟨taggedClause, taggedClauseMem, clauseEq⟩
  subst clause
  let anchor :=
    PeriodicCNF.clauseAnchor taggedClause.1
  let blockTranslate :=
    Cell.add sourceTranslate anchor
  have localHolds :=
    retainedDrawingPeriodicPlanarSATFormula_source_clause_holds
      formula wellFormed degree isLocal occurrences
      assignment planarHolds blockTranslate
      taggedClause taggedClauseMem
      (0, 0) ⟨by simp, by simp⟩
  rcases localHolds with
    ⟨literal, literalMem, literalHolds⟩
  refine ⟨literal, literalMem, ?_⟩
  unfold PeriodicLiteral.Holds
    sourceAssignmentOfPeriodicPlanarSAT
  change
    assignment (.atom literal.atom)
        (Cell.add blockTranslate
          (Cell.add
            (Cell.sub (0, 0) anchor)
            literal.offset)) =
      literal.value at literalHolds
  rw [show
    Cell.add blockTranslate
        (Cell.add (Cell.sub (0, 0) anchor)
          literal.offset) =
      Cell.add sourceTranslate literal.offset by
    rcases sourceTranslate with ⟨sourceX, sourceY⟩
    rcases anchor with ⟨anchorX, anchorY⟩
    rcases literal.offset with ⟨literalX, literalY⟩
    simp [blockTranslate, Cell.add, Cell.sub]] at literalHolds
  exact literalHolds

/-- Every satisfying source assignment induces a satisfying assignment of
the retained periodic planar formula. -/
theorem retainedDrawingPeriodicPlanarSATFormula_satisfies_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment) :
    (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
      (periodicPlanarSATAssignment
        formula assignment sourceHolds) := by
  apply
    (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
      formula
      (periodicPlanarSATAssignment
        formula assignment sourceHolds)).mpr
  intro translate
  let shifted :=
    translatedSourceAssignment assignment translate
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula
      (periodicPlanarSATAssignment
        formula assignment sourceHolds)
      translate
  apply
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mpr
  have externalRestriction :
      finiteAssignment ∘ planarSATExternalVariableMap =
        routedPlanarSATExternalAssignment
          (incidenceRouteAssignment formula shifted)
          (incidenceAtomAssignment shifted) := by
    funext node
    exact
      planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_external
        formula assignment sourceHolds translate node
  refine ⟨?_, ?_, ?_⟩
  · rw [
      planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_core
        formula assignment sourceHolds translate]
    exact
      canonicalRoutePlanarCoreAssignment_retained_holds
        (PeriodicCNF.incidenceGraph formula)
        (incidenceRouteAssignment formula shifted)
  · rw [externalRestriction]
    exact drawingRoutedClauseFormula_holds_incidenceAssignment
      formula shifted
      (translatedSourceAssignment_satisfies
        formula assignment sourceHolds translate)
  · rw [externalRestriction]
    exact drawingRoutedVariableFormula_holds_incidenceAssignment
      formula shifted

/-- Exact satisfiability preservation for the retained periodic
planarization under its geometric and occurrence-three premises. -/
theorem retainedDrawingPeriodicPlanarSATFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (retainedDrawingPeriodicPlanarSATFormula formula).Satisfiable ↔
      formula.Satisfiable := by
  constructor
  · rintro ⟨assignment, planarHolds⟩
    exact
      ⟨sourceAssignmentOfPeriodicPlanarSAT assignment,
        satisfies_of_retainedDrawingPeriodicPlanarSATFormula_satisfies
          formula wellFormed degree isLocal occurrences
          assignment planarHolds⟩
  · rintro ⟨assignment, sourceHolds⟩
    exact
      ⟨periodicPlanarSATAssignment
          formula assignment sourceHolds,
        retainedDrawingPeriodicPlanarSATFormula_satisfies_of_satisfies
          formula assignment sourceHolds⟩

end PeriodicOrthocrossing
end LeanTrominoes
