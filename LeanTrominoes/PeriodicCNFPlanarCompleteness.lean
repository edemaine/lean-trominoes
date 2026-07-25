import LeanTrominoes.PeriodicCNFPlanarAssignment

/-!
# Completeness of the routed planar SAT construction

A satisfying plane-wide assignment of the source periodic CNF determines the
value of every routed literal occurrence.  The source end of each route then
satisfies the corresponding routed clause, while the target end agrees with
the central atom as proved in `PeriodicCNFPlanarAssignment`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The external routed assignment gives a source terminal the value of its
source literal at the translated target cell of the incidence edge. -/
theorem routedPlanarSATExternalAssignment_source_eq_literal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment)
        (.carrier (.terminal (occurrence.sourceTerminal formula))) =
      assignment occurrence.incidence.literal.atom
        (Cell.add occurrence.translate occurrence.edge.offset) := by
  change
    incidenceRouteAssignment formula assignment occurrence.routeKey =
      assignment occurrence.incidence.literal.atom
        (Cell.add occurrence.translate occurrence.edge.offset)
  exact incidenceRouteAssignment_occurrence
    formula assignment occurrenceMem

/-- A satisfying source assignment satisfies every routed copy of every
source clause in the neighboring drawing block. -/
theorem drawingRoutedClauseFormula_holds_incidenceAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment) :
    FormulaHolds
      (routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment))
      (drawingRoutedClauseFormula formula) := by
  apply
    (drawingRoutedClauseFormula_holds_iff
      formula
      (routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment))).mpr
  intro site siteMem
  rcases List.mem_flatMap.mp siteMem with
    ⟨taggedClause, taggedClauseMem, siteMem⟩
  rcases List.mem_map.mp siteMem with
    ⟨translate, translateMem, siteEq⟩
  subst site
  let sourceTranslate :=
    Cell.sub translate
      (PeriodicCNF.clauseAnchor taggedClause.1)
  rcases
      sourceHolds sourceTranslate taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMem) with
    ⟨literal, literalMem, literalHolds⟩
  have mappedLiteralMem :
      literal ∈ taggedClause.1.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using literalMem
  rcases List.mem_map.mp mappedLiteralMem with
    ⟨taggedLiteral, taggedLiteralMem, taggedLiteralEq⟩
  rcases taggedLiteral with ⟨taggedLiteral, literalIndex⟩
  simp only at taggedLiteralEq
  subst taggedLiteral
  let incidence : CNFIncidence Variable :=
    ⟨taggedClause.2, taggedClause.1, literalIndex, literal⟩
  have incidenceMem :
      incidence ∈
        PeriodicCNF.incidencesWithMetadata formula := by
    apply List.mem_flatMap.mpr
    refine ⟨taggedClause, taggedClauseMem, ?_⟩
    exact List.mem_map.mpr
      ⟨(literal, literalIndex), taggedLiteralMem, rfl⟩
  have mappedIncidenceMem :
      incidence ∈
        (PeriodicCNF.incidencesWithMetadata formula).zipIdx.map
          Prod.fst := by
    simpa only [List.zipIdx_map_fst] using incidenceMem
  rcases List.mem_map.mp mappedIncidenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, taggedIncidenceEq⟩
  rcases taggedIncidence with ⟨taggedIncidence, edgeIndex⟩
  simp only at taggedIncidenceEq
  subst taggedIncidence
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨incidence, edgeIndex, translate⟩
  have occurrenceAtMem :
      occurrence ∈
        clauseRouteOccurrencesAt formula
          (taggedClause.2, translate) := by
    apply List.mem_map.mpr
    refine ⟨(incidence, edgeIndex), ?_, rfl⟩
    exact List.mem_filter.mpr
      ⟨taggedIncidenceMem, by simp [incidence]⟩
  have occurrenceDrawingMem :
      occurrence ∈ drawingCNFRouteOccurrences formula := by
    exact
      CNFRouteOccurrence.mem_drawing_of_tagged
        formula (incidence, edgeIndex) taggedIncidenceMem translate
          ((mem_neighborTranslations_iff translate).mp
            translateMem)
  refine
    ⟨(.carrier (.terminal (occurrence.sourceTerminal formula)),
        literal.value), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨occurrence, occurrenceAtMem, rfl⟩
  · rw [
      routedPlanarSATExternalAssignment_source_eq_literal
        formula assignment occurrenceDrawingMem]
    rw [show
      Cell.add occurrence.translate occurrence.edge.offset =
        Cell.add sourceTranslate literal.offset by
      rcases translate with ⟨translateX, translateY⟩
      rcases PeriodicCNF.clauseAnchor taggedClause.1 with
        ⟨anchorX, anchorY⟩
      apply Prod.ext <;>
        simp [occurrence, incidence, sourceTranslate,
          CNFRouteOccurrence.edge, CNFIncidence.edge,
          PeriodicCNF.incidenceEdge, Cell.add, Cell.sub]
        <;> omega]
    exact literalHolds

/-- Completeness of the finite routed planarization: a satisfying plane-wide
source assignment extends through every route, crossing, clause gadget, and
variable duplicator in the constructed drawing block. -/
theorem exists_drawingPlanarSATFormula_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment) :
    ∃ planarAssignment : PlanarSATVariable Variable → Bool,
      FormulaHolds planarAssignment
        (drawingPlanarSATFormula formula) := by
  rcases
      exists_drawingPlanarSATFormula_holds
        formula
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment)
        (drawingRoutedClauseFormula_holds_incidenceAssignment
          formula assignment sourceHolds)
        (drawingRoutedVariableFormula_holds_incidenceAssignment
          formula assignment) with
    ⟨planarAssignment, planarHolds, externalAgreement⟩
  exact ⟨planarAssignment, planarHolds⟩

end PeriodicOrthocrossing
end LeanTrominoes
