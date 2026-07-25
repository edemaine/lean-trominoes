import LeanTrominoes.PeriodicCNFPlanarPeriodicCompleteness

/-!
# Soundness of periodic routed planarization

A satisfying periodicized planar assignment restricts to a satisfying finite
routed block at every translate.  For each original clause, a satisfied
routed literal propagates from its clause terminal through the complete route
and degree-three variable duplicator to a central periodic atom.  That atom
value is exactly the corresponding original literal value at the required
source cell.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Moving a subtracted lattice offset across an addition. -/
theorem Cell.sub_add_eq_add_sub
    (first second third : Cell) :
    Cell.add (Cell.sub first second) third =
      Cell.add first (Cell.sub third second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases third with ⟨thirdX, thirdY⟩
  simp [Cell.add, Cell.sub]
  constructor <;> omega

/-- An occurrence selected from one routed clause comes from a literal
tagged in the uniquely indexed original source clause. -/
theorem clauseRouteOccurrence_literal_data
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMem : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceAtMem :
      occurrence ∈ clauseRouteOccurrencesAt formula
        (taggedClause.2, translate)) :
    ∃ taggedLiteral ∈ taggedClause.1.zipIdx,
      occurrence.incidence.literal = taggedLiteral.1 ∧
        occurrence.incidence.clause = taggedClause.1 ∧
          occurrence.translate = translate := by
  rcases List.mem_map.mp occurrenceAtMem with
    ⟨taggedIncidence, taggedIncidenceFilterMem,
      occurrenceEq⟩
  rcases taggedIncidence with
    ⟨incidence, edgeIndex⟩
  subst occurrence
  have taggedIncidenceMem :=
    (List.mem_filter.mp taggedIncidenceFilterMem).1
  have clauseIndexEq :
      incidence.clauseIndex = taggedClause.2 :=
    of_decide_eq_true
      (List.mem_filter.mp taggedIncidenceFilterMem).2
  rcases List.mem_flatMap.mp
      (List.fst_mem_of_mem_zipIdx
        taggedIncidenceMem) with
    ⟨sourceTaggedClause, sourceTaggedClauseMem,
      incidenceMem⟩
  rcases List.mem_map.mp incidenceMem with
    ⟨taggedLiteral, taggedLiteralMem, incidenceEq⟩
  have sourceIndexEq :
      sourceTaggedClause.2 = taggedClause.2 := by
    rw [← clauseIndexEq]
    exact congrArg CNFIncidence.clauseIndex
      incidenceEq
  have sourceClauseEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      sourceTaggedClauseMem taggedClauseMem sourceIndexEq
  subst sourceTaggedClause
  have literalEq :=
    congrArg CNFIncidence.literal incidenceEq
  have incidenceClauseEq :=
    congrArg CNFIncidence.clause incidenceEq
  exact
    ⟨taggedLiteral, taggedLiteralMem,
      literalEq.symm, incidenceClauseEq.symm, rfl⟩

/-- Every occurrence selected from a neighboring routed clause belongs to
the complete neighboring route enumeration. -/
theorem clauseRouteOccurrence_mem_drawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceAtMem :
      occurrence ∈ clauseRouteOccurrencesAt formula site)
    (translateNeighbor : IsNeighborTranslation site.2) :
    occurrence ∈ drawingCNFRouteOccurrences formula := by
  rcases List.mem_map.mp occurrenceAtMem with
    ⟨taggedIncidence, taggedIncidenceFilterMem,
      occurrenceEq⟩
  subst occurrence
  exact CNFRouteOccurrence.mem_drawing_of_tagged
    formula taggedIncidence
    (List.mem_filter.mp taggedIncidenceFilterMem).1
    site.2 translateNeighbor

/-- Read central atom values from one assignment of the combined finite
planar SAT block. -/
def finitePlanarSATAtomAssignment
    {Variable : Type*}
    (assignment : PlanarSATVariable Variable → Bool) :
    Variable → Cell → Bool :=
  fun atom cell =>
    assignment (.inl (.atom (atom, cell)))

/-- Finite local soundness: a satisfying routed block for an
occurrence-three source satisfies each represented neighboring copy of its
original source clause. -/
theorem drawingPlanarSATFormula_source_clause_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment : PlanarSATVariable Variable → Bool)
    (holds :
      FormulaHolds assignment
        (drawingPlanarSATFormula formula))
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMem : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate) :
    taggedClause.1.Holds
      (finitePlanarSATAtomAssignment assignment)
      (Cell.sub translate
        (PeriodicCNF.clauseAnchor taggedClause.1)) := by
  have components :=
    (drawingPlanarSATFormula_holds_iff
      formula assignment).mp holds
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
      (assignment ∘ planarSATExternalVariableMap)).mp
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
    drawingPlanarSATFormula_source_eq_atom
      formula occurrences assignment holds
      occurrenceDrawingMem
  have atomValue :
      assignment
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
    assignment
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

/-- Recover the original source atom family from the atom proto-variables of
a periodicized planar assignment. -/
def sourceAssignmentOfPeriodicPlanarSAT
    {Variable : Type*}
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell => assignment (.atom atom) cell

/-- Periodic soundness under the degree-three occurrence premise. -/
theorem satisfies_of_drawingPeriodicPlanarSATFormula_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (planarHolds :
      (drawingPeriodicPlanarSATFormula formula).Satisfies
        assignment) :
    formula.Satisfies
      (sourceAssignmentOfPeriodicPlanarSAT assignment) := by
  have finiteHolds :=
    (drawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp planarHolds
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
    drawingPlanarSATFormula_source_clause_holds
      formula occurrences
      (planarSATFiniteAssignmentAt
        assignment blockTranslate)
      (finiteHolds blockTranslate)
      taggedClause taggedClauseMem
      (0, 0)
      ⟨by simp, by simp⟩
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

/-- For occurrence-three sources, satisfiability of the periodicized planar
formula implies source satisfiability. -/
theorem satisfiable_of_drawingPeriodicPlanarSATFormula_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (planarSatisfiable :
      (drawingPeriodicPlanarSATFormula formula).Satisfiable) :
    formula.Satisfiable := by
  rcases planarSatisfiable with
    ⟨assignment, planarHolds⟩
  exact
    ⟨sourceAssignmentOfPeriodicPlanarSAT assignment,
      satisfies_of_drawingPeriodicPlanarSATFormula_satisfies
        formula occurrences assignment planarHolds⟩

/-- Exact satisfiability preservation for occurrence-three periodic CNF
sources. -/
theorem drawingPeriodicPlanarSATFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3) :
    (drawingPeriodicPlanarSATFormula formula).Satisfiable ↔
      formula.Satisfiable :=
  ⟨satisfiable_of_drawingPeriodicPlanarSATFormula_satisfiable
      formula occurrences,
    drawingPeriodicPlanarSATFormula_satisfiable_of_satisfiable
      formula⟩

end PeriodicOrthocrossing
end LeanTrominoes
