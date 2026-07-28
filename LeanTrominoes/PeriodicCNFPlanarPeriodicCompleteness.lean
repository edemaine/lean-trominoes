import LeanTrominoes.PeriodicCNFPlanarPeriodicization

/-!
# Completeness of periodic routed planarization

A satisfying source assignment supplies plane-wide values for every atom and
incidence route.  At each lattice translate, the finite completeness theorem
chooses values for the fresh crossover internals.  These choices assemble
into one assignment satisfying the genuine periodicized planar SAT formula.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Coordinatewise lattice addition is associative. -/
theorem Cell.add_assoc (first second third : Cell) :
    Cell.add first (Cell.add second third) =
      Cell.add (Cell.add first second) third := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases third with ⟨thirdX, thirdY⟩
  simp [Cell.add, Int.add_assoc]

/-- Shift a plane-wide source assignment by one lattice translation. -/
def translatedSourceAssignment
    {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) :
    Variable → Cell → Bool :=
  fun atom cell =>
    assignment atom (Cell.add translate cell)

/-- Source satisfaction is invariant under shifting its plane-wide
assignment. -/
theorem translatedSourceAssignment_satisfies
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    formula.Satisfies
      (translatedSourceAssignment assignment translate) := by
  intro clauseTranslate clause clauseMem
  rcases sourceHolds
      (Cell.add translate clauseTranslate)
      clause clauseMem with
    ⟨literal, literalMem, literalHolds⟩
  refine ⟨literal, literalMem, ?_⟩
  unfold PeriodicLiteral.Holds
    translatedSourceAssignment
  rw [Cell.add_assoc]
  exact literalHolds

/-- Shift the translation component of a route-occurrence key. -/
def translateRouteOccurrenceKey
    (translate : Cell) (key : RouteOccurrenceKey) :
    RouteOccurrenceKey :=
  (key.1, Cell.add translate key.2)

/-- Pulling route values from a shifted source assignment is the same as
shifting the route occurrence key in the original source assignment. -/
theorem incidenceRouteAssignment_translated
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (key : RouteOccurrenceKey) :
    incidenceRouteAssignment formula
        (translatedSourceAssignment assignment translate) key =
      incidenceRouteAssignment formula assignment
        (translateRouteOccurrenceKey translate key) := by
  unfold incidenceRouteAssignment
    translatedSourceAssignment translateRouteOccurrenceKey
  cases lookup :
      (PeriodicCNF.incidencesWithMetadata formula)[key.1]? with
  | none =>
      rfl
  | some incidence =>
      change
        assignment incidence.literal.atom
            (Cell.add translate
              (Cell.add key.2 incidence.edge.offset)) =
          assignment incidence.literal.atom
            (Cell.add (Cell.add translate key.2)
              incidence.edge.offset)
      rw [Cell.add_assoc]

/-- Translating a normalized crossover boundary by its extracted period
shift recovers the same route occurrence as the original halo boundary. -/
theorem translateRouteOccurrenceKey_periodNormalize_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (translate : Cell) (boundary : CrossingBoundary) :
    translateRouteOccurrenceKey
        (Cell.add translate
          (crossingPeriodShift graph boundary.crossing))
        (CarrierNode.boundary
          (boundary.periodNormalize graph)).routeKey =
      translateRouteOccurrenceKey translate
        (CarrierNode.boundary boundary).routeKey := by
  rcases boundary with ⟨crossing, side⟩
  cases side <;>
    apply Prod.ext <;>
    simp [translateRouteOccurrenceKey,
      CarrierNode.routeKey, CarrierNode.carrierKey,
      segmentCarrierRouteKey, CrossingBoundary.periodNormalize,
      CrossingBoundary.carrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey,
      CrossingRecord.periodNormalize, crossingPeriodShift,
      Cell.add, Cell.sub]

/-- At every translate, finite routed completeness provides a satisfying
assignment whose external values are the shifted source's route and atom
values. -/
theorem exists_translatedDrawingPlanarSATFormula_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    ∃ finiteAssignment : PlanarSATVariable Variable → Bool,
      FormulaHolds finiteAssignment
          (drawingPlanarSATFormula formula) ∧
        ∀ node,
          finiteAssignment (.inl node) =
            routedPlanarSATExternalAssignment
              (incidenceRouteAssignment formula
                (translatedSourceAssignment assignment translate))
              (incidenceAtomAssignment
                (translatedSourceAssignment assignment translate))
              node := by
  let shifted :=
    translatedSourceAssignment assignment translate
  exact exists_drawingPlanarSATFormula_holds
    formula
    (incidenceRouteAssignment formula shifted)
    (incidenceAtomAssignment shifted)
    (drawingRoutedClauseFormula_holds_incidenceAssignment
      formula shifted
      (translatedSourceAssignment_satisfies
        formula assignment sourceHolds translate))
    (drawingRoutedVariableFormula_holds_incidenceAssignment
      formula shifted)

/-- One chosen finite extension at each lattice translate. -/
noncomputable def translatedDrawingPlanarSATExtension
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    PlanarSATVariable Variable → Bool :=
  Classical.choose
    (exists_translatedDrawingPlanarSATFormula_holds
      formula assignment sourceHolds translate)

theorem translatedDrawingPlanarSATExtension_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    FormulaHolds
      (translatedDrawingPlanarSATExtension
        formula assignment sourceHolds translate)
      (drawingPlanarSATFormula formula) :=
  (Classical.choose_spec
    (exists_translatedDrawingPlanarSATFormula_holds
      formula assignment sourceHolds translate)).1

theorem translatedDrawingPlanarSATExtension_external
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell)
    (node : PlanarSATNode Variable) :
    translatedDrawingPlanarSATExtension
        formula assignment sourceHolds translate
        (.inl node) =
      routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula
          (translatedSourceAssignment assignment translate))
        (incidenceAtomAssignment
          (translatedSourceAssignment assignment translate))
        node :=
  (Classical.choose_spec
    (exists_translatedDrawingPlanarSATFormula_holds
      formula assignment sourceHolds translate)).2 node

/-- Assemble global route and atom values with the canonical local crossover
extension at every physical crossing.  Because the internal truth-table
choice depends only on the two crossing signals, halo copies identified by
periodic normalization receive identical values. -/
noncomputable def periodicPlanarSATAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (_sourceHolds : formula.Satisfies assignment) :
    PeriodicPlanarSATVariable Variable → Cell → Bool
  | .terminal indexed _endpoint, cell =>
      incidenceRouteAssignment formula assignment
        (indexed.routeIndex, cell)
  | .boundary boundary, cell =>
      incidenceRouteAssignment formula assignment
        (translateRouteOccurrenceKey cell
          (CarrierNode.boundary boundary).routeKey)
  | .atom atom, cell =>
      assignment atom cell
  | .crossoverInternal (crossing, internal), cell =>
      canonicalCrossoverAssignment
        (incidenceRouteAssignment formula assignment
          (translateRouteOccurrenceKey cell
            (CarrierNode.boundary
              ⟨crossing, .left⟩).routeKey))
        (incidenceRouteAssignment formula assignment
          (translateRouteOccurrenceKey cell
            (CarrierNode.boundary
              ⟨crossing, .top⟩).routeKey))
        internal.toVariable

/-- At each translate, the induced assignment agrees with the shifted source
assignment on every external carrier and atom node. -/
theorem planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_external
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) (node : PlanarSATNode Variable) :
    planarSATFiniteAssignmentAt
        formula
        (periodicPlanarSATAssignment
          formula assignment sourceHolds)
        translate (.inl node) =
      routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula
          (translatedSourceAssignment assignment translate))
        (incidenceAtomAssignment
          (translatedSourceAssignment assignment translate))
        node := by
  cases node with
  | atom site =>
      rcases site with ⟨atom, cell⟩
      rfl
  | carrier carrierNode =>
      cases carrierNode with
      | terminal terminal =>
          change
            incidenceRouteAssignment formula assignment
                (terminal.indexed.routeIndex,
                  Cell.add translate terminal.translate) =
              incidenceRouteAssignment formula
                (translatedSourceAssignment assignment translate)
                terminal.routeKey
          exact
            (incidenceRouteAssignment_translated
              formula assignment translate terminal.routeKey).symm
      | boundary boundary =>
          change
            incidenceRouteAssignment formula assignment
                (translateRouteOccurrenceKey
                  (Cell.add translate
                    (crossingPeriodShift
                      (PeriodicCNF.incidenceGraph formula)
                      boundary.crossing))
                  (CarrierNode.boundary
                    (boundary.periodNormalize
                      (PeriodicCNF.incidenceGraph formula))).routeKey) =
              incidenceRouteAssignment formula
                (translatedSourceAssignment assignment translate)
                (CarrierNode.boundary boundary).routeKey
          rw [translateRouteOccurrenceKey_periodNormalize_boundary]
          exact
            (incidenceRouteAssignment_translated
              formula assignment translate
              (CarrierNode.boundary boundary).routeKey).symm

/-- The induced finite assignment restricts on the route core to the
canonical complete-core assignment for the shifted route signals. -/
theorem planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_core
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    planarSATFiniteAssignmentAt formula
          (periodicPlanarSATAssignment
            formula assignment sourceHolds)
          translate ∘
        planarSATCoreVariableMap =
      canonicalRoutePlanarCoreAssignment
        (incidenceRouteAssignment formula
          (translatedSourceAssignment assignment translate)) := by
  funext input
  cases input with
  | inl carrier =>
      exact
        planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_external
          formula assignment sourceHolds translate (.carrier carrier)
  | inr internal =>
      rcases internal with ⟨crossing, internal⟩
      change
        canonicalCrossoverAssignment
            (incidenceRouteAssignment formula assignment
              (translateRouteOccurrenceKey
                (Cell.add translate
                  (crossingPeriodShift
                    (PeriodicCNF.incidenceGraph formula) crossing))
                (CarrierNode.boundary
                  ⟨crossing.periodNormalize
                    (PeriodicCNF.incidenceGraph formula),
                    .left⟩).routeKey))
            (incidenceRouteAssignment formula assignment
              (translateRouteOccurrenceKey
                (Cell.add translate
                  (crossingPeriodShift
                    (PeriodicCNF.incidenceGraph formula) crossing))
                (CarrierNode.boundary
                  ⟨crossing.periodNormalize
                    (PeriodicCNF.incidenceGraph formula),
                    .top⟩).routeKey))
            internal.toVariable =
          canonicalCrossoverAssignment
            (incidenceRouteAssignment formula
              (translatedSourceAssignment assignment translate)
              (CarrierNode.boundary
                ⟨crossing, .left⟩).routeKey)
            (incidenceRouteAssignment formula
              (translatedSourceAssignment assignment translate)
              (CarrierNode.boundary
                ⟨crossing, .top⟩).routeKey)
            internal.toVariable
      have leftKey :=
        translateRouteOccurrenceKey_periodNormalize_boundary
          (PeriodicCNF.incidenceGraph formula) translate
          (⟨crossing, .left⟩ : CrossingBoundary)
      have topKey :=
        translateRouteOccurrenceKey_periodNormalize_boundary
          (PeriodicCNF.incidenceGraph formula) translate
          (⟨crossing, .top⟩ : CrossingBoundary)
      simp only [CrossingBoundary.periodNormalize] at leftKey topKey
      rw [leftKey, topKey,
        incidenceRouteAssignment_translated,
        incidenceRouteAssignment_translated]

/-- Every finite translated block induced by the assembled periodic
assignment satisfies the routed planar SAT formula. -/
theorem planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_holds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    FormulaHolds
      (planarSATFiniteAssignmentAt formula
        (periodicPlanarSATAssignment
          formula assignment sourceHolds)
        translate)
      (drawingPlanarSATFormula formula) := by
  let shifted :=
    translatedSourceAssignment assignment translate
  apply
    (drawingPlanarSATFormula_holds_iff formula
      (planarSATFiniteAssignmentAt formula
        (periodicPlanarSATAssignment
          formula assignment sourceHolds)
        translate)).mpr
  have externalRestriction :
      planarSATFiniteAssignmentAt formula
            (periodicPlanarSATAssignment
              formula assignment sourceHolds)
            translate ∘
          planarSATExternalVariableMap =
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
    exact canonicalRoutePlanarCoreAssignment_holds
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

/-- Periodic completeness: every satisfying source assignment induces a
satisfying assignment of the genuine periodic routed planar SAT formula. -/
theorem drawingPeriodicPlanarSATFormula_satisfies_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment) :
    (drawingPeriodicPlanarSATFormula formula).Satisfies
      (periodicPlanarSATAssignment
        formula assignment sourceHolds) := by
  apply
    (drawingPeriodicPlanarSATFormula_satisfies_iff
      formula
      (periodicPlanarSATAssignment
        formula assignment sourceHolds)).mpr
  intro translate
  exact
    planarSATFiniteAssignmentAt_periodicPlanarSATAssignment_holds
      formula assignment sourceHolds translate

/-- Satisfiability is preserved by periodic routed planarization. -/
theorem drawingPeriodicPlanarSATFormula_satisfiable_of_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceSatisfiable : formula.Satisfiable) :
    (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  rcases sourceSatisfiable with
    ⟨assignment, sourceHolds⟩
  exact
    ⟨periodicPlanarSATAssignment
        formula assignment sourceHolds,
      drawingPeriodicPlanarSATFormula_satisfies_of_satisfies
        formula assignment sourceHolds⟩

end PeriodicOrthocrossing
end LeanTrominoes
