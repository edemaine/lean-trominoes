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

/-- Assemble global route and atom values with one independently chosen
crossover-internal extension in every translated block. -/
noncomputable def periodicPlanarSATAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment) :
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
  | .crossoverInternal internal, cell =>
      translatedDrawingPlanarSATExtension
        formula assignment sourceHolds cell (.inr internal)

/-- At each translate, the finite assignment induced by the assembled
periodic assignment is exactly the chosen satisfying finite extension. -/
theorem planarSATFiniteAssignmentAt_periodicPlanarSATAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (sourceHolds : formula.Satisfies assignment)
    (translate : Cell) :
    planarSATFiniteAssignmentAt
        (periodicPlanarSATAssignment
          formula assignment sourceHolds)
        translate =
      translatedDrawingPlanarSATExtension
        formula assignment sourceHolds translate := by
  funext inputVariable
  cases inputVariable with
  | inr internal =>
      simp [planarSATFiniteAssignmentAt,
        normalizePlanarSATVariable,
        periodicPlanarSATAssignment, Cell.add]
  | inl node =>
      cases node with
      | atom site =>
          rcases site with ⟨atom, cell⟩
          rw [translatedDrawingPlanarSATExtension_external
            formula assignment sourceHolds translate
            (.atom (atom, cell))]
          rfl
      | carrier carrierNode =>
          cases carrierNode with
          | terminal terminal =>
              rw [translatedDrawingPlanarSATExtension_external
                formula assignment sourceHolds translate
                (.carrier (.terminal terminal))]
              change
                incidenceRouteAssignment formula assignment
                    (terminal.indexed.routeIndex,
                      Cell.add translate terminal.translate) =
                  incidenceRouteAssignment formula
                    (translatedSourceAssignment
                      assignment translate)
                    terminal.routeKey
              exact
                (incidenceRouteAssignment_translated
                  formula assignment translate
                  terminal.routeKey).symm
          | boundary boundary =>
              rw [translatedDrawingPlanarSATExtension_external
                formula assignment sourceHolds translate
                (.carrier (.boundary boundary))]
              change
                incidenceRouteAssignment formula assignment
                    (translateRouteOccurrenceKey
                      (Cell.add translate (0, 0))
                      (CarrierNode.boundary boundary).routeKey) =
                  incidenceRouteAssignment formula
                    (translatedSourceAssignment
                      assignment translate)
                    (CarrierNode.boundary boundary).routeKey
              rw [show Cell.add translate (0, 0) = translate by
                rcases translate with ⟨x, y⟩
                simp [Cell.add]]
              exact
                (incidenceRouteAssignment_translated
                  formula assignment translate
                  (CarrierNode.boundary boundary).routeKey).symm

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
  rw [planarSATFiniteAssignmentAt_periodicPlanarSATAssignment
    formula assignment sourceHolds translate]
  exact translatedDrawingPlanarSATExtension_holds
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
