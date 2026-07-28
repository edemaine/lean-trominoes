import LeanTrominoes.PeriodicCNFPlanarVariableSoundness

/-!
# Periodicizing the routed planar SAT block

The finite routed construction explicitly names neighboring route
translations.  To obtain a genuine periodic CNF presentation, terminal and
atom translations are erased from the proto-variable name and retained as
literal offsets.  Crossing-halo boundaries and internals are reduced to
their canonical crossing record, retaining the common period shift as their
literal offset.

The semantic bridge proved below is exact: the resulting periodic CNF holds
under a plane-wide assignment precisely when the original finite routed block
holds at every lattice translate under the induced finite assignment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Proto-variables of the periodic routed planar SAT formula. -/
inductive PeriodicPlanarSATVariable (Variable : Type*)
  | terminal (indexed : IndexedGridSegment) (endpoint : SegmentEnd)
  | boundary (boundary : CrossingBoundary)
  | atom (atom : Variable)
  | crossoverInternal
      (internal : CrossingRecord × CrossoverInternal)
  deriving DecidableEq, Repr

/-- Erase explicit neighboring translations from a finite planar SAT
variable, returning its periodic proto-variable and lattice offset. -/
def normalizePlanarSATVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable : PlanarSATVariable Variable) :
    PeriodicPlanarSATVariable Variable × Cell :=
  let graph := PeriodicCNF.incidenceGraph formula
  match inputVariable with
  | .inl (.carrier (.terminal terminal)) =>
      (.terminal terminal.indexed terminal.endpoint,
        terminal.translate)
  | .inl (.carrier (.boundary boundary)) =>
      (.boundary (boundary.periodNormalize graph),
        crossingPeriodShift graph boundary.crossing)
  | .inl (.atom (atom, cell)) =>
      (.atom atom, cell)
  | .inr (crossing, internal) =>
      (.crossoverInternal
          (crossing.periodNormalize graph, internal),
        crossingPeriodShift graph crossing)

/-- Convert one finite routed literal into a periodic literal. -/
def periodicizePlanarSATLiteral
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PlanarSATVariable Variable × Bool) :
    PeriodicLiteral (PeriodicPlanarSATVariable Variable) :=
  let normalized := normalizePlanarSATVariable formula literal.1
  ⟨normalized.1, normalized.2, literal.2⟩

/-- Convert one finite embedded clause into a periodic clause.  Its geometric
drawing position is irrelevant to Boolean semantics; variable offsets carry
the necessary periodic identifications. -/
def periodicizePlanarSATClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable)) :
    PeriodicClause (PeriodicPlanarSATVariable Variable) :=
  clause.literals.map (periodicizePlanarSATLiteral formula)

/-- The periodic CNF obtained from the complete finite routed planar SAT
block. -/
def drawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨(drawingPlanarSATFormula formula).map
    (periodicizePlanarSATClause formula)⟩

/-- Restrict a plane-wide periodicized assignment to the explicit variables
of the finite routed block at one lattice translate. -/
def planarSATFiniteAssignmentAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (translate : Cell) :
    PlanarSATVariable Variable → Bool :=
  fun inputVariable =>
    let normalized :=
      normalizePlanarSATVariable formula inputVariable
    assignment normalized.1
      (Cell.add translate normalized.2)

/-- Periodicizing one clause preserves its satisfaction exactly under the
induced finite assignment at every translate. -/
theorem periodicizePlanarSATClause_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (translate : Cell)
    (clause : EmbeddedClause (PlanarSATVariable Variable)) :
    PeriodicClause.Holds assignment translate
        (periodicizePlanarSATClause formula clause) ↔
      ClauseHolds
        (planarSATFiniteAssignmentAt formula assignment translate)
        clause := by
  constructor
  · rintro ⟨periodicLiteral, periodicLiteralMem,
      periodicLiteralHolds⟩
    rcases List.mem_map.mp periodicLiteralMem with
      ⟨literal, literalMem, periodicLiteralEq⟩
    subst periodicLiteral
    exact ⟨literal, literalMem, periodicLiteralHolds⟩
  · rintro ⟨literal, literalMem, literalHolds⟩
    exact
      ⟨periodicizePlanarSATLiteral formula literal,
        List.mem_map.mpr ⟨literal, literalMem, rfl⟩,
        literalHolds⟩

/-- Periodicizing any finite embedded formula makes periodic satisfaction
equivalent to satisfaction of that finite formula at every translate. -/
theorem periodicizePlanarSATFormula_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula :
      List (EmbeddedClause (PlanarSATVariable Variable)))
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool) :
    (PeriodicCNF.mk
      (finiteFormula.map
        (periodicizePlanarSATClause formula))).Satisfies
        assignment ↔
      ∀ translate,
        FormulaHolds
          (planarSATFiniteAssignmentAt formula assignment translate)
          finiteFormula := by
  constructor
  · intro satisfies translate clause clauseMem
    apply
      (periodicizePlanarSATClause_holds_iff
        formula assignment translate clause).mp
    exact satisfies translate
      (periodicizePlanarSATClause formula clause)
      (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
  · intro finiteHolds translate periodicClause
      periodicClauseMem
    rcases List.mem_map.mp periodicClauseMem with
      ⟨clause, clauseMem, periodicClauseEq⟩
    subst periodicClause
    apply
      (periodicizePlanarSATClause_holds_iff
        formula assignment translate clause).mpr
    exact finiteHolds translate clause clauseMem

/-- Exact semantic interface for the genuine periodic routed planar SAT
formula. -/
theorem drawingPeriodicPlanarSATFormula_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool) :
    (drawingPeriodicPlanarSATFormula formula).Satisfies assignment ↔
      ∀ translate,
        FormulaHolds
          (planarSATFiniteAssignmentAt formula assignment translate)
          (drawingPlanarSATFormula formula) := by
  exact periodicizePlanarSATFormula_satisfies_iff
    formula (drawingPlanarSATFormula formula) assignment

end PeriodicOrthocrossing
end LeanTrominoes
