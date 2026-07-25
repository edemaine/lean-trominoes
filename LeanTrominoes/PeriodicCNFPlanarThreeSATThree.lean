import LeanTrominoes.PeriodicCNFPlanarPeriodicSoundness
import LeanTrominoes.PeriodicCNFPlanarWidth
import LeanTrominoes.PeriodicThreeSATThreeCorrectness
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-!
# Occurrence splitting after periodic planarization

The crossover and routing gadgets used to planarize a periodic 3SAT
presentation preserve clause width, but their internal variables need not
retain the source formula's three-occurrence bound.  As in the proof of
Theorem 3.5, we therefore apply the standard implication-cycle construction
*after* planarization.

This file records the logical part of that step.  The output has width at
most three and every protovariable occurs at most three times, while its
periodic satisfiability remains exactly that of the routed planar formula and
hence, under the usual source hypotheses, exactly that of the original
periodic CNF.  A separate geometry layer places the new implication cycles in
small neighborhoods of the old variable vertices.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- An opaque wrapper around an arbitrary periodic protovariable. -/
structure WrappedPeriodicVariable (Original : Type*) where
  original : Original
  deriving DecidableEq, Repr

/-- Specialize the opaque wrapper to routed periodic planar SAT variables.
Keeping this layer opaque prevents equality proofs for later clause-scoped
auxiliaries from repeatedly unfolding the complete routed-variable type. -/
abbrev WrappedPeriodicPlanarSATVariable (Variable : Type*) :=
  WrappedPeriodicVariable (PeriodicPlanarSATVariable Variable)

/-- Lift one routed periodic literal through the opaque variable wrapper. -/
def wrapPeriodicPlanarSATLiteral
    {Original : Type*}
    (literal : PeriodicLiteral Original) :
    PeriodicLiteral (WrappedPeriodicVariable Original) :=
  ⟨⟨literal.atom⟩, literal.offset, literal.value⟩

/-- Lift a routed periodic clause through the opaque variable wrapper. -/
def wrapPeriodicPlanarSATClause
    {Original : Type*}
    (clause : PeriodicClause Original) :
    PeriodicClause (WrappedPeriodicVariable Original) :=
  clause.map wrapPeriodicPlanarSATLiteral

/-- Lift an arbitrary periodic formula over routed planar variables through
the opaque wrapper. -/
def wrapPeriodicPlanarSATFormula
    {Original : Type*}
    (source : PeriodicCNF Original) :
    PeriodicCNF (WrappedPeriodicVariable Original) :=
  ⟨source.clauses.map
    wrapPeriodicPlanarSATClause⟩

/-- A definitionally simple copy of the routed periodic planar formula. -/
def wrappedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable) :=
  wrapPeriodicPlanarSATFormula
    (drawingPeriodicPlanarSATFormula formula)

/-- Pull a routed assignment through the opaque variable wrapper. -/
def wrapPeriodicPlanarSATAssignment
    {Original : Type*}
    (assignment : Original → Cell → Bool) :
    WrappedPeriodicVariable Original → Cell → Bool :=
  fun atom => assignment atom.original

/-- Read a wrapped assignment at the canonical wrapper of an original
routed variable. -/
def unwrapPeriodicPlanarSATAssignment
    {Original : Type*}
    (assignment :
      WrappedPeriodicVariable Original → Cell → Bool) :
    Original → Cell → Bool :=
  fun atom => assignment ⟨atom⟩

theorem wrapPeriodicPlanarSATClause_holds
    {Original : Type*}
    (assignment : Original → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Original) :
    clause.Holds assignment translate ↔
      (wrapPeriodicPlanarSATClause clause).Holds
        (wrapPeriodicPlanarSATAssignment assignment) translate := by
  constructor
  · rintro ⟨literal, literalMem, literalHolds⟩
    exact
      ⟨wrapPeriodicPlanarSATLiteral literal,
        List.mem_map.mpr ⟨literal, literalMem, rfl⟩,
        literalHolds⟩
  · rintro ⟨wrappedLiteral, wrappedLiteralMem, wrappedLiteralHolds⟩
    rcases List.mem_map.mp wrappedLiteralMem with
      ⟨literal, literalMem, wrappedLiteralEq⟩
    subst wrappedLiteral
    exact ⟨literal, literalMem, wrappedLiteralHolds⟩

theorem unwrap_wrapPeriodicPlanarSATClause_holds
    {Original : Type*}
    (assignment :
      WrappedPeriodicVariable Original → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Original) :
    (wrapPeriodicPlanarSATClause clause).Holds assignment translate ↔
      clause.Holds
        (unwrapPeriodicPlanarSATAssignment assignment) translate := by
  constructor
  · rintro ⟨wrappedLiteral, wrappedLiteralMem, wrappedLiteralHolds⟩
    rcases List.mem_map.mp wrappedLiteralMem with
      ⟨literal, literalMem, wrappedLiteralEq⟩
    subst wrappedLiteral
    exact ⟨literal, literalMem, wrappedLiteralHolds⟩
  · rintro ⟨literal, literalMem, literalHolds⟩
    exact
      ⟨wrapPeriodicPlanarSATLiteral literal,
        List.mem_map.mpr ⟨literal, literalMem, rfl⟩,
        literalHolds⟩

/-- The opaque wrapper changes no periodic satisfiability semantics. -/
theorem wrapPeriodicPlanarSATFormula_satisfiable_iff
    {Original : Type*}
    (source : PeriodicCNF Original) :
    (wrapPeriodicPlanarSATFormula source).Satisfiable ↔
      source.Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine ⟨unwrapPeriodicPlanarSATAssignment assignment, ?_⟩
    intro translate clause clauseMem
    apply
      (unwrap_wrapPeriodicPlanarSATClause_holds
        assignment translate clause).mp
    apply satisfies translate (wrapPeriodicPlanarSATClause clause)
    exact List.mem_map.mpr ⟨clause, clauseMem, rfl⟩
  · rintro ⟨assignment, satisfies⟩
    refine ⟨wrapPeriodicPlanarSATAssignment assignment, ?_⟩
    intro translate wrappedClause wrappedClauseMem
    rcases List.mem_map.mp wrappedClauseMem with
      ⟨clause, clauseMem, wrappedClauseEq⟩
    subst wrappedClause
    apply
      (wrapPeriodicPlanarSATClause_holds
        assignment translate clause).mp
    exact satisfies translate clause clauseMem

/-- Specialization of the wrapper equivalence to the routed drawing. -/
theorem wrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (wrappedDrawingPeriodicPlanarSATFormula formula).Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable :=
  wrapPeriodicPlanarSATFormula_satisfiable_iff
    (drawingPeriodicPlanarSATFormula formula)

/-- Wrapping variables preserves every clause-width bound. -/
theorem wrapPeriodicPlanarSATFormula_widthAtMost
    {Original : Type*}
    (source : PeriodicCNF Original)
    (width : Nat)
    (sourceWidth : source.WidthAtMost width) :
    (wrapPeriodicPlanarSATFormula source).WidthAtMost width := by
  intro wrappedClause wrappedClauseMem
  rcases List.mem_map.mp wrappedClauseMem with
    ⟨clause, clauseMem, wrappedClauseEq⟩
  subst wrappedClause
  simpa [PeriodicClause.WidthAtMost,
    wrapPeriodicPlanarSATClause] using
      sourceWidth clause clauseMem

@[simp]
theorem wrapPeriodicPlanarSATFormula_variableOccurrences
    {Original : Type*} (source : PeriodicCNF Original) :
    PeriodicCNF.variableOccurrences
        (wrapPeriodicPlanarSATFormula source) =
      (PeriodicCNF.variableOccurrences source).map
        WrappedPeriodicVariable.mk := by
  simp [PeriodicCNF.variableOccurrences,
    wrapPeriodicPlanarSATFormula,
    wrapPeriodicPlanarSATClause,
    wrapPeriodicPlanarSATLiteral,
    List.flatMap_map, List.map_map, Function.comp_def]
  rw [List.map_flatMap]
  simp [List.map_map, Function.comp_def]

/-- Wrapping variables preserves every finite-presentation occurrence
bound. -/
theorem wrapPeriodicPlanarSATFormula_occurrencesAtMost
    {Original : Type*} [DecidableEq Original]
    (source : PeriodicCNF Original)
    (bound : Nat)
    (sourceOccurrences : source.OccurrencesAtMost bound) :
    (wrapPeriodicPlanarSATFormula source).OccurrencesAtMost bound := by
  rintro ⟨atom⟩
  rw [wrapPeriodicPlanarSATFormula_variableOccurrences]
  rw [List.count_map_of_injective
    (PeriodicCNF.variableOccurrences source)
    WrappedPeriodicVariable.mk
    (fun first second equal =>
      congrArg WrappedPeriodicVariable.original equal)
    atom]
  exact sourceOccurrences atom

/-- Periodicization of the positioned routed formula retains its finite
width-three certificate. -/
theorem drawingPeriodicPlanarSATFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingPeriodicPlanarSATFormula formula).WidthAtMost 3 := by
  intro periodicClause periodicClauseMem
  simp only [drawingPeriodicPlanarSATFormula] at periodicClauseMem
  rcases List.mem_map.mp periodicClauseMem with
    ⟨embeddedClause, embeddedClauseMem, periodicClauseEq⟩
  subst periodicClause
  have embeddedWidth :=
    drawingPlanarSATFormula_widthAtMostThree
      formula sourceWidth embeddedClause embeddedClauseMem
  simpa [PeriodicClause.WidthAtMost,
    PlanarThreeSAT.EmbeddedClause.WidthAtMost,
    periodicizePlanarSATClause] using embeddedWidth

/-- Proto-variable type produced by occurrence splitting the wrapped routed
periodic planar SAT formula. -/
abbrev PeriodicPlanarThreeSATThreeVariable (Variable : Type*) :=
  ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable)

/-- The routed periodic planar SAT formula after replacing every literal
occurrence by its own copy and tying equal source protovariables together by
directed implication cycles. -/
def drawingPeriodicPlanarThreeSATThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  PeriodicThreeSATThree.formula
    (wrappedDrawingPeriodicPlanarSATFormula formula)

/-- The post-planarization occurrence split retains width three. -/
theorem drawingPeriodicPlanarThreeSATThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingPeriodicPlanarThreeSATThreeFormula formula).WidthAtMost 3 := by
  apply PeriodicThreeSATThree.formula_widthAtMostThree
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact drawingPeriodicPlanarSATFormula_widthAtMostThree
    formula sourceWidth

/-- Independently of the routed gadgets' internal degrees, the split output
has at most three occurrences of every protovariable. -/
theorem drawingPeriodicPlanarThreeSATThreeFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarThreeSATThreeFormula formula).OccurrencesAtMost 3 :=
  PeriodicThreeSATThree.formula_occurrencesAtMostThree
    (wrappedDrawingPeriodicPlanarSATFormula formula)

/-- Occurrence splitting preserves the satisfiability of the routed periodic
planar formula exactly. -/
theorem drawingPeriodicPlanarThreeSATThreeFormula_satisfiable_iff_planarSAT
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarThreeSATThreeFormula formula).Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  exact
    (PeriodicThreeSATThree.satisfiable_iff
      (wrappedDrawingPeriodicPlanarSATFormula formula)).symm.trans
        (wrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff formula)

/-- End-to-end semantic correctness of planarization followed by the
occurrence split. -/
theorem drawingPeriodicPlanarThreeSATThreeFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceOccurrences : formula.OccurrencesAtMost 3) :
    (drawingPeriodicPlanarThreeSATThreeFormula formula).Satisfiable ↔
      formula.Satisfiable := by
  rw [
    drawingPeriodicPlanarThreeSATThreeFormula_satisfiable_iff_planarSAT,
    drawingPeriodicPlanarSATFormula_satisfiable_iff
      formula sourceOccurrences]

end PeriodicOrthocrossing
end LeanTrominoes
