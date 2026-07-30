import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# Canonically gauging retained periodic planar-SAT variables

The first retained periodicization keeps the literal occurrences at their
exact finite physical positions.  Some variable prototypes—most notably
terminals on routes that cross a period boundary—therefore have stored
positions in neighboring lattice cells.  This file applies the generic
per-variable gauge before clause-anchor normalization.  Physical literal
positions and finite routes remain unchanged, while every stored variable
position is reduced modulo the drawing period.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Canonical lattice-cell quotient of every wrapped routed-SAT variable
position. -/
def retainedDrawingWrappedPeriodicPlanarSATVariableGauge
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    WrappedPeriodicPlanarSATVariable Variable → Cell :=
  (wrappedDrawingPeriodicPlanarSATPlacement
    formula).canonicalPositionGauge

/-- Wrapped retained source after moving every variable prototype to its
canonical period cell. -/
def retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).variableGauge
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)

@[simp]
theorem retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase =
      wrapPeriodicPlanarSATFormula
        (retainedDrawingPeriodicPlanarSATFormula formula) := by
  rw [retainedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_rename,
    retainedDrawingPositionedPeriodicPlanarSATFormula_erase]
  rfl

/-- Variable placement paired with the canonical source gauge. -/
def retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (wrappedDrawingPeriodicPlanarSATPlacement formula).variableGauge
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)

@[simp]
theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).period =
      (wrappedDrawingPeriodicPlanarSATPlacement formula).period := rfl

/-- The canonically gauged wrapped source has exactly the same displayed
physical routes as the original finite retained block. -/
theorem
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula) := by
  exact
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch.variableGauge
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
        formula wellFormed degree isLocal)

/-- Put every canonically gauged retained clause in its incidence-anchor
gauge. -/
def
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).anchorNormalize
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)

/-- Canonically gauged retained periodic source with one positioned
representative per clause orbit. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).deduplicateByLiterals

/-- The final retained source is definitionally the deduplicated normalized
source.  This named equation avoids re-elaborating the large construction
when downstream proofs transport certificates across the definition. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula =
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).deduplicateByLiterals :=
  rfl

/-- Variable gauging, anchor normalization, wrapping, and clause
deduplication together preserve the retained periodic SAT semantics. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.Satisfiable ↔
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfiable := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.deduplicateByLiterals_satisfiable_iff,
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.anchorNormalize_satisfiable_iff,
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    PeriodicCNF.variableGauge_satisfiable_iff,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase,
    wrapPeriodicPlanarSATFormula_satisfiable_iff]

/-- Canonical retained route family after variable gauging, clause-anchor
normalization, and clause-orbit deduplication. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.deduplicatedIncidenceRoutes
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula))

/-- Complete periodic incidence drawing for the canonically gauged retained
source. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)

/-- The named final drawing is exactly the positioned incidence drawing
assembled from the final source, placement, and routes. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula =
      PositionedPeriodicCNF.incidenceDrawing
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula) :=
  rfl

/-- The canonically gauged and transported routes have the exact endpoints
of the final periodic incidence graph. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutesMatch
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.deduplicatedIncidenceDrawing_routesMatch
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula))
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_physicalRoutesMatch
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
          formula wellFormed degree isLocal))
      (drawingPeriodicPlanarSATPlacement_period_pos formula)

end LeanTrominoes.PeriodicOrthocrossing
