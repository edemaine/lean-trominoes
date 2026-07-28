import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity
import LeanTrominoes.PeriodicCNFPlanarSATIncidenceRoutes

/-!
# Periodicizing the retained planar SAT drawing

The globally planar retained drawing is still an explicitly translated
finite block.  This file transports it through the same four bookkeeping
steps used by the routed SAT pipeline:

1. normalize translated finite variables into periodic protovariables and
   literal offsets;
2. wrap those protovariables in the opaque pipeline type;
3. subtract each clause's periodic anchor from its displayed position and
   routes; and
4. retain one positioned representative of every periodic clause orbit.

The final theorem proves exact graph-level incidence endpoints for the
resulting periodic drawing.  Periodic planarity is a separate geometric
quotient theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Periodic CNF obtained by normalizing the variables of every retained
finite embedded clause. -/
def retainedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨(retainedDrawingPlanarSATFormula formula).map
    (periodicizePlanarSATClause formula)⟩

/-- Periodic satisfaction of the retained formula is exactly satisfaction
of its explicit finite block at every lattice translate. -/
theorem retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool) :
    (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment ↔
      ∀ translate,
        FormulaHolds
          (planarSATFiniteAssignmentAt formula assignment translate)
          (retainedDrawingPlanarSATFormula formula) := by
  exact periodicizePlanarSATFormula_satisfies_iff
    formula (retainedDrawingPlanarSATFormula formula) assignment

/-- Retain the finite drawing positions while periodicizing the retained
literal variables. -/
def retainedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarSATVariable Variable) :=
  positionPeriodicizedPlanarSATFormula
    formula (retainedDrawingPlanarSATFormula formula)

@[simp]
theorem retainedDrawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPositionedPeriodicPlanarSATFormula formula).erase =
      retainedDrawingPeriodicPlanarSATFormula formula := by
  exact positionPeriodicizedPlanarSATFormula_erase
    formula (retainedDrawingPlanarSATFormula formula)

/-- Put the retained positioned source behind the same opaque variable
wrapper used by the downstream routed-SAT pipeline. -/
def retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedDrawingPositionedPeriodicPlanarSATFormula formula).rename
    WrappedPeriodicVariable.mk

/-- Normalize every retained clause to the incidence graph's periodic
anchor gauge. -/
def retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).anchorNormalize
      (wrappedDrawingPeriodicPlanarSATPlacement formula)

/-- The retained periodic source with one positioned representative per
periodic clause orbit. -/
def retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
    formula).deduplicateByLiterals

/-- The retained finite routes match the physical endpoints after literal
periodicization. -/
theorem
    retainedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (retainedDrawingPositionedPeriodicPlanarSATFormula formula)
      (drawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula) := by
  exact
    positionPeriodicizedPlanarSATFormula_physicalRoutesMatch
      formula
      (retainedDrawingPlanarSATFormula formula)
      (drawingPlanarSATVariablePosition formula)
      (drawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes_physicalRoutesMatch
        formula wellFormed degree isLocal)
      (periodicizePlanarSATLiteral_position formula)

/-- Opaque wrapping changes neither the retained finite route endpoints nor
their physical period. -/
theorem
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula) := by
  apply
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch.rename
      (retainedDrawingPositionedPeriodicPlanarSATFormula formula)
      (drawingPeriodicPlanarSATPlacement formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
      WrappedPeriodicVariable.mk
      (retainedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
        formula wellFormed degree isLocal)
  · intro atom
    rfl
  · rfl

/-- Canonical retained route family after clause-anchor normalization and
clause-orbit deduplication. -/
def retainedDeduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.deduplicatedIncidenceRoutes
    (retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula))

/-- Complete periodic incidence drawing determined by the retained route
representatives. -/
def retainedDeduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDeduplicatedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)

/-- The transported retained route family has the exact endpoints of every
edge in the deduplicated periodic incidence graph. -/
theorem
    retainedDeduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDeduplicatedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutesMatch
        (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.deduplicatedIncidenceDrawing_routesMatch
      (retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula))
      (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_physicalRoutesMatch
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
          formula wellFormed degree isLocal))
      (drawingPeriodicPlanarSATPlacement_period_pos formula)

end PeriodicOrthocrossing
end LeanTrominoes
