import LeanTrominoes.PeriodicEightOccurrenceSplitPortAssignment
import LeanTrominoes.PeriodicThreeSATThreeAngularOrder

/-!
# Eight-direction terminal-ray ports

The planarization gadgets used in the paper draw every incidence at an
integer multiple of 45 degrees.  This file classifies exactly those eight
nonzero integer rays and turns the terminal vectors of an incidence-route
family into a total compass-port assignment.

The source-specific geometric layer need only provide a
`TerminalPortCertificate`: every genuine route has one of the eight
directions, and two occurrences of the same atom never use the same
direction.  The latter condition is converted here into the Boolean
reduction's collision-free certificate.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Classify a nonzero vector on one of the eight axis or 45-degree rays.
The coordinate convention has north at negative `y`, matching the established
Figure 7 drawing. -/
def terminalPort (vector : Cell) : Option Port :=
  if vector.1 < 0 then
    if vector.2 < 0 then
      if vector.1 = vector.2 then some .northwest else none
    else if vector.2 = 0 then
      some .west
    else if vector.2 = -vector.1 then
      some .southwest
    else
      none
  else if vector.1 = 0 then
    if vector.2 < 0 then
      some .north
    else if 0 < vector.2 then
      some .south
    else
      none
  else if vector.2 < 0 then
    if vector.1 = -vector.2 then
      some .northeast
    else
      none
  else if vector.2 = 0 then
    some .east
  else if vector.1 = vector.2 then
    some .southeast
  else
    none

/-- Compass port read from one clause-to-variable incidence route.  Invalid
or empty routes use a harmless northwest fallback; certificates below rule
that fallback out for genuine incidences. -/
def routeTerminalPort
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) : Port :=
  (terminalPort
    (routeTerminalVector
      (routes clauseIndex literalIndex))).getD .northwest

/-- Total occurrence-port assignment read directly from route terminal
vectors. -/
def terminalOccurrencePorts
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    OccurrencePorts where
  port := routeTerminalPort routes

/-- The terminal geometry required from a routed source before inserting
the fixed Figure 7 rings. -/
structure TerminalPortCertificate
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Prop where
  valid :
    ∀ tagged ∈ taggedLiterals source,
      (terminalPort
        (routeTerminalVector
          (routes tagged.2.1 tagged.2.2))).isSome
  separate :
    ∀ first ∈ taggedLiterals source,
      ∀ second ∈ taggedLiterals source,
        first.1.atom = second.1.atom →
        routeTerminalPort routes first.2.1 first.2.2 =
          routeTerminalPort routes second.2.1 second.2.2 →
        first = second

/-- A certified terminal route's total port lookup is the unique port
returned by the eight-direction classifier. -/
theorem routeTerminalPort_eq_of_terminalPort_eq_some
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (port : Port)
    (classified :
      terminalPort
          (routeTerminalVector
            (routes clauseIndex literalIndex)) =
        some port) :
    routeTerminalPort routes clauseIndex literalIndex =
      port := by
  simp [routeTerminalPort, classified]

/-- Terminal-port separation gives the exact no-collision premise used by
the occurrence count. -/
theorem terminalOccurrencePorts_collisionFree
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      TerminalPortCertificate source routes) :
    (terminalOccurrencePorts routes).CollisionFree
      source := by
  unfold OccurrencePorts.CollisionFree selectedCopies
  apply List.Nodup.map_on
    (l := taggedLiterals source) ?_
      (taggedLiterals_nodup source)
  intro first firstMember second secondMember copiesEqual
  apply certificate.separate
    first firstMember second secondMember
  · exact (copy_eq_iff.mp copiesEqual).1
  · exact (copy_eq_iff.mp copiesEqual).2

/-- Fixed-eight splitting driven directly by certified terminal rays
preserves satisfiability. -/
theorem terminalFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (formula source
      (terminalOccurrencePorts routes)).Satisfiable ↔
        source.Satisfiable :=
  satisfiable_iff source (terminalOccurrencePorts routes)

/-- Terminal-driven splitting preserves locality. -/
theorem terminalFormula_isLocal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceLocal : source.IsLocal) :
    (formula source
      (terminalOccurrencePorts routes)).IsLocal :=
  formula_isLocal (terminalOccurrencePorts routes) sourceLocal

/-- Terminal-driven splitting preserves width three. -/
theorem terminalFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceWidth : source.WidthAtMost 3) :
    (formula source
      (terminalOccurrencePorts routes)).WidthAtMost 3 :=
  formula_widthAtMostThree
    (terminalOccurrencePorts routes) sourceWidth

/-- Certified terminal rays give the three-occurrence output bound. -/
theorem terminalFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      TerminalPortCertificate source routes) :
    (formula source
      (terminalOccurrencePorts routes)).OccurrencesAtMost 3 :=
  formula_occurrencesAtMostThree source
    (terminalOccurrencePorts routes)
    (terminalOccurrencePorts_collisionFree
      source routes certificate)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
