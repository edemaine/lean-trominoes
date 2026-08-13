/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitAngularFanBoundary
import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedOccurrenceIndex

/-!
# Routing copied incidences through angular fan boundaries

Occurrence splitting replaces the variable endpoint of every source
incidence by one selected vertex of a local Figure 7 fan.  The global
geometric construction only has to route the copied clause to the
corresponding fan boundary.  The certified local spoke can then finish the
route.

This file states that deliberately narrow upstream interface and verifies
the local splice.  In particular, the splice uses the literal offset
relative to its clause anchor, so incidences into neighboring periodic
copies reach the correct translated fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The source occurrence named by a clause/literal presentation index. -/
def indexedOccurrence
    {Variable : Type*}
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    ThreeOccurrenceVariable Variable :=
  (literal.atom, clauseIndex, literalIndex)

/-- Position of a genuine source occurrence in the chosen angular order. -/
def angularOccurrenceIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (order : OccurrenceOrder source.erase)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) : Nat :=
  (order.copies literal.atom).idxOf
    (indexedOccurrence literal clauseIndex literalIndex)

/-- Logical translate of a literal endpoint relative to its clause orbit's
canonical anchor. -/
def incidenceRelativeOffset
    {Variable : Type*}
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) : Cell :=
  Cell.sub literal.offset
    (PeriodicCNF.clauseAnchor clause.literals)

/-- Copying a clause changes atoms but preserves the first literal offset
used as its periodic anchor. -/
@[simp]
theorem occurrenceClause_clauseAnchor
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    PeriodicCNF.clauseAnchor
        (PeriodicEightOccurrenceSplit.occurrenceClause
          occurrencePorts clauseIndex clause) =
      PeriodicCNF.clauseAnchor clause := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rfl

/-- Positioned clause membership induces membership of its erased literal
list at the same presentation index. -/
theorem erasedClause_mem_of_positioned_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    (clause.literals, clauseIndex) ∈
      source.erase.clauses.zipIdx := by
  change
    (clause.literals, clauseIndex) ∈
      (source.clauses.map
        PositionedPeriodicClause.literals).zipIdx
  rw [List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨(clause, clauseIndex), clauseMember, rfl⟩

/-- A genuine positioned incidence is one of the tagged incidences used by
the occurrence-order lookup. -/
theorem taggedLiteral_mem_of_positioned_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (literal, clauseIndex, literalIndex) ∈
      taggedLiterals source.erase :=
  taggedLiterals_mem source.erase
    (erasedClause_mem_of_positioned_mem
      source clauseMember)
    literalMember

/-- The total east-first port lookup selects exactly the port at the source
occurrence's angular-list index. -/
theorem occurrencePortsOfAngularOrder_eq_angularPort
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (order : OccurrenceOrder source.erase)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (occurrencePortsOfAngularOrder
        source.erase order).port clauseIndex literalIndex =
      angularPortOfIndex
        (angularOccurrenceIndex order literal
          clauseIndex literalIndex) := by
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      source clauseMember literalMember
  simpa [angularOccurrenceIndex, indexedOccurrence,
    angularOrderedOccurrencePort] using
      occurrencePortsOfAngularOrder_eq
        source.erase order
        (literal, clauseIndex, literalIndex)
        taggedMember

/-- The certified suffix for one genuine source incidence, lifted to the
literal's anchor-relative periodic occurrence. -/
def angularOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  angularFanSpokeRouteAt sourcePlacement
    literal.atom
    (incidenceRelativeOffset clause literal)
    (angularOccurrenceIndex order literal
      clauseIndex literalIndex)

/-- The suffix starts at the translated angular fan boundary advertised to
the global router. -/
@[simp]
theorem angularOccurrenceSuffix_head?
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    (angularOccurrenceSuffix sourcePlacement order
      clause literal clauseIndex literalIndex).head? =
      some
        (angularFanBoundaryPositionAt sourcePlacement
          literal.atom
          (incidenceRelativeOffset clause literal)
          (angularOccurrenceIndex order literal
            clauseIndex literalIndex)) := by
  simp [angularOccurrenceSuffix]

/-- The suffix ends at the canonical endpoint of the copied literal chosen
by the angular port assignment. -/
theorem angularOccurrenceSuffix_getLast?
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (angularOccurrenceSuffix sourcePlacement order
      clause literal clauseIndex literalIndex).getLast? =
      some
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (placement sourcePlacement)
          (occurrenceClause
            (occurrencePortsOfAngularOrder
              source.erase order)
            clauseIndex clause)
          (PeriodicEightOccurrenceSplit.occurrenceLiteral
            (occurrencePortsOfAngularOrder
              source.erase order)
            clauseIndex literalIndex literal)) := by
  rw [angularOccurrenceSuffix,
    angularFanSpokeRouteAt_getLast?]
  apply congrArg some
  unfold PositionedPeriodicCNF.canonicalLiteralPosition
    occurrenceClause
    PeriodicEightOccurrenceSplit.occurrenceLiteral
  rw [occurrencePortsOfAngularOrder_eq_angularPort
    source order clauseMember literalMember]
  simp [incidenceRelativeOffset, placement,
    occurrenceVariablePosition_copy]

/-- Every genuine angular fan suffix is an orthogonal polyline. -/
theorem angularOccurrenceSuffix_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (angularOccurrenceSuffix sourcePlacement order
        clause literal clauseIndex literalIndex) := by
  exact angularFanSpokeRouteAt_orthogonal
    sourcePlacement literal.atom
    (incidenceRelativeOffset clause literal)
    (angularOccurrenceIndex order literal
      clauseIndex literalIndex)

/-- Minimal global obligation left by the certified local angular fans:
route each copied source clause incidence to its translated fan boundary. -/
structure AngularBoundaryRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) where
  routes : PositionedPeriodicCNF.IncidenceRoutes
  endpoints :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        (routes clauseIndex literalIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                (placement sourcePlacement)
                (occurrenceClause
                  (occurrencePortsOfAngularOrder
                    source.erase order)
                  clauseIndex clause)) ∧
          (routes clauseIndex literalIndex).getLast? =
            some
              (angularFanBoundaryPositionAt
                sourcePlacement literal.atom
                (incidenceRelativeOffset clause literal)
                (angularOccurrenceIndex order literal
                  clauseIndex literalIndex))
  orthogonal :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        PeriodicOrthocrossing.OrthogonalPolyline
          (routes clauseIndex literalIndex)

/-- Join an upstream boundary route to the certified local fan suffix. -/
def angularSplicedOccurrenceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {order : OccurrenceOrder source.erase}
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  joinAtEndpoint
    (boundary.routes clauseIndex literalIndex)
    (angularOccurrenceSuffix sourcePlacement order
      clause literal clauseIndex literalIndex)

/-- A genuine spliced copied-source incidence has both canonical outer
endpoints and remains orthogonal. -/
theorem angularSplicedOccurrenceRoute_valid
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {order : OccurrenceOrder source.erase}
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (angularSplicedOccurrenceRoute boundary
        clause literal clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement)
            (occurrenceClause
              (occurrencePortsOfAngularOrder
                source.erase order)
              clauseIndex clause)) ∧
      (angularSplicedOccurrenceRoute boundary
        clause literal clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement sourcePlacement)
            (occurrenceClause
              (occurrencePortsOfAngularOrder
                source.erase order)
              clauseIndex clause)
            (PeriodicEightOccurrenceSplit.occurrenceLiteral
              (occurrencePortsOfAngularOrder
                source.erase order)
              clauseIndex literalIndex literal)) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (angularSplicedOccurrenceRoute boundary
          clause literal clauseIndex literalIndex) := by
  have boundaryFacts :=
    boundary.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  have suffixHead :=
    angularOccurrenceSuffix_head?
      sourcePlacement order clause literal
      clauseIndex literalIndex
  have suffixLast :=
    angularOccurrenceSuffix_getLast?
      source sourcePlacement order clauseMember literalMember
  constructor
  · exact joinAtEndpoint_head? boundaryFacts.1
  constructor
  · exact joinAtEndpoint_getLast?
      boundaryFacts.2 suffixHead suffixLast
  · exact
      boundary.orthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember
        |>.joinAtEndpoint
          (angularOccurrenceSuffix_orthogonal
            sourcePlacement order clause literal
            clauseIndex literalIndex)
          boundaryFacts.2 suffixHead

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
