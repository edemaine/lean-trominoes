/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceSplice
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes

/-!
# Retained source routes to refined angular fan boundaries

This file lifts the single-route retained fan splice to a total incidence
route family.  Invalid presentation indices receive the harmless empty
route.  Every genuine clause/literal index selects its classified terminal
datum and its bounded angular slot, producing an orthogonal route from the
source clause at scale 288 to the matching factor-eight Figure 7 boundary.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplitPositioned
open OccurrenceSplitRing

/-- Total conversion from an arbitrary natural index to one of the eight
router slots.  Genuine angular occurrence indices are below eight and
therefore remain unchanged. -/
def boundedRetainedTerminalSlot
    (index : Nat) : RetainedTerminalSlot :=
  ⟨min index 7, by omega⟩

@[simp]
theorem boundedRetainedTerminalSlot_val_of_lt
    {index : Nat} (indexLt : index < 8) :
    (boundedRetainedTerminalSlot index).val = index := by
  simp [boundedRetainedTerminalSlot]
  omega

/-- At a genuine occurrence, the total bounded slot is exactly the slot
selected by profile lookup. -/
theorem boundedRetainedTerminalSlot_eq_retainedAngularTerminalSlot
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (copyMember :
      (literal.atom, clauseIndex, literalIndex) ∈
        occurrenceVariables source.erase literal.atom) :
    boundedRetainedTerminalSlot
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex) =
      retainedAngularTerminalSlot
        source.erase routes fits literal.atom
        (literal.atom, clauseIndex, literalIndex)
        copyMember := by
  apply Fin.ext
  simp only [angularOccurrenceIndex,
    indexedOccurrence, retainedAngularTerminalSlot_val]
  apply boundedRetainedTerminalSlot_val_of_lt
  exact
    (retainedAngularTerminalSlot
      source.erase routes fits literal.atom
      (literal.atom, clauseIndex, literalIndex)
      copyMember).isLt

/-- Total retained source-to-fan-boundary route family. -/
def retainedAngularFanBoundaryIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            retainedAngularFanSplicedBoundaryRoute
              (routes clauseIndex literalIndex)
              (classifiedRetainedTerminalData
                (routeTerminalVector
                  (routes clauseIndex literalIndex)))
              (boundedRetainedTerminalSlot
                (angularOccurrenceIndex
                  (angularOccurrenceOrder source.erase routes)
                  literal clauseIndex literalIndex))

/-- Genuine presentation indices reduce the total family to the explicit
classified single-route splice. -/
theorem retainedAngularFanBoundaryIncidenceRoutes_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    retainedAngularFanBoundaryIncidenceRoutes
        source routes clauseIndex literalIndex =
      retainedAngularFanSplicedBoundaryRoute
        (routes clauseIndex literalIndex)
        (classifiedRetainedTerminalData
          (routeTerminalVector
            (routes clauseIndex literalIndex)))
        (boundedRetainedTerminalSlot
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            literal clauseIndex literalIndex)) := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [retainedAngularFanBoundaryIncidenceRoutes,
    clauseLookup, literalLookup]

/-- Every genuine retained boundary route has its exact scaled source
clause endpoint, exact scaled Figure 7 boundary endpoint, and
orthogonality. -/
theorem retainedAngularFanBoundaryIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase routes)
    (endpoints :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement clause) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal))
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (retainedRoutes :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex))
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedAngularFanBoundaryIncidenceRoutes
      source routes clauseIndex literalIndex).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              placement clause)) ∧
      (retainedAngularFanBoundaryIncidenceRoutes
        source routes clauseIndex literalIndex).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryPositionAt
                placement literal.atom
                (incidenceRelativeOffset clause literal)
                (angularOccurrenceIndex
                  (angularOccurrenceOrder source.erase routes)
                  literal clauseIndex literalIndex))) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanBoundaryIncidenceRoutes
          source routes clauseIndex literalIndex) := by
  let copy : ThreeOccurrenceVariable Variable :=
    (literal.atom, clauseIndex, literalIndex)
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      source clauseMember literalMember
  have copyMember :
      copy ∈ occurrenceVariables source.erase literal.atom := by
    exact occurrenceVariables_mem source.erase taggedMember
  let slot :=
    boundedRetainedTerminalSlot
      (angularOccurrenceIndex
        (angularOccurrenceOrder source.erase routes)
        literal clauseIndex literalIndex)
  have slotEq :
      slot =
        retainedAngularTerminalSlot
          source.erase routes fits literal.atom
          copy copyMember := by
    exact boundedRetainedTerminalSlot_eq_retainedAngularTerminalSlot
      source routes fits literal clauseIndex literalIndex copyMember
  have angularIndexLt :
      angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex < 8 := by
    simpa [angularOccurrenceIndex, indexedOccurrence, copy,
      retainedAngularTerminalSlot_val] using
      (retainedAngularTerminalSlot
        source.erase routes fits literal.atom
        copy copyMember).isLt
  have slotVal :
      slot.val =
        angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex := by
    exact boundedRetainedTerminalSlot_val_of_lt angularIndexLt
  have retainedVector :=
    certificate literal.atom copy copyMember
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (routeTerminalVector
          (routes clauseIndex literalIndex))).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff _).2
      retainedVector
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  have terminalEq :
      classifiedRetainedTerminalData
          (routeTerminalVector
            (routes clauseIndex literalIndex)) =
        terminal :=
    classifiedRetainedTerminalData_eq_of_classified
      classified
  have classifiedTotal :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (routes clauseIndex literalIndex)) =
        some
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (routes clauseIndex literalIndex))) := by
    rw [terminalEq]
    exact classified
  have routeEndpoints :=
    endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember
  have routeLastD :
      (routes clauseIndex literalIndex).getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause literal := by
    simp [List.getLastD_eq_getLast?, routeEndpoints.2]
  have valid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      (routes clauseIndex literalIndex)
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (routes clauseIndex literalIndex)))
      slot
      (lengths clause clauseIndex clauseMember
        literal literalIndex literalMember)
      classifiedTotal
      (retainedRoutes clause clauseIndex clauseMember
        literal literalIndex literalMember)
      routeEndpoints.1
  rw [retainedAngularFanBoundaryIncidenceRoutes_of_members
    source routes clauseMember literalMember]
  change
    _ ∧ _ ∧ _ at valid
  refine ⟨valid.1, ?_, valid.2.2⟩
  rw [valid.2.1]
  apply congrArg some
  rw [routeLastD]
  rw [angularFanBoundaryPositionAt_eq_scaledCenter_add_offset]
  rw [slotVal]
  simp only [PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset]
  rcases placement.position literal.atom with ⟨x, y⟩
  rcases placement.translation
    (Cell.sub literal.offset
      (PeriodicCNF.clauseAnchor clause.literals)) with ⟨dx, dy⟩
  rcases angularFanBoundaryOffset
    (angularOccurrenceIndex
      (angularOccurrenceOrder source.erase routes)
      literal clauseIndex literalIndex) with ⟨ox, oy⟩
  apply Prod.ext <;>
    simp [
      retainedTerminalFanTotalRefinement_eq,
      retainedTerminalFanRoutingRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      Cell.add, Cell.scale] <;>
    ring

end PeriodicEightOccurrenceSplit
end LeanTrominoes
