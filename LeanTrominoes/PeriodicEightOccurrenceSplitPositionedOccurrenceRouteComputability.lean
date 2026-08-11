import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedRoutesComputability

/-!
# Computable lookup for positioned fixed-eight routes

This module assembles the primitive-recursive local geometry into the total
presentation-indexed canonical route family.  The executable definition uses
only compass-port and ordered-copy lookups; a definitional equation identifies
it with the existing proof-carrying angular-splice construction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

set_option maxHeartbeats 3000000

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- One copied source incidence, expressed using only the computational fields
of an angular occurrence order. -/
def canonicalAngularOccurrenceRouteData
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (ports : OccurrencePorts)
    (copies : Variable → List (ThreeOccurrenceVariable Variable))
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  let occurrenceIndex :=
    (copies literal.atom).idxOf
      (indexedOccurrence literal clauseIndex literalIndex)
  let relative := incidenceRelativeOffset clause literal
  joinAtEndpoint
    (PositionedPeriodicCNF.orthogonalDetour
      (PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement)
        (occurrenceClause ports clauseIndex clause))
      (angularFanBoundaryPositionAt sourcePlacement literal.atom
        relative occurrenceIndex))
    (angularFanSpokeRouteAt sourcePlacement literal.atom
      relative occurrenceIndex)

/-- Copied-clause route lookup without proof fields. -/
def canonicalAngularCopiedIncidenceRoutesData
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (ports : OccurrencePorts)
    (copies : Variable → List (ThreeOccurrenceVariable Variable))
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        match clause.literals[literalIndex]? with
        | none => []
        | some literal =>
            canonicalAngularOccurrenceRouteData
              sourcePlacement ports copies clause literal
              clauseIndex literalIndex

/-- Total fixed-eight route lookup without proof fields. -/
def canonicalAngularSplicedIncidenceRoutesData
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (ports : OccurrencePorts)
    (copies : Variable → List (ThreeOccurrenceVariable Variable)) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    if clauseIndex < (occurrenceClauses source ports).length then
      canonicalAngularCopiedIncidenceRoutesData
        sourcePlacement ports copies source clauseIndex literalIndex
    else
      allCycleRoutes source sourcePlacement
        (clauseIndex - (occurrenceClauses source ports).length)
        literalIndex

/-- Erasing the proof fields of an angular order leaves the existing
canonical route family definitionally unchanged. -/
theorem canonicalAngularSplicedIncidenceRoutes_eq_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase) :
    canonicalAngularSplicedIncidenceRoutes
        source sourcePlacement order =
      canonicalAngularSplicedIncidenceRoutesData
        source sourcePlacement
        (occurrencePortsOfAngularOrder source.erase order)
        order.copies := by
  funext clauseIndex literalIndex
  by_cases occurrence :
      clauseIndex <
        (occurrenceClauses source
          (occurrencePortsOfAngularOrder source.erase order)).length
  · simp only [canonicalAngularSplicedIncidenceRoutes,
      angularSplicedIncidenceRoutes,
      canonicalAngularSplicedIncidenceRoutesData,
      canonicalAngularCopiedIncidenceRoutesData,
      occurrence, if_pos]
    cases clauseLookup : source.clauses[clauseIndex]? with
    | none =>
        simp [angularSplicedOccurrenceRoutes, clauseLookup]
    | some clause =>
        cases literalLookup : clause.literals[literalIndex]? with
        | none =>
            simp [angularSplicedOccurrenceRoutes, clauseLookup,
              literalLookup]
        | some literal =>
            simp [angularSplicedOccurrenceRoutes,
              angularSplicedOccurrenceRoute,
              canonicalAngularBoundaryRoutes,
              canonicalAngularBoundaryIncidenceRoutes,
              angularOccurrenceSuffix,
              canonicalAngularOccurrenceRouteData,
              angularOccurrenceIndex, clauseLookup, literalLookup]
  · simp [canonicalAngularSplicedIncidenceRoutes,
      angularSplicedIncidenceRoutes,
      canonicalAngularSplicedIncidenceRoutesData, occurrence]

theorem occurrence_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (item : ThreeOccurrenceVariable Variable)
    (items : List (ThreeOccurrenceVariable Variable)) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq item items = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

theorem canonicalAngularOccurrenceRouteData_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (clause : Input → PositionedPeriodicClause Variable)
    (literal : Input → PeriodicLiteral Variable)
    (clauseIndex literalIndex : Input → Nat)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2)
    (clausePrimrec : Primrec clause)
    (literalPrimrec : Primrec literal)
    (clauseIndexPrimrec : Primrec clauseIndex)
    (literalIndexPrimrec : Primrec literalIndex) :
    Primrec fun input =>
      canonicalAngularOccurrenceRouteData
        (sourcePlacement input) (ports input) (copies input)
        (clause input) (literal input)
        (clauseIndex input) (literalIndex input) := by
  have copiedClause : Primrec fun input =>
      occurrenceClause (ports input) (clauseIndex input) (clause input) :=
    occurrenceClause_primrec ports portsPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair Primrec.id clauseIndexPrimrec)
        clausePrimrec)
  have splitPeriod : Primrec fun input =>
      (placement (sourcePlacement input)).period :=
    placement_period_primrec sourcePlacement periodPrimrec
  have sourcePoint : Primrec fun input =>
      PositionedPeriodicCNF.canonicalClausePosition
        (placement (sourcePlacement input))
        (occurrenceClause
          (ports input) (clauseIndex input) (clause input)) :=
    PositionedPeriodicCNF.canonicalClausePosition_primrec
      (fun input => (placement (sourcePlacement input)).period)
      splitPeriod |>.comp
        (Primrec.pair Primrec.id copiedClause)
  have relative : Primrec fun input =>
      incidenceRelativeOffset (clause input) (literal input) :=
    incidenceRelativeOffset_primrec.comp
      (Primrec.pair clausePrimrec literalPrimrec)
  have atom : Primrec fun input => (literal input).atom :=
    PeriodicThreeCNF.literal_atom_primrec.comp literalPrimrec
  have copyList : Primrec fun input =>
      copies input (literal input).atom :=
    copiesPrimrec.comp (Primrec.pair Primrec.id atom)
  have occurrence : Primrec fun input =>
      indexedOccurrence (literal input)
        (clauseIndex input) (literalIndex input) :=
    Primrec.pair atom
      (Primrec.pair clauseIndexPrimrec literalIndexPrimrec)
  have occurrenceIndex : Primrec fun input =>
      (copies input (literal input).atom).idxOf
        (indexedOccurrence (literal input)
          (clauseIndex input) (literalIndex input)) :=
    (Primrec.list_idxOf.comp occurrence copyList).of_eq fun input =>
      occurrence_idxOf_decidableEq_eq
        (indexedOccurrence (literal input)
          (clauseIndex input) (literalIndex input))
        (copies input (literal input).atom)
  have boundaryPoint : Primrec fun input =>
      angularFanBoundaryPositionAt
        (sourcePlacement input) (literal input).atom
        (incidenceRelativeOffset (clause input) (literal input))
        ((copies input (literal input).atom).idxOf
          (indexedOccurrence (literal input)
            (clauseIndex input) (literalIndex input))) :=
    angularFanBoundaryPositionAt_primrec
      sourcePlacement periodPrimrec positionPrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair Primrec.id atom) relative)
          occurrenceIndex)
  have routePrefix : Primrec fun input =>
      PositionedPeriodicCNF.orthogonalDetour
        (PositionedPeriodicCNF.canonicalClausePosition
          (placement (sourcePlacement input))
          (occurrenceClause
            (ports input) (clauseIndex input) (clause input)))
        (angularFanBoundaryPositionAt
          (sourcePlacement input) (literal input).atom
          (incidenceRelativeOffset (clause input) (literal input))
          ((copies input (literal input).atom).idxOf
            (indexedOccurrence (literal input)
              (clauseIndex input) (literalIndex input)))) :=
    PositionedPeriodicCNF.orthogonalDetour_primrec.comp
      sourcePoint boundaryPoint
  have suffix : Primrec fun input =>
      angularFanSpokeRouteAt
        (sourcePlacement input) (literal input).atom
        (incidenceRelativeOffset (clause input) (literal input))
        ((copies input (literal input).atom).idxOf
          (indexedOccurrence (literal input)
            (clauseIndex input) (literalIndex input))) :=
    angularFanSpokeRouteAt_primrec
      sourcePlacement periodPrimrec positionPrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair Primrec.id atom) relative)
          occurrenceIndex)
  exact (joinAtEndpoint_primrec _ _ routePrefix suffix).of_eq fun _ => rfl

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
