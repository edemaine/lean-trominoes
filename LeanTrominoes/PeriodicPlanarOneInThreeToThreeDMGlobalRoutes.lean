import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositions
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Global incidence routes for the planar 3DM assembly

This file emits one route for each encoded RGB incidence.  Clause-core
incidences are translated copies of the checked clause drawing.  A variable
incidence starts with its route in the checked complete variable-site
drawing; the uniquely classified routed incidence is then joined to its
certified three-strand corridor.

The construction is indexed by attached typed triples, so all membership
proofs needed to select the correct finite variable site remain internal.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Membership of an ordinary typed triple identifies its active variable
and occurrence block. -/
theorem ordinaryTriple_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      Triple.ordinary atom slot variant localTriple ∈
        occurrenceTriples source atom slot := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · rw [variableTriples_eq_occurrenceEntries_flatMap] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨entry, entryMember, blockMember⟩
    rcases entry with ⟨entryAtom, entrySlot⟩
    have entryParts :=
      (mem_occurrenceEntries_iff
        source entryAtom entrySlot).mp entryMember
    cases kindEq :
        occurrenceConnectorKind source entryAtom entrySlot <;>
      simp [occurrenceTriples, kindEq, allFixedRedTriples,
        allOrdinaryTriples] at blockMember
    all_goals
      rcases blockMember with
        ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩
    all_goals
      simp_all [occurrenceTriples, allOrdinaryTriples]
  · simp [clauseTriples, allClauseSets] at clauseMember

/-- Membership of a fixed-red typed triple identifies its active variable
and occurrence block. -/
theorem fixedRedTriple_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      Triple.fixedRed atom slot localTriple ∈
        occurrenceTriples source atom slot := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · rw [variableTriples_eq_occurrenceEntries_flatMap] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨entry, entryMember, blockMember⟩
    rcases entry with ⟨entryAtom, entrySlot⟩
    have entryParts :=
      (mem_occurrenceEntries_iff
        source entryAtom entrySlot).mp entryMember
    cases kindEq :
        occurrenceConnectorKind source entryAtom entrySlot <;>
      simp [occurrenceTriples, kindEq, allFixedRedTriples,
        allOrdinaryTriples] at blockMember
    all_goals
      rcases blockMember with
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩
    all_goals
      simp_all [occurrenceTriples, allFixedRedTriples]
  · simp [clauseTriples, allClauseSets] at clauseMember

/-- An ordinary variable incidence route inside its complete finite site,
translated to the global variable origin. -/
def assembledOrdinaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) : List Cell :=
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  PeriodicOrthocrossing.translatePolyline
    (routing.variableOrigin atom)
    (typedVariableSiteRoute source atom location.1 slot location.2.1
      (.ordinary atom slot variant localTriple) location.2.2
      color)

/-- A fixed-red variable incidence route inside its complete finite site,
translated to the global variable origin. -/
def assembledFixedRedPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) : List Cell :=
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  PeriodicOrthocrossing.translatePolyline
    (routing.variableOrigin atom)
    (typedVariableSiteRoute source atom location.1 slot location.2.1
      (.fixedRed atom slot localTriple) location.2.2 color)

/-- A clause-core incidence translated to its global clause neighborhood. -/
def assembledClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (routing.clauseOrigin clauseIndex)
    (orientedIncidenceLocalRoute source (.clause clauseIndex set) color)

/-- Every translated ordinary variable-site prefix is rectilinear. -/
theorem assembledOrdinaryPrefix_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.ordinary atom slot variant localTriple) location.2.2
          color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact typedVariableSiteRoute_orthogonal source atom location.1
      slot location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color segment segmentMember
  exact localOrthogonal.translate (routing.variableOrigin atom)

/-- Every translated fixed-red variable-site prefix is rectilinear. -/
theorem assembledFixedRedPrefix_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledFixedRedPrefix routing atom slot localTriple
        member color) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.fixedRed atom slot localTriple) location.2.2 color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact typedVariableSiteRoute_orthogonal source atom location.1
      slot location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color segment segmentMember
  exact localOrthogonal.translate (routing.variableOrigin atom)

/-- Every translated clause-core route is rectilinear. -/
theorem assembledClauseRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledClauseRoute routing clauseIndex set color) := by
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (orientedIncidenceLocalRoute
          source (.clause clauseIndex set) color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact orientedIncidenceLocalRoute_orthogonal source
      (.clause clauseIndex set) color segment segmentMember
  exact localOrthogonal.translate (routing.clauseOrigin clauseIndex)

/-- If an ordinary incidence is the routed connector incidence, its
translated finite prefix ends exactly at the corresponding certified
corridor port. -/
theorem assembledOrdinaryPrefix_getLast_routed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor)
    (routed :
      Triple.ordinary atom slot variant localTriple =
        routedOccurrenceTriple source atom slot color) :
    let location :=
      ordinaryTriple_location source atom slot variant localTriple member
    let entry : ActiveOccurrenceEntry source :=
      ⟨(atom, slot),
        (mem_occurrenceEntries_iff source atom slot).mpr
          ⟨location.1, location.2.1⟩⟩
    (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color).getLast? =
      some (Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color
  simp only [assembledOrdinaryPrefix,
    PeriodicOrthocrossing.translatePolyline, List.getLast?_map,
    endpoints.2, Option.map_some]
  congr 2
  simp only [routedVariablePortPosition,
    routedActiveVariableSiteTriple]
  congr 2
  apply Subtype.ext
  exact congrArg variableSiteTripleOfTyped routed

/-- The analogous fixed-red routed prefix ends at its certified RGB
corridor port. -/
theorem assembledFixedRedPrefix_getLast_routed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor)
    (routed :
      Triple.fixedRed atom slot localTriple =
        routedOccurrenceTriple source atom slot color) :
    let location :=
      fixedRedTriple_location source atom slot localTriple member
    let entry : ActiveOccurrenceEntry source :=
      ⟨(atom, slot),
        (mem_occurrenceEntries_iff source atom slot).mpr
          ⟨location.1, location.2.1⟩⟩
    (assembledFixedRedPrefix routing atom slot localTriple
        member color).getLast? =
      some (Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color
  simp only [assembledFixedRedPrefix,
    PeriodicOrthocrossing.translatePolyline, List.getLast?_map,
    endpoints.2, Option.map_some]
  congr 2
  simp only [routedVariablePortPosition,
    routedActiveVariableSiteTriple]
  congr 2
  apply Subtype.ext
  exact congrArg variableSiteTripleOfTyped routed

/-- Complete route of one active typed incidence. -/
def assembledTypedIncidenceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) : List Cell :=
  match tripleEq : triple.1 with
  | .ordinary atom slot variant localTriple =>
      let member :
          Triple.ordinary atom slot variant localTriple ∈
            triples source :=
        tripleEq ▸ triple.2
      let prefixRoute :=
        assembledOrdinaryPrefix routing atom slot variant localTriple
          member color
      if _routed :
          Triple.ordinary atom slot variant localTriple =
            routedOccurrenceTriple source atom slot color then
        let location :=
          ordinaryTriple_location source atom slot variant localTriple
            member
        let entry : ActiveOccurrenceEntry source :=
          ⟨(atom, slot),
            (mem_occurrenceEntries_iff source atom slot).mpr
              ⟨location.1, location.2.1⟩⟩
        joinAtEndpoint prefixRoute (routing.route entry color)
      else
        prefixRoute
  | .fixedRed atom slot localTriple =>
      let member :
          Triple.fixedRed atom slot localTriple ∈ triples source :=
        tripleEq ▸ triple.2
      let prefixRoute :=
        assembledFixedRedPrefix routing atom slot localTriple
          member color
      if _routed :
          Triple.fixedRed atom slot localTriple =
            routedOccurrenceTriple source atom slot color then
        let location :=
          fixedRedTriple_location source atom slot localTriple member
        let entry : ActiveOccurrenceEntry source :=
          ⟨(atom, slot),
            (mem_occurrenceEntries_iff source atom slot).mpr
              ⟨location.1, location.2.1⟩⟩
        joinAtEndpoint prefixRoute (routing.route entry color)
      else
        prefixRoute
  | .clause clauseIndex set =>
      assembledClauseRoute routing clauseIndex set color

/-- Every complete typed incidence route is rectilinear. -/
theorem assembledTypedIncidenceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledTypedIncidenceRoute routing triple color) := by
  unfold assembledTypedIncidenceRoute
  split
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        ordinaryTriple_location source atom slot variant localTriple
          member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      apply
        (assembledOrdinaryPrefix_orthogonal routing atom slot variant
          localTriple member color).joinAtEndpoint
          (routing.route_orthogonal entry color)
      · exact assembledOrdinaryPrefix_getLast_routed routing atom slot
          variant localTriple member color routed
      · exact (routing.route_endpoints entry color).1
    next notRouted =>
      exact assembledOrdinaryPrefix_orthogonal routing atom slot variant
        localTriple member color
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        fixedRedTriple_location source atom slot localTriple member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      apply
        (assembledFixedRedPrefix_orthogonal routing atom slot localTriple
          member color).joinAtEndpoint
          (routing.route_orthogonal entry color)
      · exact assembledFixedRedPrefix_getLast_routed routing atom slot
          localTriple member color routed
      · exact (routing.route_endpoints entry color).1
    next notRouted =>
      exact assembledFixedRedPrefix_orthogonal routing atom slot
        localTriple member color
  next clauseIndex set tripleEq =>
    exact assembledClauseRoute_orthogonal
      routing clauseIndex set color

/-- Edge-route list in encoded triple-major, RGB-minor order. -/
def assembledEdgeRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : List (List Cell) :=
  (triples source).attach.flatMap fun triple =>
    PeriodicThreeDM.incidenceColors.map fun color =>
      assembledTypedIncidenceRoute routing triple color

/-- The assembled route list has exactly one entry per encoded incidence
graph edge. -/
theorem assembledEdgeRoutes_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledEdgeRoutes routing).length =
      (encodedProblem source).incidenceGraph.edges.length := by
  simp [assembledEdgeRoutes, encodedProblem, TypedProblem.encode,
    PeriodicThreeDM.incidenceGraph,
    PeriodicThreeDM.tripleIncidenceEdges,
    PeriodicThreeDM.incidenceColors, problem]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
