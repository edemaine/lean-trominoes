import LeanTrominoes.PeriodicCNFPlanarFormula
import LeanTrominoes.PlanarThreeSATOcurrences

/-!
# Occurrence bounds in the periodic planar-SAT construction

The fixed Figure 8 gadgets have small local occurrence bounds, but the full
planarizer shares carrier variables between crossover, equality-wire, bend,
and vertex components.  This file develops the componentwise accounting
needed to show that the routed periodic source fits the eight ports of
Figure 7.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- First endpoints of adjacent pairs form a sublist of the original list. -/
theorem consecutivePairs_fst_sublist
    {Value : Type*} (values : List Value) :
    List.Sublist
      ((consecutivePairs values).map Prod.fst) values := by
  induction values using List.twoStepInduction with
  | nil | singleton =>
      simp [consecutivePairs]
  | cons_cons first second rest _ tailInduction =>
      simp only [consecutivePairs, List.map_cons]
      exact List.Sublist.cons_cons first
        (tailInduction second)

/-- Second endpoints of adjacent pairs are exactly the tail of the original
list. -/
theorem consecutivePairs_snd
    {Value : Type*} (values : List Value) :
    (consecutivePairs values).map Prod.snd =
      values.tail := by
  induction values using List.twoStepInduction with
  | nil | singleton =>
      simp [consecutivePairs]
  | cons_cons first second rest _ tailInduction =>
      simp [consecutivePairs, tailInduction second]

/-- In particular, second endpoints form a sublist of the original list. -/
theorem consecutivePairs_snd_sublist
    {Value : Type*} (values : List Value) :
    List.Sublist
      ((consecutivePairs values).map Prod.snd) values := by
  rw [consecutivePairs_snd]
  exact List.tail_sublist values

/-- Both endpoints of every listed pair, once per pair. -/
def pairEndpoints {Value : Type*}
    (pairs : List (Value × Value)) : List Value :=
  pairs.flatMap fun pair => [pair.1, pair.2]

/-- Counting pair endpoints is the sum of counting first and second
projections. -/
theorem pairEndpoints_count
    {Value : Type*} [DecidableEq Value]
    (pairs : List (Value × Value)) (value : Value) :
    (pairEndpoints pairs).count value =
      (pairs.map Prod.fst).count value +
        (pairs.map Prod.snd).count value := by
  induction pairs with
  | nil =>
      simp [pairEndpoints]
  | cons pair pairs induction =>
      unfold pairEndpoints at induction ⊢
      simp only [List.flatMap_cons,
        List.count_append, List.map_cons,
        List.count_cons, List.count_nil]
      rw [induction]
      by_cases firstEqual : pair.1 = value <;>
        by_cases secondEqual : pair.2 = value <;>
          simp [firstEqual, secondEqual] <;>
          omega

/-- Any subfamily of adjacent pairs in a noduplicated list has endpoint
degree at most two. -/
theorem pairEndpoints_count_le_two_of_sublist_consecutivePairs
    {Value : Type*} [DecidableEq Value]
    {values : List Value} (valuesNodup : values.Nodup)
    {pairs : List (Value × Value)}
    (pairsSublist :
      List.Sublist pairs (consecutivePairs values))
    (value : Value) :
    (pairEndpoints pairs).count value ≤ 2 := by
  rw [pairEndpoints_count]
  have firstSublist :
      List.Sublist (pairs.map Prod.fst) values :=
    (pairsSublist.map Prod.fst).trans
      (consecutivePairs_fst_sublist values)
  have secondSublist :
      List.Sublist (pairs.map Prod.snd) values :=
    (pairsSublist.map Prod.snd).trans
      (consecutivePairs_snd_sublist values)
  have valueCountLeOne :
      values.count value ≤ 1 :=
    (List.nodup_iff_count_le_one.mp valuesNodup) value
  have firstLe :
      (pairs.map Prod.fst).count value ≤ 1 :=
    firstSublist.subperm.count_le value |>.trans
      valueCountLeOne
  have secondLe :
      (pairs.map Prod.snd).count value ≤ 1 :=
    secondSublist.subperm.count_le value |>.trans
      valueCountLeOne
  omega

/-- The combined site-and-template-variable map used by the carrier-node
crossover family. -/
def carrierNodeScopedCrossoverVariableMap
    (input : CrossingRecord × CrossoverVariable) :
    Sum CarrierNode (CrossingRecord × CrossoverInternal) :=
  scopedCrossoverVariableMap input.1
    (carrierNodeCrossingPorts input.1) input.2

/-- Different crossover sites and different roles name different variables
in the carrier-node crossover family. -/
theorem carrierNodeScopedCrossoverVariableMap_injective :
    Function.Injective carrierNodeScopedCrossoverVariableMap := by
  rintro ⟨firstSite, firstVariable⟩
    ⟨secondSite, secondVariable⟩ equal
  cases firstVariable <;>
    cases secondVariable <;>
      simp [carrierNodeScopedCrossoverVariableMap,
        scopedCrossoverVariableMap,
        carrierNodeCrossingPorts] at equal ⊢
  all_goals exact equal

/-- The complete family of fixed crossover gadgets retains the local
eight-occurrence bound. -/
theorem drawingCarrierNodeCrossoverFormula_occurrencesAtMostEight
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 8
      (drawingCarrierNodeCrossoverFormula graph) := by
  simpa [drawingCarrierNodeCrossoverFormula,
    crossoverFamily, scopedCrossoverInstance,
    carrierNodeScopedCrossoverVariableMap] using
    instantiateFamily_occurrencesAtMost_of_jointly_injective
      8 (orientedCrossings graph)
      (fun site =>
        scopedCrossoverVariableMap site
          (carrierNodeCrossingPorts site))
      crossingMacroOrigin 1 crossoverFormula
      (orientedCrossings_nodup graph)
      carrierNodeScopedCrossoverVariableMap_injective
      crossoverFormula_occurrencesAtMostEight

/-- Equality-link endpoints of one carrier chain are exactly the endpoints
of its retained adjacent carrier-node pairs. -/
theorem completeCarrierLinks_endpoints
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) :
    equalityLinkEndpoints (completeCarrierLinks graph key) =
      pairEndpoints
        ((consecutivePairs
          (completeCarrierNodes graph key)).filter fun pair =>
            !pair.1.sameCrossoverSite pair.2) := by
  simp [completeCarrierLinks,
    equalityLinkEndpoints, pairEndpoints,
    carrierNodePairLink, List.flatMap_map]

/-- A node is incident to at most two equality links in one simple carrier
chain. -/
theorem completeCarrierLinks_endpoint_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell)
    (node : CarrierNode) :
    (equalityLinkEndpoints
      (completeCarrierLinks graph key)).count node ≤ 2 := by
  rw [completeCarrierLinks_endpoints]
  apply
    pairEndpoints_count_le_two_of_sublist_consecutivePairs
      (completeCarrierNodes_nodup graph key)
  exact List.filter_sublist

/-- Every endpoint in a carrier chain records that chain's key. -/
theorem completeCarrierLinks_endpoint_key
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell)
    (node : CarrierNode)
    (nodeMem :
      node ∈ equalityLinkEndpoints
        (completeCarrierLinks graph key)) :
    node.carrierKey = key := by
  rcases List.mem_flatMap.mp nodeMem with
    ⟨link, linkMem, endpointMem⟩
  have common :=
    completeCarrierLinks_common_key graph key linkMem
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at endpointMem
  rcases endpointMem with endpointMem | endpointMem
  · exact
      (congrArg CarrierNode.carrierKey endpointMem).trans
        common.1
  · exact
      (congrArg CarrierNode.carrierKey endpointMem).trans
        common.2

/-- Carrier chains with the wrong key contain no occurrence of the given
node. -/
theorem completeCarrierLinks_endpoint_count_eq_zero_of_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell)
    (node : CarrierNode)
    (keyNe : key ≠ node.carrierKey) :
    (equalityLinkEndpoints
      (completeCarrierLinks graph key)).count node = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro nodeMem
  exact keyNe
    (completeCarrierLinks_endpoint_key
      graph key node nodeMem).symm

/-- Across any noduplicated collection of carrier keys, a node is still
incident to at most two links: only its own key can contribute. -/
theorem completeCarrierKeyFamily_endpoint_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (keys : List (Nat × Nat × Cell))
    (keysNodup : keys.Nodup)
    (node : CarrierNode) :
    (keys.flatMap fun key =>
      equalityLinkEndpoints
        (completeCarrierLinks graph key)).count node ≤ 2 := by
  induction keys with
  | nil =>
      simp
  | cons key keys induction =>
      have keyNotMem : key ∉ keys :=
        (List.nodup_cons.mp keysNodup).1
      have keysNodup' : keys.Nodup :=
        (List.nodup_cons.mp keysNodup).2
      simp only [List.flatMap_cons, List.count_append]
      by_cases keyEq : key = node.carrierKey
      · have tailZero :
            (keys.flatMap fun tailKey =>
              equalityLinkEndpoints
                (completeCarrierLinks graph tailKey)).count node = 0 := by
          apply List.count_eq_zero_of_not_mem
          intro nodeMem
          rcases List.mem_flatMap.mp nodeMem with
            ⟨tailKey, tailKeyMem, endpointMem⟩
          have nodeKey :=
            completeCarrierLinks_endpoint_key
              graph tailKey node endpointMem
          exact keyNotMem
            ((keyEq.trans nodeKey) ▸ tailKeyMem)
        rw [tailZero, Nat.add_zero]
        exact completeCarrierLinks_endpoint_count_le_two
          graph key node
      · rw [completeCarrierLinks_endpoint_count_eq_zero_of_ne
          graph key node keyEq, Nat.zero_add]
        exact induction keysNodup'

/-- Every carrier node is incident to at most two complete-carrier equality
links in the entire drawing block. -/
theorem drawingCompleteCarrierLinks_endpoint_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) :
    (equalityLinkEndpoints
      (drawingCompleteCarrierLinks graph)).count node ≤ 2 := by
  simpa [drawingCompleteCarrierLinks,
    equalityLinkEndpoints, List.flatMap_assoc] using
    completeCarrierKeyFamily_endpoint_count_le_two graph
      (drawingCompleteCarrierKeys graph)
      (List.nodup_dedup _) node

/-- The equality chains along all complete carriers contribute at most four
formula occurrences of any carrier node. -/
theorem drawingCompleteCarrierFormula_occurrencesAtMostFour
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 4
      (drawingCompleteCarrierFormula graph) := by
  apply equalityFamily_occurrencesAtMost
    (drawingCompleteCarrierLinks graph) 2 4 rfl
  exact drawingCompleteCarrierLinks_endpoint_count_le_two graph

/-- Every bend enumerated from a route tail retains the fixed route,
translation, and an incoming-segment index no smaller than the starting
index. -/
theorem routeBendsAux_member_data
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {routeBend : RouteBend},
      routeBend ∈
          routeBendsAux routeIndex translate startIndex points →
        routeBend.routeIndex = routeIndex ∧
          routeBend.translate = translate ∧
          startIndex ≤ routeBend.incomingSegmentIndex := by
  intro points
  induction points with
  | nil =>
      intro startIndex routeBend routeBendMem
      simp [routeBendsAux] at routeBendMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex routeBend routeBendMem
          simp [routeBendsAux] at routeBendMem
      | cons second rest =>
          cases rest with
          | nil =>
              intro startIndex routeBend routeBendMem
              simp [routeBendsAux] at routeBendMem
          | cons third rest =>
              intro startIndex routeBend routeBendMem
              simp only [routeBendsAux, List.mem_cons]
                at routeBendMem
              rcases routeBendMem with routeBendEq | routeBendMem
              · subst routeBend
                simp
              · have tailData :=
                  induction (startIndex + 1) routeBendMem
                exact
                  ⟨tailData.1, tailData.2.1,
                    Nat.le_trans
                      (Nat.le_add_right startIndex 1)
                      tailData.2.2⟩

/-- Within one enumerated route tail, the incoming segment index uniquely
identifies a bend. -/
theorem routeBendsAux_eq_of_index_eq
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {first second : RouteBend},
      first ∈
          routeBendsAux routeIndex translate startIndex points →
        second ∈
          routeBendsAux routeIndex translate startIndex points →
        first.incomingSegmentIndex =
          second.incomingSegmentIndex →
        first = second := by
  intro points
  induction points with
  | nil =>
      intro startIndex first second firstMem
      simp [routeBendsAux] at firstMem
  | cons firstPoint rest induction =>
      cases rest with
      | nil =>
          intro startIndex first second firstMem
          simp [routeBendsAux] at firstMem
      | cons secondPoint rest =>
          cases rest with
          | nil =>
              intro startIndex first second firstMem
              simp [routeBendsAux] at firstMem
          | cons thirdPoint rest =>
              intro startIndex first second firstMem secondMem indexEq
              simp only [routeBendsAux, List.mem_cons]
                at firstMem secondMem
              rcases firstMem with firstEq | firstMem <;>
                rcases secondMem with secondEq | secondMem
              · subst first
                subst second
                rfl
              · subst first
                have secondData :=
                  routeBendsAux_member_data routeIndex translate
                    (secondPoint :: thirdPoint :: rest)
                    (startIndex + 1) secondMem
                simp at indexEq
                omega
              · subst second
                have firstData :=
                  routeBendsAux_member_data routeIndex translate
                    (secondPoint :: thirdPoint :: rest)
                    (startIndex + 1) firstMem
                simp at indexEq
                omega
              · exact induction (startIndex + 1)
                  firstMem secondMem indexEq

/-- In the finite drawing enumeration, route index, translation, and
incoming-segment index jointly identify a bend. -/
theorem drawingRouteBends_eq_of_identity_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (routeEq : first.routeIndex = second.routeIndex)
    (translateEq : first.translate = second.translate)
    (indexEq :
      first.incomingSegmentIndex =
        second.incomingSegmentIndex) :
    first = second := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstTaggedRoute, firstTaggedRouteMem, firstTranslateMem⟩
  rcases List.mem_flatMap.mp firstTranslateMem with
    ⟨firstTranslate, firstTranslateMem, firstBendMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondTaggedRoute, secondTaggedRouteMem, secondTranslateMem⟩
  rcases List.mem_flatMap.mp secondTranslateMem with
    ⟨secondTranslate, secondTranslateMem, secondBendMem⟩
  have firstData :=
    routeBendsAux_member_data firstTaggedRoute.2 firstTranslate
      firstTaggedRoute.1 0 firstBendMem
  have secondData :=
    routeBendsAux_member_data secondTaggedRoute.2 secondTranslate
      secondTaggedRoute.1 0 secondBendMem
  have taggedRouteEq :
      firstTaggedRoute = secondTaggedRoute :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstTaggedRouteMem secondTaggedRouteMem
      (firstData.1.symm.trans
        (routeEq.trans secondData.1))
  subst secondTaggedRoute
  have translatesEq :
      firstTranslate = secondTranslate :=
    firstData.2.1.symm.trans
      (translateEq.trans secondData.2.1)
  subst secondTranslate
  exact
    routeBendsAux_eq_of_index_eq
      firstTaggedRoute.2 firstTranslate firstTaggedRoute.1 0
      firstBendMem secondBendMem indexEq

/-- Incoming terminals identify their bends inside the drawing
enumeration. -/
theorem drawingRouteBends_incomingTerminal_injective_on
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (terminalEq :
      first.incomingTerminal = second.incomingTerminal) :
    first = second := by
  apply drawingRouteBends_eq_of_identity_eq graph
    firstMem secondMem
  · exact congrArg
      (fun terminal => terminal.indexed.routeIndex) terminalEq
  · exact congrArg SegmentTerminal.translate terminalEq
  · exact congrArg
      (fun terminal => terminal.indexed.segmentIndex) terminalEq

/-- Outgoing terminals likewise identify their bends inside the drawing
enumeration. -/
theorem drawingRouteBends_outgoingTerminal_injective_on
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (terminalEq :
      first.outgoingTerminal = second.outgoingTerminal) :
    first = second := by
  apply drawingRouteBends_eq_of_identity_eq graph
    firstMem secondMem
  · exact congrArg
      (fun terminal => terminal.indexed.routeIndex) terminalEq
  · exact congrArg SegmentTerminal.translate terminalEq
  · have successorEq :
        first.incomingSegmentIndex + 1 =
          second.incomingSegmentIndex + 1 :=
      congrArg
        (fun terminal => terminal.indexed.segmentIndex) terminalEq
    omega

/-- Incoming and outgoing terminals can never coincide, even when they come
from different bends, because they name different segment ends. -/
theorem RouteBend.incomingTerminal_ne_outgoingTerminal
    (first second : RouteBend) :
    first.incomingTerminal ≠ second.outgoingTerminal := by
  intro terminalEq
  have endpointEq :=
    congrArg SegmentTerminal.endpoint terminalEq
  simp [RouteBend.incomingTerminal,
    RouteBend.outgoingTerminal] at endpointEq

/-- Carrier-node endpoints of a bend list, with the incoming endpoint
followed by the outgoing endpoint of each bend. -/
def routeBendEndpointNodes (routeBends : List RouteBend) :
    List CarrierNode :=
  routeBends.flatMap fun routeBend =>
    [.terminal routeBend.incomingTerminal,
      .terminal routeBend.outgoingTerminal]

/-- A noduplicated sublist of the drawing's bend records has a noduplicated
endpoint list.  Same-role collisions identify their bends; cross-role
collisions are impossible. -/
theorem routeBendEndpointNodes_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ∀ (routeBends : List RouteBend),
      routeBends.Nodup →
      (∀ routeBend ∈ routeBends,
        routeBend ∈ drawingRouteBends graph) →
      (routeBendEndpointNodes routeBends).Nodup := by
  intro routeBends
  induction routeBends with
  | nil =>
      simp [routeBendEndpointNodes]
  | cons routeBend routeBends induction =>
      intro bendsNodup allMembers
      have routeBendMem :
          routeBend ∈ drawingRouteBends graph :=
        allMembers routeBend (by simp)
      have tailMembers :
          ∀ tailBend ∈ routeBends,
            tailBend ∈ drawingRouteBends graph := by
        intro tailBend tailBendMem
        exact allMembers tailBend
          (List.mem_cons_of_mem routeBend tailBendMem)
      have routeBendNotMem : routeBend ∉ routeBends :=
        (List.nodup_cons.mp bendsNodup).1
      have tailNodup : routeBends.Nodup :=
        (List.nodup_cons.mp bendsNodup).2
      change
        (CarrierNode.terminal routeBend.incomingTerminal ::
          CarrierNode.terminal routeBend.outgoingTerminal ::
            routeBendEndpointNodes routeBends).Nodup
      rw [List.nodup_cons, List.nodup_cons]
      constructor
      · intro incomingMem
        simp only [List.mem_cons] at incomingMem
        rcases incomingMem with outgoingEq | tailMem
        · exact
            (routeBend.incomingTerminal_ne_outgoingTerminal
              routeBend)
              (CarrierNode.terminal.inj outgoingEq)
        · rcases List.mem_flatMap.mp tailMem with
            ⟨tailBend, tailBendMem, endpointMem⟩
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at endpointMem
          rcases endpointMem with incomingEq | outgoingEq
          · have bendEq :=
              drawingRouteBends_incomingTerminal_injective_on
                graph routeBendMem
                (tailMembers tailBend tailBendMem)
                (CarrierNode.terminal.inj incomingEq)
            exact routeBendNotMem (bendEq ▸ tailBendMem)
          · exact
              (routeBend.incomingTerminal_ne_outgoingTerminal
                tailBend)
                (CarrierNode.terminal.inj outgoingEq)
      · constructor
        · intro tailMem
          rcases List.mem_flatMap.mp tailMem with
            ⟨tailBend, tailBendMem, endpointMem⟩
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at endpointMem
          rcases endpointMem with incomingEq | outgoingEq
          · exact
              (tailBend.incomingTerminal_ne_outgoingTerminal
                routeBend)
                (CarrierNode.terminal.inj incomingEq.symm)
          · have bendEq :=
              drawingRouteBends_outgoingTerminal_injective_on
                graph routeBendMem
                (tailMembers tailBend tailBendMem)
                (CarrierNode.terminal.inj outgoingEq)
            exact routeBendNotMem (bendEq ▸ tailBendMem)
        · exact induction tailNodup tailMembers

/-- Bend-link endpoints are precisely the two terminal nodes of each
deduplicated bend record. -/
theorem drawingRouteBendLinks_endpoints
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    equalityLinkEndpoints (drawingRouteBendLinks graph) =
      routeBendEndpointNodes (drawingRouteBends graph).dedup := by
  simp [drawingRouteBendLinks, equalityLinkEndpoints,
    routeBendEndpointNodes, RouteBend.equalityLink,
    List.flatMap_map]

/-- Every carrier node is an endpoint of at most one bend link. -/
theorem drawingRouteBendLinks_endpoint_count_le_one
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) :
    (equalityLinkEndpoints
      (drawingRouteBendLinks graph)).count node ≤ 1 := by
  rw [drawingRouteBendLinks_endpoints]
  have endpointsNodup :=
    routeBendEndpointNodes_nodup graph
      (drawingRouteBends graph).dedup
      (List.nodup_dedup _)
      (by
        intro routeBend routeBendMem
        exact List.mem_dedup.mp routeBendMem)
  exact List.nodup_iff_count_le_one.mp endpointsNodup node

/-- Bend equalities contribute at most two formula occurrences of any
carrier node. -/
theorem drawingRouteBendFormula_occurrencesAtMostTwo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 2
      (drawingRouteBendFormula graph) := by
  apply equalityFamily_occurrencesAtMost
    (drawingRouteBendLinks graph) 1 2 rfl
  exact drawingRouteBendLinks_endpoint_count_le_one graph

/-- Straight-chain and bend equality clauses together use every carrier node
at most six times. -/
theorem drawingRouteWireFormula_occurrencesAtMostSix
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 6
      (drawingRouteWireFormula graph) := by
  simpa [drawingRouteWireFormula] using
    formulaOccurrencesAtMost_append
      (drawingCompleteCarrierFormula_occurrencesAtMostFour graph)
      (drawingRouteBendFormula_occurrencesAtMostTwo graph)

end PeriodicOrthocrossing
end LeanTrominoes
