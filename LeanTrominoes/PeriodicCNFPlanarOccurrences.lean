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
      8 (orientedCrossingHalo graph)
      (fun site =>
        scopedCrossoverVariableMap site
          (carrierNodeCrossingPorts site))
      crossingMacroOrigin 1 crossoverFormula
      (orientedCrossingHalo_nodup graph)
      carrierNodeScopedCrossoverVariableMap_injective
      crossoverFormula_occurrencesAtMostEight

/-- Every external boundary port occurs exactly in its two local crossover
implication clauses, and therefore at most twice in the entire crossover
family. -/
theorem drawingCarrierNodeCrossoverFormula_external_count_le_two
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) :
    @List.count
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))
      instBEqOfDecidableEq (.inl node)
      (embeddedVariableOccurrences
        (drawingCarrierNodeCrossoverFormula graph)) ≤ 2 := by
  simpa [drawingCarrierNodeCrossoverFormula,
    crossoverFamily, scopedCrossoverInstance,
    carrierNodeScopedCrossoverVariableMap] using
    instantiateFamily_occurrence_count_le_of_jointly_injective
      2 (orientedCrossingHalo graph)
      (fun site =>
        scopedCrossoverVariableMap site
          (carrierNodeCrossingPorts site))
      crossingMacroOrigin 1 crossoverFormula
      (orientedCrossingHalo_nodup graph)
      carrierNodeScopedCrossoverVariableMap_injective
      (.inl node)
      (by
        rintro ⟨site, sourceVariable⟩ sourceEq
        apply crossoverFormula_boundary_count_le_two
        cases sourceVariable <;>
          simp [scopedCrossoverVariableMap,
            carrierNodeCrossingPorts] at sourceEq ⊢)

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

/-- Scoping route-wire variables into the external summand preserves the
six-occurrence bound. -/
theorem scopedDrawingRouteWireFormula_occurrencesAtMostSix
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 6
      (scopedDrawingRouteWireFormula graph) := by
  simpa [scopedDrawingRouteWireFormula,
    EmbeddedClause.rename] using
    formulaOccurrencesAtMost_map_of_injective
      6
      (fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))
      id (drawingRouteWireFormula graph)
      (fun first second equal =>
        Sum.inl.inj equal)
      (drawingRouteWireFormula_occurrencesAtMostSix graph)

/-- Route-wire clauses contain no crossover-internal variables. -/
theorem scopedDrawingRouteWireFormula_internal_count_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (internal : CrossingRecord × CrossoverInternal) :
    @List.count
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))
      instBEqOfDecidableEq (.inr internal)
      (embeddedVariableOccurrences
        (scopedDrawingRouteWireFormula graph)) = 0 := by
  apply @List.count_eq_zero_of_not_mem
    (Sum CarrierNode (CrossingRecord × CrossoverInternal))
    instBEqOfDecidableEq (by infer_instance)
  simp [scopedDrawingRouteWireFormula,
    EmbeddedClause.rename]

/-- The complete crossover-and-route core fits the paper's degree-eight
budget.  External nodes contribute at most `2 + 6`; internal nodes occur only
in their crossover family. -/
theorem drawingRoutePlanarCoreFormula_occurrencesAtMostEight
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 8
      (drawingRoutePlanarCoreFormula graph) := by
  intro atom
  rw [drawingRoutePlanarCoreFormula,
    embeddedVariableOccurrences_append]
  rw [@List.count_append
    (Sum CarrierNode (CrossingRecord × CrossoverInternal))
    instBEqOfDecidableEq]
  cases atom with
  | inl node =>
      exact Nat.add_le_add
        (drawingCarrierNodeCrossoverFormula_external_count_le_two
          graph node)
        (scopedDrawingRouteWireFormula_occurrencesAtMostSix
          graph (.inl node))
  | inr internal =>
      rw [scopedDrawingRouteWireFormula_internal_count_eq_zero,
        Nat.add_zero]
      exact
        drawingCarrierNodeCrossoverFormula_occurrencesAtMostEight
          graph (.inr internal)

/-! ## Routed SAT vertex families -/

/-- Within the neighboring route enumeration, the global edge index and
translation identify the complete metadata-rich occurrence. -/
theorem drawingCNFRouteOccurrences_eq_of_edgeIndex_eq_of_translate_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : CNFRouteOccurrence Variable}
    (firstMem : first ∈ drawingCNFRouteOccurrences formula)
    (secondMem : second ∈ drawingCNFRouteOccurrences formula)
    (edgeIndexEq : first.edgeIndex = second.edgeIndex)
    (translateEq : first.translate = second.translate) :
    first = second := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstTagged, firstTaggedMem, firstTranslateMem⟩
  rcases List.mem_map.mp firstTranslateMem with
    ⟨firstTranslate, firstTranslateMem, firstEq⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondTagged, secondTaggedMem, secondTranslateMem⟩
  rcases List.mem_map.mp secondTranslateMem with
    ⟨secondTranslate, secondTranslateMem, secondEq⟩
  subst first
  subst second
  have taggedEq :
      firstTagged = secondTagged :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstTaggedMem secondTaggedMem edgeIndexEq
  subst secondTagged
  change firstTranslate = secondTranslate at translateEq
  subst secondTranslate
  rfl

/-- Source terminals identify neighboring CNF route occurrences. -/
theorem drawingCNFRouteOccurrences_sourceTerminal_injective_on
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : CNFRouteOccurrence Variable}
    (firstMem : first ∈ drawingCNFRouteOccurrences formula)
    (secondMem : second ∈ drawingCNFRouteOccurrences formula)
    (terminalEq :
      first.sourceTerminal formula =
        second.sourceTerminal formula) :
    first = second := by
  apply
    drawingCNFRouteOccurrences_eq_of_edgeIndex_eq_of_translate_eq
      formula firstMem secondMem
  · exact congrArg
      (fun terminal => terminal.indexed.routeIndex) terminalEq
  · exact congrArg SegmentTerminal.translate terminalEq

/-- Target terminals likewise identify neighboring CNF route
occurrences. -/
theorem drawingCNFRouteOccurrences_targetTerminal_injective_on
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : CNFRouteOccurrence Variable}
    (firstMem : first ∈ drawingCNFRouteOccurrences formula)
    (secondMem : second ∈ drawingCNFRouteOccurrences formula)
    (terminalEq :
      first.targetTerminal formula =
        second.targetTerminal formula) :
    first = second := by
  apply
    drawingCNFRouteOccurrences_eq_of_edgeIndex_eq_of_translate_eq
      formula firstMem secondMem
  · exact congrArg
      (fun terminal => terminal.indexed.routeIndex) terminalEq
  · exact congrArg SegmentTerminal.translate terminalEq

/-- The finite list of represented clause sites has no duplicates. -/
theorem drawingClauseRouteSites_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingClauseRouteSites formula).Nodup := by
  have indicesPairwise :
      formula.clauses.zipIdx.Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact List.nodup_zipIdx_map_snd formula.clauses
  rw [drawingClauseRouteSites, List.nodup_flatMap]
  constructor
  · intro taggedClause _
    exact neighborTranslations_nodup.map
      (fun first second equal =>
        congrArg Prod.snd equal)
  · exact indicesPairwise.imp fun {first second} indexNe => by
      change List.Disjoint
        (neighborTranslations.map fun translate =>
          (first.2, translate))
        (neighborTranslations.map fun translate =>
          (second.2, translate))
      rw [List.disjoint_left]
      intro site firstMem secondMem
      rcases List.mem_map.mp firstMem with
        ⟨firstTranslate, firstTranslateMem, siteEq⟩
      rcases List.mem_map.mp secondMem with
        ⟨secondTranslate, secondTranslateMem, siteEq'⟩
      have indexEq :
          first.2 = second.2 := by
        exact congrArg Prod.fst (siteEq.trans siteEq'.symm)
      exact indexNe indexEq

/-- Every routed occurrence selected at a represented clause site belongs
to the global neighboring occurrence enumeration. -/
theorem clauseRouteOccurrencesAt_mem_drawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : ClauseRouteSite}
    (siteMem : site ∈ drawingClauseRouteSites formula)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ clauseRouteOccurrencesAt formula site) :
    occurrence ∈ drawingCNFRouteOccurrences formula := by
  rcases List.mem_flatMap.mp siteMem with
    ⟨taggedClause, taggedClauseMem, siteMem⟩
  rcases List.mem_map.mp siteMem with
    ⟨translate, translateMem, siteEq⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceEq⟩
  subst site
  subst occurrence
  apply List.mem_flatMap.mpr
  refine ⟨taggedIncidence, ?_, ?_⟩
  · exact (List.mem_filter.mp taggedIncidenceMem).1
  · exact List.mem_map.mpr
      ⟨translate, translateMem, rfl⟩

/-- A selected clause-route occurrence reaches exactly its selecting
clause site. -/
theorem clauseRouteOccurrencesAt_clauseOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ clauseRouteOccurrencesAt formula site) :
    occurrence.clauseOccurrence = site := by
  rcases List.mem_map.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceEq⟩
  subst occurrence
  have clauseIndexEq :=
    of_decide_eq_true
      (List.mem_filter.mp taggedIncidenceMem).2
  exact Prod.ext clauseIndexEq rfl

/-- At one clause site the selected route occurrences are duplicate-free. -/
theorem clauseRouteOccurrencesAt_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (clauseRouteOccurrencesAt formula site).Nodup := by
  have taggedNodup :
      (PeriodicCNF.incidencesWithMetadata formula).zipIdx.Nodup :=
    (List.nodup_zipIdx_map_snd
      (PeriodicCNF.incidencesWithMetadata formula)).of_map
        Prod.snd
  exact (taggedNodup.filter _).map
    (fun first second equal => by
      apply Prod.ext
      · exact congrArg CNFRouteOccurrence.incidence equal
      · exact congrArg CNFRouteOccurrence.edgeIndex equal)

/-- Equality of two selected source terminals identifies both their routed
occurrences and their selecting clause sites. -/
theorem clauseRouteOccurrencesAt_eq_and_site_eq_of_sourceTerminal_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstSite secondSite : ClauseRouteSite}
    {first second : CNFRouteOccurrence Variable}
    (firstMem :
      first ∈ clauseRouteOccurrencesAt formula firstSite)
    (secondMem :
      second ∈ clauseRouteOccurrencesAt formula secondSite)
    (terminalEq :
      first.sourceTerminal formula =
        second.sourceTerminal formula) :
    first = second ∧ firstSite = secondSite := by
  rcases List.mem_map.mp firstMem with
    ⟨firstTagged, firstTaggedMem, firstEq⟩
  rcases List.mem_map.mp secondMem with
    ⟨secondTagged, secondTaggedMem, secondEq⟩
  subst first
  subst second
  have taggedEq :
      firstTagged = secondTagged :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      (List.mem_filter.mp firstTaggedMem).1
      (List.mem_filter.mp secondTaggedMem).1
      (congrArg
        (fun terminal => terminal.indexed.routeIndex)
        terminalEq)
  subst secondTagged
  have horizontalEq :
      firstSite.1 = secondSite.1 := by
    have firstClauseEq :=
      of_decide_eq_true
        (List.mem_filter.mp firstTaggedMem).2
    have secondClauseEq :=
      of_decide_eq_true
        (List.mem_filter.mp secondTaggedMem).2
    exact firstClauseEq.symm.trans secondClauseEq
  have translateEq :
      firstSite.2 = secondSite.2 := by
    exact congrArg SegmentTerminal.translate terminalEq
  have siteEq : firstSite = secondSite :=
    Prod.ext horizontalEq translateEq
  subst secondSite
  exact ⟨rfl, rfl⟩

/-- The source-terminal nodes appearing in the routed clause family are
duplicate-free. -/
theorem drawingRoutedClauseNodes_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((drawingClauseRouteSites formula).flatMap fun site =>
      (clauseRouteOccurrencesAt formula site).map fun occurrence =>
        (PlanarSATNode.carrier
          (.terminal
            (occurrence.sourceTerminal formula)) :
          PlanarSATNode Variable)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro site siteMem
    apply (clauseRouteOccurrencesAt_nodup formula site).map_on
    intro first firstMem second secondMem nodeEq
    exact
      (clauseRouteOccurrencesAt_eq_and_site_eq_of_sourceTerminal_eq
        formula firstMem secondMem
        (CarrierNode.terminal.inj
          (PlanarSATNode.carrier.inj nodeEq))).1
  · exact (drawingClauseRouteSites_nodup formula).imp
      fun {firstSite secondSite} siteNe => by
        change List.Disjoint
          ((clauseRouteOccurrencesAt formula firstSite).map
            fun occurrence =>
              (PlanarSATNode.carrier
                (.terminal
                  (occurrence.sourceTerminal formula)) :
                PlanarSATNode Variable))
          ((clauseRouteOccurrencesAt formula secondSite).map
            fun occurrence =>
              (PlanarSATNode.carrier
                (.terminal
                  (occurrence.sourceTerminal formula)) :
                PlanarSATNode Variable))
        rw [List.disjoint_left]
        intro node firstMem secondMem
        rcases List.mem_map.mp firstMem with
          ⟨first, firstOccurrenceMem, nodeEq⟩
        rcases List.mem_map.mp secondMem with
          ⟨second, secondOccurrenceMem, nodeEq'⟩
        have occurrenceData :=
          clauseRouteOccurrencesAt_eq_and_site_eq_of_sourceTerminal_eq
            formula firstOccurrenceMem secondOccurrenceMem
            (CarrierNode.terminal.inj
              (PlanarSATNode.carrier.inj
                (nodeEq.trans nodeEq'.symm)))
        exact siteNe occurrenceData.2

/-- Flattening routed clauses exposes exactly their source-terminal node
list. -/
theorem embeddedVariableOccurrences_drawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    embeddedVariableOccurrences
        (drawingRoutedClauseFormula formula) =
      (drawingClauseRouteSites formula).flatMap fun site =>
        (clauseRouteOccurrencesAt formula site).map fun occurrence =>
          (PlanarSATNode.carrier
            (.terminal
              (occurrence.sourceTerminal formula)) :
            PlanarSATNode Variable) := by
  simp [drawingRoutedClauseFormula, routedClauseAt,
    embeddedVariableOccurrences, List.flatMap_map,
    Function.comp_def]

/-- Each routed clause terminal occurs in exactly one source literal at
most. -/
theorem drawingRoutedClauseFormula_occurrencesAtMostOne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaOccurrencesAtMost 1
      (drawingRoutedClauseFormula formula) := by
  intro node
  rw [embeddedVariableOccurrences_drawingRoutedClauseFormula]
  exact
    (List.nodup_iff_count_le_one.mp
      (drawingRoutedClauseNodes_nodup formula)) node

/-! ### Active variable arms -/

/-- Collect all active routed-variable equality links. -/
def drawingRoutedVariableLinks
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EqualityLink (PlanarSATNode Variable)) :=
  (drawingVariableRouteSites formula).flatMap
    (routedVariableLinksAt formula)

/-- Flattening the per-site active equality families is the equality family
of the flattened link list. -/
theorem drawingRoutedVariableFormula_eq_equalityFamily
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    drawingRoutedVariableFormula formula =
      equalityFamily (drawingRoutedVariableLinks formula) := by
  unfold drawingRoutedVariableFormula
    drawingRoutedVariableLinks routedVariableFormulaAt
    equalityFamily
  rw [List.flatMap_assoc]

/-- A routed-variable occurrence is selected from the global neighboring
enumeration and reaches exactly its selecting variable site. -/
theorem variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ variableRouteOccurrencesAt formula site) :
    occurrence ∈ drawingCNFRouteOccurrences formula ∧
      occurrence.variableOccurrence = site := by
  simpa [variableRouteOccurrencesAt] using occurrenceMem

/-- Membership in the deduplicated active node list comes from a routed
occurrence reaching that site. -/
theorem mem_routedVariableNodes_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (node : PlanarSATNode Variable) :
    node ∈ routedVariableNodes formula site ↔
      ∃ occurrence ∈ variableRouteOccurrencesAt formula site,
        node = .carrier
          (.terminal (occurrence.targetTerminal formula)) := by
  simp [routedVariableNodes, eq_comm]

/-- Active target-terminal node lists at different variable sites are
disjoint. -/
theorem routedVariableNodes_disjoint_of_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstSite secondSite : VariableRouteSite Variable}
    (siteNe : firstSite ≠ secondSite) :
    List.Disjoint
      (routedVariableNodes formula firstSite)
      (routedVariableNodes formula secondSite) := by
  rw [List.disjoint_left]
  intro node firstMem secondMem
  rcases (mem_routedVariableNodes_iff
      formula firstSite node).mp firstMem with
    ⟨first, firstMem, nodeEq⟩
  rcases (mem_routedVariableNodes_iff
      formula secondSite node).mp secondMem with
    ⟨second, secondMem, nodeEq'⟩
  have firstData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula firstSite firstMem
  have secondData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula secondSite secondMem
  have occurrenceEq :=
    drawingCNFRouteOccurrences_targetTerminal_injective_on
      formula firstData.1 secondData.1
      (CarrierNode.terminal.inj
        (PlanarSATNode.carrier.inj
          (nodeEq.symm.trans nodeEq')))
  exact siteNe
    (firstData.2.symm.trans
      ((congrArg CNFRouteOccurrence.variableOccurrence
        occurrenceEq).trans secondData.2))

/-- The first endpoints of all active variable links are exactly the
deduplicated target nodes, truncated to the three Figure 8(a) arms. -/
theorem drawingRoutedVariableLinks_firsts
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingRoutedVariableLinks formula).map EqualityLink.first =
      (drawingVariableRouteSites formula).flatMap fun site =>
        (routedVariableNodes formula site).take 3 := by
  simp [drawingRoutedVariableLinks, routedVariableLinksAt,
    List.map_flatMap, List.map_map, Function.comp_def]

/-- Across the complete represented variable family, active target
terminals serve as first endpoints of at most one equality arm. -/
theorem drawingRoutedVariableLinks_firsts_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((drawingRoutedVariableLinks formula).map
      EqualityLink.first).Nodup := by
  rw [drawingRoutedVariableLinks_firsts,
    List.nodup_flatMap]
  constructor
  · intro site _
    exact (List.nodup_dedup _).take
  · exact (List.nodup_dedup _).imp
      fun {firstSite secondSite} siteNe => by
        change List.Disjoint
          ((routedVariableNodes formula firstSite).take 3)
          ((routedVariableNodes formula secondSite).take 3)
        rw [List.disjoint_left]
        intro node firstMem secondMem
        exact
          (routedVariableNodes_disjoint_of_ne formula siteNe)
            (List.mem_of_mem_take firstMem)
            (List.mem_of_mem_take secondMem)

/-- Each variable site has at most three active equality links. -/
theorem routedVariableLinksAt_length_le_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (routedVariableLinksAt formula site).length ≤ 3 := by
  simp [routedVariableLinksAt]

/-- The second endpoint of every active arm is its site's central atom. -/
theorem routedVariableLinksAt_second
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    link.second = .atom site := by
  rcases List.mem_map.mp linkMem with
    ⟨taggedNode, taggedNodeMem, linkEq⟩
  subst link
  rfl

/-- Central atoms are second endpoints of at most their three active
arms; carrier nodes are never second endpoints. -/
theorem drawingRoutedVariableLinks_seconds_count_le_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    ((drawingRoutedVariableLinks formula).map
      EqualityLink.second).count node ≤ 3 := by
  let sites := drawingVariableRouteSites formula
  have sitesNodup : sites.Nodup := List.nodup_dedup _
  change
    (((sites.flatMap
      (routedVariableLinksAt formula))).map
        EqualityLink.second).count node ≤ 3
  rw [List.map_flatMap]
  cases node with
  | carrier carrier =>
      have countZero :
          (sites.flatMap fun site =>
            (routedVariableLinksAt formula site).map
              EqualityLink.second).count
              (.carrier carrier) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro nodeMem
        rcases List.mem_flatMap.mp nodeMem with
          ⟨site, siteMem, nodeMem⟩
        rcases List.mem_map.mp nodeMem with
          ⟨link, linkMem, nodeEq⟩
        have secondEq :=
          routedVariableLinksAt_second formula site linkMem
        simp [secondEq] at nodeEq
      omega
  | atom targetSite =>
      revert sitesNodup
      induction sites with
      | nil =>
          intro _
          simp
      | cons site sites induction =>
          intro sitesNodup
          have nodupData := List.nodup_cons.mp sitesNodup
          rw [List.flatMap_cons, List.count_append]
          by_cases siteEq : site = targetSite
          · subst site
            have tailZero :
                (sites.flatMap fun site =>
                  (routedVariableLinksAt formula site).map
                    EqualityLink.second).count
                    (.atom targetSite) = 0 := by
              apply List.count_eq_zero_of_not_mem
              intro targetMem
              rcases List.mem_flatMap.mp targetMem with
                ⟨tailSite, tailSiteMem, targetMem⟩
              rcases List.mem_map.mp targetMem with
                ⟨link, linkMem, targetEq⟩
              have secondEq :=
                routedVariableLinksAt_second
                  formula tailSite linkMem
              exact nodupData.1
                (PlanarSATNode.atom.inj
                  (secondEq.symm.trans targetEq) ▸
                    tailSiteMem)
            rw [tailZero, Nat.add_zero]
            have headCountLe :
                ((routedVariableLinksAt formula targetSite).map
                  EqualityLink.second).count
                    (.atom targetSite) ≤
                  ((routedVariableLinksAt formula targetSite).map
                    EqualityLink.second).length :=
              List.count_le_length
            exact
              headCountLe.trans
                (by
                  rw [List.length_map]
                  exact routedVariableLinksAt_length_le_three
                    formula targetSite)
          · have headZero :
                ((routedVariableLinksAt formula site).map
                  EqualityLink.second).count
                    (.atom targetSite) = 0 := by
              apply List.count_eq_zero_of_not_mem
              intro targetMem
              rcases List.mem_map.mp targetMem with
                ⟨link, linkMem, targetEq⟩
              have secondEq :=
                routedVariableLinksAt_second formula site linkMem
              exact siteEq
                (PlanarSATNode.atom.inj
                  (secondEq.symm.trans targetEq))
            rw [headZero, Nat.zero_add]
            exact induction nodupData.2

/-- Counting equality-link endpoints splits into first- and second-endpoint
counts. -/
theorem equalityLinkEndpoints_count_eq_firsts_add_seconds
    {Variable : Type*} [DecidableEq Variable]
    (links : List (EqualityLink Variable))
    (node : Variable) :
    (equalityLinkEndpoints links).count node =
      (links.map EqualityLink.first).count node +
        (links.map EqualityLink.second).count node := by
  simpa [equalityLinkEndpoints, pairEndpoints,
    List.flatMap_map, Function.comp_def] using
    pairEndpoints_count
      (links.map fun link => (link.first, link.second)) node

/-- Active variable links have endpoint degree at most three. -/
theorem drawingRoutedVariableLinks_endpoint_count_le_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    (equalityLinkEndpoints
      (drawingRoutedVariableLinks formula)).count node ≤ 3 := by
  rw [equalityLinkEndpoints_count_eq_firsts_add_seconds]
  cases node with
  | carrier carrier =>
      have firstLe :
          ((drawingRoutedVariableLinks formula).map
            EqualityLink.first).count (.carrier carrier) ≤ 1 :=
        (List.nodup_iff_count_le_one.mp
          (drawingRoutedVariableLinks_firsts_nodup formula))
          (.carrier carrier)
      have secondZero :
          ((drawingRoutedVariableLinks formula).map
            EqualityLink.second).count (.carrier carrier) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro nodeMem
        rcases List.mem_map.mp nodeMem with
          ⟨link, linkMem, nodeEq⟩
        rcases List.mem_flatMap.mp linkMem with
          ⟨site, siteMem, linkMem⟩
        have secondEq :=
          routedVariableLinksAt_second formula site linkMem
        simp [secondEq] at nodeEq
      omega
  | atom site =>
      have firstZero :
          ((drawingRoutedVariableLinks formula).map
            EqualityLink.first).count (.atom site) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro nodeMem
        rcases List.mem_map.mp nodeMem with
          ⟨link, linkMem, nodeEq⟩
        rcases List.mem_flatMap.mp linkMem with
          ⟨linkSite, linkSiteMem, linkMem⟩
        rcases List.mem_map.mp linkMem with
          ⟨taggedNode, taggedNodeMem, linkEq⟩
        subst link
        have nodeMemInTake :
            taggedNode.1 ∈
              (routedVariableNodes formula linkSite).take 3 :=
          List.fst_mem_of_mem_zipIdx taggedNodeMem
        have nodeMem :
            taggedNode.1 ∈
              routedVariableNodes formula linkSite :=
          List.mem_of_mem_take nodeMemInTake
        rcases (mem_routedVariableNodes_iff
            formula linkSite taggedNode.1).mp nodeMem with
          ⟨occurrence, occurrenceMem, taggedNodeEq⟩
        have impossible :
            (PlanarSATNode.carrier
              (.terminal (occurrence.targetTerminal formula)) :
              PlanarSATNode Variable) =
                .atom site :=
          taggedNodeEq.symm.trans nodeEq
        cases impossible
      have secondLe :=
        drawingRoutedVariableLinks_seconds_count_le_three
          formula (.atom site)
      omega

/-- The complete active variable family uses every external node at most
six times. -/
theorem drawingRoutedVariableFormula_occurrencesAtMostSix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaOccurrencesAtMost 6
      (drawingRoutedVariableFormula formula) := by
  rw [drawingRoutedVariableFormula_eq_equalityFamily]
  apply equalityFamily_occurrencesAtMost
    (drawingRoutedVariableLinks formula) 3 6 rfl
  exact drawingRoutedVariableLinks_endpoint_count_le_three formula

/-- A carrier target participates in at most one active variable arm, hence
in at most two implication literals. -/
theorem drawingRoutedVariableFormula_carrier_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (carrier : CarrierNode) :
    (embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula)).count
        (.carrier carrier) ≤ 2 := by
  rw [drawingRoutedVariableFormula_eq_equalityFamily,
    equalityFamily_occurrence_count]
  rw [equalityLinkEndpoints_count_eq_firsts_add_seconds]
  have firstLe :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.first).count (.carrier carrier) ≤ 1 :=
    (List.nodup_iff_count_le_one.mp
      (drawingRoutedVariableLinks_firsts_nodup formula))
      (.carrier carrier)
  have secondZero :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.second).count (.carrier carrier) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro nodeMem
    rcases List.mem_map.mp nodeMem with
      ⟨link, linkMem, nodeEq⟩
    rcases List.mem_flatMap.mp linkMem with
      ⟨site, siteMem, linkMem⟩
    have secondEq :=
      routedVariableLinksAt_second formula site linkMem
    simp [secondEq] at nodeEq
  omega

/-! ## Separating route endpoints from local gadgets -/

/-- Crossover gadgets use boundary carrier nodes, never segment
terminals. -/
theorem drawingCarrierNodeCrossoverFormula_terminal_count_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal) :
    @List.count
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))
      instBEqOfDecidableEq
      (.inl (.terminal terminal))
      (embeddedVariableOccurrences
        (drawingCarrierNodeCrossoverFormula graph)) = 0 := by
  apply @List.count_eq_zero_of_not_mem
    (Sum CarrierNode (CrossingRecord × CrossoverInternal))
    instBEqOfDecidableEq (by infer_instance)
  rw [drawingCarrierNodeCrossoverFormula, crossoverFamily,
    embeddedVariableOccurrences_flatMap]
  intro terminalMem
  rcases List.mem_flatMap.mp terminalMem with
    ⟨crossing, _crossingMem, terminalMem⟩
  rw [scopedCrossoverInstance,
    embeddedVariableOccurrences_instantiateFormula] at terminalMem
  rcases List.mem_map.mp terminalMem with
    ⟨source, _sourceMem, sourceEq⟩
  cases source <;>
    simp [scopedCrossoverVariableMap,
      carrierNodeCrossingPorts] at sourceEq

/-- A segment terminal therefore receives only the route-wire part of the
core's six-occurrence budget. -/
theorem drawingRoutePlanarCoreFormula_terminal_count_le_six
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal) :
    @List.count
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))
      instBEqOfDecidableEq
      (.inl (.terminal terminal))
      (embeddedVariableOccurrences
        (drawingRoutePlanarCoreFormula graph)) ≤ 6 := by
  rw [drawingRoutePlanarCoreFormula,
    embeddedVariableOccurrences_append]
  rw [@List.count_append
    (Sum CarrierNode (CrossingRecord × CrossoverInternal))
    instBEqOfDecidableEq]
  rw [drawingCarrierNodeCrossoverFormula_terminal_count_eq_zero,
    Nat.zero_add]
  exact
    scopedDrawingRouteWireFormula_occurrencesAtMostSix
      graph (.inl (.terminal terminal))

/-- Routed source clauses contain carrier terminals, never central atoms. -/
theorem drawingRoutedClauseFormula_atom_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (embeddedVariableOccurrences
      (drawingRoutedClauseFormula formula)).count
        (.atom site) = 0 := by
  apply List.count_eq_zero_of_not_mem
  rw [embeddedVariableOccurrences_drawingRoutedClauseFormula]
  simp

/-- Routed source clauses contain terminals, never crossover boundaries. -/
theorem drawingRoutedClauseFormula_boundary_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (embeddedVariableOccurrences
      (drawingRoutedClauseFormula formula)).count
        (.carrier (.boundary boundary)) = 0 := by
  apply List.count_eq_zero_of_not_mem
  rw [embeddedVariableOccurrences_drawingRoutedClauseFormula]
  simp

/-- A non-source segment end cannot appear in a routed source clause. -/
theorem drawingRoutedClauseFormula_terminal_count_eq_zero_of_ne_start
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (terminal : SegmentTerminal)
    (endNe : terminal.endpoint ≠ .start) :
    (embeddedVariableOccurrences
      (drawingRoutedClauseFormula formula)).count
        (.carrier (.terminal terminal)) = 0 := by
  apply List.count_eq_zero_of_not_mem
  rw [embeddedVariableOccurrences_drawingRoutedClauseFormula]
  intro nodeMem
  rcases List.mem_flatMap.mp nodeMem with
    ⟨site, siteMem, nodeMem⟩
  rcases List.mem_map.mp nodeMem with
    ⟨occurrence, occurrenceMem, nodeEq⟩
  have terminalEq :
      occurrence.sourceTerminal formula = terminal :=
    CarrierNode.terminal.inj
      (PlanarSATNode.carrier.inj nodeEq)
  exact endNe
    (by
      have endpointEq :=
        congrArg SegmentTerminal.endpoint terminalEq
      simpa [CNFRouteOccurrence.sourceTerminal] using endpointEq.symm)

/-- Active variable arms contain target terminals and atoms, never
crossover boundaries. -/
theorem drawingRoutedVariableFormula_boundary_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula)).count
        (.carrier (.boundary boundary)) = 0 := by
  rw [drawingRoutedVariableFormula_eq_equalityFamily,
    equalityFamily_occurrence_count,
    equalityLinkEndpoints_count_eq_firsts_add_seconds]
  have firstZero :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.first).count
          (.carrier (.boundary boundary)) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro nodeMem
    rw [drawingRoutedVariableLinks_firsts] at nodeMem
    rcases List.mem_flatMap.mp nodeMem with
      ⟨site, siteMem, nodeMem⟩
    have nodeMem' :=
      List.mem_of_mem_take nodeMem
    rcases (mem_routedVariableNodes_iff
        formula site (.carrier (.boundary boundary))).mp nodeMem' with
      ⟨occurrence, occurrenceMem, nodeEq⟩
    cases PlanarSATNode.carrier.inj nodeEq
  have secondZero :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.second).count
          (.carrier (.boundary boundary)) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro nodeMem
    rcases List.mem_map.mp nodeMem with
      ⟨link, linkMem, nodeEq⟩
    rcases List.mem_flatMap.mp linkMem with
      ⟨site, siteMem, linkMem⟩
    have secondEq :=
      routedVariableLinksAt_second formula site linkMem
    simp [secondEq] at nodeEq
  omega

/-- A non-target segment end cannot appear in an active variable arm. -/
theorem drawingRoutedVariableFormula_terminal_count_eq_zero_of_ne_finish
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (terminal : SegmentTerminal)
    (endNe : terminal.endpoint ≠ .finish) :
    (embeddedVariableOccurrences
      (drawingRoutedVariableFormula formula)).count
        (.carrier (.terminal terminal)) = 0 := by
  rw [drawingRoutedVariableFormula_eq_equalityFamily,
    equalityFamily_occurrence_count,
    equalityLinkEndpoints_count_eq_firsts_add_seconds]
  have firstZero :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.first).count
          (.carrier (.terminal terminal)) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro nodeMem
    rw [drawingRoutedVariableLinks_firsts] at nodeMem
    rcases List.mem_flatMap.mp nodeMem with
      ⟨site, siteMem, nodeMem⟩
    have nodeMem' :=
      List.mem_of_mem_take nodeMem
    rcases (mem_routedVariableNodes_iff
        formula site (.carrier (.terminal terminal))).mp nodeMem' with
      ⟨occurrence, occurrenceMem, nodeEq⟩
    have terminalEq :
        occurrence.targetTerminal formula = terminal :=
      CarrierNode.terminal.inj
        (PlanarSATNode.carrier.inj nodeEq.symm)
    exact endNe
      (by
        have endpointEq :=
          congrArg SegmentTerminal.endpoint terminalEq
        simpa [CNFRouteOccurrence.targetTerminal] using endpointEq.symm)
  have secondZero :
      ((drawingRoutedVariableLinks formula).map
        EqualityLink.second).count
          (.carrier (.terminal terminal)) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro nodeMem
    rcases List.mem_map.mp nodeMem with
      ⟨link, linkMem, nodeEq⟩
    rcases List.mem_flatMap.mp linkMem with
      ⟨site, siteMem, linkMem⟩
    have secondEq :=
      routedVariableLinksAt_second formula site linkMem
    simp [secondEq] at nodeEq
  omega

/-! ## The combined finite planar SAT formula -/

/-- The route-core renaming into the combined SAT variable type is
injective. -/
theorem planarSATCoreVariableMap_injective
    {Variable : Type*} :
    Function.Injective
      (@planarSATCoreVariableMap Variable) := by
  intro first second equal
  cases first <;> cases second <;>
    simp [planarSATCoreVariableMap] at equal ⊢
  all_goals exact equal

/-- A renamed route-core variable has exactly its original occurrence
count. -/
theorem scopedDrawingPlanarSATCore_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node :
      Sum CarrierNode (CrossingRecord × CrossoverInternal)) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (planarSATCoreVariableMap node)
      (embeddedVariableOccurrences
        (scopedDrawingPlanarSATCore formula)) =
      @List.count
        (Sum CarrierNode (CrossingRecord × CrossoverInternal))
        instBEqOfDecidableEq node
        (embeddedVariableOccurrences
          (drawingRoutePlanarCoreFormula
            (PeriodicCNF.incidenceGraph formula))) := by
  unfold scopedDrawingPlanarSATCore
  simp only [EmbeddedClause.rename]
  rw [embeddedVariableOccurrences_map]
  exact
    @List.count_map_of_injective
      (Sum CarrierNode (CrossingRecord × CrossoverInternal))
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq (by infer_instance)
      instBEqOfDecidableEq (by infer_instance)
      (embeddedVariableOccurrences
        (drawingRoutePlanarCoreFormula
          (PeriodicCNF.incidenceGraph formula)))
      planarSATCoreVariableMap
      planarSATCoreVariableMap_injective node

/-- Specialized count preservation for an external carrier node. -/
theorem scopedDrawingPlanarSATCore_carrier_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (carrier : CarrierNode) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inl (.carrier carrier))
      (embeddedVariableOccurrences
        (scopedDrawingPlanarSATCore formula)) =
      @List.count
        (Sum CarrierNode (CrossingRecord × CrossoverInternal))
        instBEqOfDecidableEq (.inl carrier)
        (embeddedVariableOccurrences
          (drawingRoutePlanarCoreFormula
            (PeriodicCNF.incidenceGraph formula))) := by
  simpa [planarSATCoreVariableMap] using
    scopedDrawingPlanarSATCore_count formula (.inl carrier)

/-- Specialized count preservation for a crossover-internal node. -/
theorem scopedDrawingPlanarSATCore_internal_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inr internal)
      (embeddedVariableOccurrences
        (scopedDrawingPlanarSATCore formula)) =
      @List.count
        (Sum CarrierNode (CrossingRecord × CrossoverInternal))
        instBEqOfDecidableEq (.inr internal)
        (embeddedVariableOccurrences
          (drawingRoutePlanarCoreFormula
            (PeriodicCNF.incidenceGraph formula))) := by
  simpa [planarSATCoreVariableMap] using
    scopedDrawingPlanarSATCore_count formula (.inr internal)

/-- Central atoms are outside the route-core renaming's image. -/
theorem scopedDrawingPlanarSATCore_atom_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inl (.atom site))
      (embeddedVariableOccurrences
        (scopedDrawingPlanarSATCore formula)) = 0 := by
  apply @List.count_eq_zero_of_not_mem
    (PlanarSATVariable Variable)
    instBEqOfDecidableEq (by infer_instance)
  unfold scopedDrawingPlanarSATCore
  simp only [EmbeddedClause.rename]
  rw [embeddedVariableOccurrences_map]
  simp [planarSATCoreVariableMap]

/-- Renaming an external node into the combined SAT type preserves its
occurrence count in the routed clause family. -/
theorem scopedDrawingRoutedClauseFormula_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inl node)
      (embeddedVariableOccurrences
        (scopedDrawingRoutedClauseFormula formula)) =
      @List.count
        (PlanarSATNode Variable)
        instBEqOfDecidableEq node
        (embeddedVariableOccurrences
          (drawingRoutedClauseFormula formula)) := by
  unfold scopedDrawingRoutedClauseFormula
  simp only [EmbeddedClause.rename]
  rw [embeddedVariableOccurrences_map]
  exact
    @List.count_map_of_injective
      (PlanarSATNode Variable) (PlanarSATVariable Variable)
      instBEqOfDecidableEq (by infer_instance)
      instBEqOfDecidableEq (by infer_instance)
      (embeddedVariableOccurrences
        (drawingRoutedClauseFormula formula))
      planarSATExternalVariableMap
      (fun first second equal => Sum.inl.inj equal) node

/-- The same count preservation holds for routed variable gadgets. -/
theorem scopedDrawingRoutedVariableFormula_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inl node)
      (embeddedVariableOccurrences
        (scopedDrawingRoutedVariableFormula formula)) =
      @List.count
        (PlanarSATNode Variable)
        instBEqOfDecidableEq node
        (embeddedVariableOccurrences
          (drawingRoutedVariableFormula formula)) := by
  unfold scopedDrawingRoutedVariableFormula
  simp only [EmbeddedClause.rename]
  rw [embeddedVariableOccurrences_map]
  exact
    @List.count_map_of_injective
      (PlanarSATNode Variable) (PlanarSATVariable Variable)
      instBEqOfDecidableEq (by infer_instance)
      instBEqOfDecidableEq (by infer_instance)
      (embeddedVariableOccurrences
        (drawingRoutedVariableFormula formula))
      planarSATExternalVariableMap
      (fun first second equal => Sum.inl.inj equal) node

/-- External clause and variable families contain no crossover-internal
summand. -/
theorem scopedDrawingRoutedExternal_internal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    @List.count
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq
      (.inr internal)
      (embeddedVariableOccurrences
        (scopedDrawingRoutedClauseFormula formula)) = 0 ∧
      @List.count
        (PlanarSATVariable Variable)
        instBEqOfDecidableEq
        (.inr internal)
        (embeddedVariableOccurrences
          (scopedDrawingRoutedVariableFormula formula)) = 0 := by
  constructor <;>
    apply @List.count_eq_zero_of_not_mem
      (PlanarSATVariable Variable)
      instBEqOfDecidableEq (by infer_instance)
  · unfold scopedDrawingRoutedClauseFormula
    simp only [EmbeddedClause.rename]
    rw [embeddedVariableOccurrences_map]
    simp [planarSATExternalVariableMap]
  · unfold scopedDrawingRoutedVariableFormula
    simp only [EmbeddedClause.rename]
    rw [embeddedVariableOccurrences_map]
    simp [planarSATExternalVariableMap]

/-- Under the source occurrence-three premise, the complete finite routed
planar SAT formula fits the paper's degree-eight budget.  (The premise is
used upstream to ensure there are at most three active variable arms.) -/
theorem drawingPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (_occurrences : formula.OccurrencesAtMost 3) :
    FormulaOccurrencesAtMost 8
      (drawingPlanarSATFormula formula) := by
  intro atom
  rw [drawingPlanarSATFormula,
    embeddedVariableOccurrences_append,
    embeddedVariableOccurrences_append]
  rw [@List.count_append
      (PlanarSATVariable Variable) instBEqOfDecidableEq,
    @List.count_append
      (PlanarSATVariable Variable) instBEqOfDecidableEq]
  cases atom with
  | inr internal =>
      have externalZero :=
        scopedDrawingRoutedExternal_internal_count_eq_zero
          formula internal
      rw [externalZero.1, externalZero.2]
      simp only [Nat.add_zero]
      rw [scopedDrawingPlanarSATCore_internal_count
        formula internal]
      exact
        drawingRoutePlanarCoreFormula_occurrencesAtMostEight
          (PeriodicCNF.incidenceGraph formula) (.inr internal)
  | inl node =>
      cases node with
      | atom site =>
          rw [scopedDrawingPlanarSATCore_atom_count_eq_zero
              formula site,
            scopedDrawingRoutedClauseFormula_count
              formula (.atom site),
            drawingRoutedClauseFormula_atom_count_eq_zero
              formula site,
            scopedDrawingRoutedVariableFormula_count
              formula (.atom site)]
          simp only [Nat.zero_add]
          exact
            (drawingRoutedVariableFormula_occurrencesAtMostSix
              formula (.atom site)).trans (by omega)
      | carrier carrier =>
          cases carrier with
          | boundary boundary =>
              rw [scopedDrawingPlanarSATCore_carrier_count
                    formula (.boundary boundary),
                scopedDrawingRoutedClauseFormula_count
                    formula (.carrier (.boundary boundary)),
                drawingRoutedClauseFormula_boundary_count_eq_zero
                    formula boundary,
                scopedDrawingRoutedVariableFormula_count
                    formula (.carrier (.boundary boundary)),
                drawingRoutedVariableFormula_boundary_count_eq_zero
                    formula boundary]
              simp only [Nat.add_zero]
              exact
                drawingRoutePlanarCoreFormula_occurrencesAtMostEight
                  (PeriodicCNF.incidenceGraph formula)
                  (.inl (.boundary boundary))
          | terminal terminal =>
              cases terminal with
              | mk indexed translate endpoint =>
                  cases endpoint with
                  | start =>
                      rw [scopedDrawingPlanarSATCore_carrier_count
                            formula
                            (.terminal
                              ⟨indexed, translate, .start⟩),
                        scopedDrawingRoutedClauseFormula_count
                            formula
                            (.carrier (.terminal
                              ⟨indexed, translate, .start⟩)),
                        scopedDrawingRoutedVariableFormula_count
                            formula
                            (.carrier (.terminal
                              ⟨indexed, translate, .start⟩)),
                        drawingRoutedVariableFormula_terminal_count_eq_zero_of_ne_finish
                            formula
                            ⟨indexed, translate, .start⟩
                            (by simp)]
                      simp only [Nat.add_zero]
                      have coreLe :=
                        drawingRoutePlanarCoreFormula_terminal_count_le_six
                          (PeriodicCNF.incidenceGraph formula)
                          ⟨indexed, translate, .start⟩
                      have clauseLe :=
                        drawingRoutedClauseFormula_occurrencesAtMostOne
                          formula
                          (.carrier (.terminal
                            ⟨indexed, translate, .start⟩))
                      omega
                  | finish =>
                      rw [scopedDrawingPlanarSATCore_carrier_count
                            formula
                            (.terminal
                              ⟨indexed, translate, .finish⟩),
                        scopedDrawingRoutedClauseFormula_count
                            formula
                            (.carrier (.terminal
                              ⟨indexed, translate, .finish⟩)),
                        drawingRoutedClauseFormula_terminal_count_eq_zero_of_ne_start
                            formula
                            ⟨indexed, translate, .finish⟩
                            (by simp),
                        scopedDrawingRoutedVariableFormula_count
                            formula
                            (.carrier (.terminal
                              ⟨indexed, translate, .finish⟩))]
                      have coreLe :=
                        drawingRoutePlanarCoreFormula_terminal_count_le_six
                          (PeriodicCNF.incidenceGraph formula)
                          ⟨indexed, translate, .finish⟩
                      have variableLe :=
                        drawingRoutedVariableFormula_carrier_count_le_two
                          formula (.terminal
                            ⟨indexed, translate, .finish⟩)
                      omega

end PeriodicOrthocrossing
end LeanTrominoes
