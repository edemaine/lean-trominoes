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

end PeriodicOrthocrossing
end LeanTrominoes
