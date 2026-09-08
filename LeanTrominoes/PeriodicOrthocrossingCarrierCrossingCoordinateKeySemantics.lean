/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingCoordinateKeyCompiler
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Crossing-origin dictionary membership and exact boundary identities -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingCoordinateKeys

/-- Global datum ranking preserves exactly the retained physical node set. -/
theorem mem_nodes_iff (descriptors : List RouteDescriptor) (node : CarrierNode) :
    node ∈ CarrierCrossingMacroOrigin.nodes descriptors ↔
      node ∈ routeDescriptorRetainedCarrierNodesAtPeriod
        (routeDescriptorStreamGridSize descriptors) descriptors := by
  let period := routeDescriptorStreamGridSize descriptors
  let datums := (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  change node ∈ (CarrierRankGlobal.enumeration datums).map
    (fun entry => entry.1.identity.node) ↔ _
  constructor
  · intro member
    obtain ⟨entry, entryMember, nodeEq⟩ := List.mem_map.mp member
    have datumMember := List.fst_mem_of_mem_zipIdx
      ((CarrierRankGlobal.mem_enumeration_iff datums entry).mp entryMember)
    have rawMember := List.mem_dedup.mp datumMember
    obtain ⟨original, originalMember, datumEq⟩ := List.mem_map.mp rawMember
    have originalEq : original = node := by
      calc
        original = (carrierNodeRankDatumAtPeriod period original).identity.node := by
          simp [carrierNodeRankDatumAtPeriod, CarrierNodeCode.node_code]
        _ = entry.1.identity.node := congrArg (fun datum => datum.identity.node) datumEq
        _ = node := nodeEq
    exact originalEq ▸ originalMember
  · intro member
    let datum := carrierNodeRankDatumAtPeriod period node
    have datumMember : datum ∈ datums :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨node, member, rfl⟩)
    obtain ⟨index, indexLt, indexEq⟩ := List.mem_iff_getElem.mp datumMember
    apply List.mem_map.mpr
    refine ⟨(datum, index), ?_, ?_⟩
    · apply (CarrierRankGlobal.mem_enumeration_iff datums _).mpr
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨indexLt, indexEq⟩
    · simp [datum, carrierNodeRankDatumAtPeriod, CarrierNodeCode.node_code]

/-- The full source-pair identity separates every physical dictionary node. -/
theorem nodeWord_injective_on (descriptors : List RouteDescriptor)
    (first : CarrierNode) (firstMember : first ∈ CarrierCrossingMacroOrigin.nodes descriptors)
    (second : CarrierNode) (secondMember : second ∈ CarrierCrossingMacroOrigin.nodes descriptors)
    (equal : nodeWord first = nodeWord second) : first = second := by
  apply sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
    (routeDescriptorStreamGridSize descriptors) descriptors
    first ((mem_nodes_iff descriptors first).mp firstMember)
    second ((mem_nodes_iff descriptors second).mp secondMember)
  apply CarrierNodeSourceKeys.word_injective
  simpa [nodeWord] using equal

/-- A boundary query names the same physical crossing boundary. -/
def queryNode {Variable : Type*} (query : WrappedPeriodicPlanarSATVariable Variable) :
    Option CarrierNode :=
  match query.original with
  | .boundary boundary => some (.boundary boundary)
  | _ => none

def queryDatum {Variable : Type*} (datum : CarrierNode → Nat)
    (query : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  ((queryNode query).map datum).getD 0

theorem queryNode_word_eq {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (node : CarrierNode)
    (equal : queryNode query = some node) :
    RetainedCompactAtomWords.word sourceWord query = nodeWord node := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryNode, reduceCtorEq] at equal
  rename_i boundary
  cases Option.some.inj equal
  rfl

theorem queryNode_none_word_ne {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (node : CarrierNode)
    (equal : queryNode query = none) :
    RetainedCompactAtomWords.word sourceWord query ≠ nodeWord node := by
  rcases query with ⟨query⟩
  cases query <;> simp [queryNode] at equal
  all_goals simp [RetainedCompactAtomWords.word, nodeWord]

/-- Every valid boundary query is present in the globally ranked physical dictionary. -/
theorem queryNode_mem {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula query.original)
    (node : CarrierNode) (equal : queryNode query = some node) :
    node ∈ CarrierCrossingMacroOrigin.nodes (PeriodicCNF.numericRouteDescriptors formula) := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryNode, reduceCtorEq] at equal
  rename_i boundary
  cases Option.some.inj equal
  rw [mem_nodes_iff,
    PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors formula nonempty,
    PeriodicCNF.routeDescriptorRetainedCarrierNodes_numeric_eq formula]
  exact RetainedCompactAtomWords.zeroCarrierNode_mem_of_valid formula (.boundary boundary) valid

end LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingCoordinateKeys
