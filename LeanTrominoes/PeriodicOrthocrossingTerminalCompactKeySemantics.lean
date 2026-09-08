/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingActiveTerminalCompactKeyCompiler
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Exact physical terminal identities selected by compact atom keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys

/-- Physical endpoints in the same order used by the coordinate compiler. -/
def nodes (descriptors : List RouteDescriptor) : List CarrierNode :=
  (routeDescriptorNeighborOccurrences descriptors).flatMap occurrenceCarrierTerminalNodes

private theorem node_is_terminal (descriptors : List RouteDescriptor) (node : CarrierNode)
    (member : node ∈ nodes descriptors) : ∃ terminal, node = .terminal terminal := by
  obtain ⟨occurrence, _member, equal | equal⟩ :=
    (mem_flatMap_occurrenceCarrierTerminalNodes_iff _ _).mp member
  · exact ⟨_, equal⟩
  · exact ⟨_, equal⟩

private theorem node_mem_retained (period : Nat) (descriptors : List RouteDescriptor)
    (node : CarrierNode) (member : node ∈ nodes descriptors) :
    node ∈ routeDescriptorRetainedCarrierNodesAtPeriod period descriptors := by
  exact List.mem_append_left _ member

/-- Compact terminal keys are injective on the physical endpoint enumeration. -/
theorem nodeWord_injective_on (descriptors : List RouteDescriptor)
    (first : CarrierNode) (firstMember : first ∈ nodes descriptors)
    (second : CarrierNode) (secondMember : second ∈ nodes descriptors)
    (equal : nodeWord first = nodeWord second) : first = second := by
  obtain ⟨firstTerminal, rfl⟩ := node_is_terminal descriptors first firstMember
  obtain ⟨secondTerminal, rfl⟩ := node_is_terminal descriptors second secondMember
  have keyEq : (CarrierNodeSourceKeys.pair (.terminal firstTerminal)).1 =
      (CarrierNodeSourceKeys.pair (.terminal secondTerminal)).1 := by
    apply CarrierKeyWords.word_injective
    simpa [nodeWord] using equal
  apply sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
    0 descriptors _ (node_mem_retained 0 descriptors _ firstMember)
    _ (node_mem_retained 0 descriptors _ secondMember)
  simpa [CarrierNodeSourceKeys.pair] using congrArg (fun key => (key, key)) keyEq

/-- A periodic terminal refers to its translation-zero physical representative. -/
def queryNode {Variable : Type*} (query : WrappedPeriodicPlanarSATVariable Variable) :
    Option CarrierNode :=
  match query.original with
  | .terminal indexed endpoint => some (.terminal ⟨indexed, (0, 0), endpoint⟩)
  | _ => none

/-- Lift any physical terminal datum to its periodic atom, using zero on other families. -/
def queryDatum {Variable : Type*} (datum : CarrierNode → Nat)
    (query : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  ((queryNode query).map datum).getD 0

/-- Periodic and physical words agree exactly at a terminal representative. -/
theorem queryNode_word_eq {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (node : CarrierNode)
    (equal : queryNode query = some node) :
    RetainedCompactAtomWords.word sourceWord query = nodeWord node := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryNode, reduceCtorEq] at equal
  rename_i indexed endpoint
  cases Option.some.inj equal
  rfl

/-- Other atom families cannot match the terminal constructor prefix. -/
theorem queryNode_none_word_ne {Variable : Type*} (sourceWord : Variable → List Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable) (node : CarrierNode)
    (equal : queryNode query = none) :
    RetainedCompactAtomWords.word sourceWord query ≠ nodeWord node := by
  rcases query with ⟨query⟩
  cases query <;> simp [queryNode] at equal
  all_goals simp [RetainedCompactAtomWords.word, nodeWord]

/-- Valid periodic terminals always have a candidate in the physical dictionary. -/
theorem queryNode_mem {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (query : WrappedPeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula query.original)
    (node : CarrierNode) (equal : queryNode query = some node) :
    node ∈ nodes (PeriodicCNF.numericRouteDescriptors formula) := by
  rcases query with ⟨query⟩
  cases query <;> simp only [queryNode, reduceCtorEq] at equal
  rename_i indexed endpoint
  cases Option.some.inj equal
  have retainedMember := RetainedCompactAtomWords.zeroCarrierNode_mem_of_valid
    formula (.terminal indexed endpoint) valid
  rw [← PeriodicCNF.routeDescriptorRetainedCarrierNodes_numeric_eq formula] at retainedMember
  have provenance := terminal_mem_routeDescriptorRetainedCarrierNodesAtPeriod
    (drawingGridSize formula.incidenceGraph) (PeriodicCNF.numericRouteDescriptors formula)
    ⟨indexed, (0, 0), endpoint⟩ retainedMember
  obtain ⟨occurrence, occurrenceMember, startEqual | finishEqual⟩ := provenance
  · exact (mem_flatMap_occurrenceCarrierTerminalNodes_iff _ _).mpr
      ⟨occurrence, occurrenceMember, Or.inl (congrArg CarrierNode.terminal startEqual)⟩
  · exact (mem_flatMap_occurrenceCarrierTerminalNodes_iff _ _).mpr
      ⟨occurrence, occurrenceMember, Or.inr (congrArg CarrierNode.terminal finishEqual)⟩

end LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys
