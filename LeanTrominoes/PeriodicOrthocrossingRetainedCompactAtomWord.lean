/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorRetainedCarrierNodes
import LeanTrominoes.PeriodicCNFPlanarVariableNormalizationDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomWord
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeSourceKeyInjectivity

/-! # Compact words for represented retained routed atoms -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RetainedCompactAtomWords

open CarrierNodeSourceKeys
open PeriodicCNFStripReduction.DirectSourceFinalAtomWords

/-- Translation-zero physical representative of a periodic carrier node. -/
def zeroCarrierNode : PeriodicCarrierNode → CarrierNode
  | .terminal indexed endpoint =>
      .terminal ⟨indexed, (0, 0), endpoint⟩
  | .boundary boundary => .boundary boundary

theorem zeroCarrierNode_injective : Function.Injective zeroCarrierNode := by
  intro first second equal
  cases first <;> cases second <;>
    simp [zeroCarrierNode] at equal ⊢
  all_goals exact equal

/-- Compact two-key identity of a periodic terminal or boundary prototype. -/
def carrierPair (node : PeriodicCarrierNode) : SourceKeyPair :=
  CarrierNodeSourceKeys.pair (zeroCarrierNode node)

/-- A fixed boundary side supplies a compact identity for one canonical
crossing site. -/
def crossingPair (crossing : CrossingRecord) : SourceKeyPair :=
  carrierPair (.boundary ⟨crossing, .left⟩)

/-- Constructor-tagged compact word. Terminals need only their tagged first
source key; boundaries retain both source keys, while source and crossover
branches keep their established self-delimiting payloads. -/
def word
    {Variable : Type*}
    (sourceWord : Variable → List Bool)
    (atom : WrappedPeriodicPlanarSATVariable Variable) : List Bool :=
  match atom.original with
  | .terminal indexed endpoint =>
      false :: false :: CarrierKeyWords.word
        (carrierPair (.terminal indexed endpoint)).1
  | .boundary boundary =>
      false :: true :: CarrierNodeSourceKeys.word
        (carrierPair (.boundary boundary))
  | .atom sourceAtom => true :: false :: sourceWord sourceAtom
  | .crossoverInternal (crossing, internal) =>
      true :: true ::
        CarrierNodeSourceKeys.word (crossingPair crossing) ++
          crossoverInternalWord internal

/-- A valid periodic carrier prototype's translation-zero representative is
present in the retained physical carrier-node stream. -/
theorem zeroCarrierNode_mem_of_valid
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PeriodicCarrierNode)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula
      (periodicCarrierNodeToPlanarSATVariable node)) :
    zeroCarrierNode node ∈ retainedDrawingCarrierNodes
      formula.incidenceGraph := by
  have lifted := retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
    formula (periodicCarrierNodeToPlanarSATVariable node) valid
  cases node <;>
    simpa [periodicCarrierNodeToPlanarSATVariable,
      periodicPlanarSATVariableZeroLift, zeroCarrierNode,
      RetainedDrawingPlanarSATVariableValid] using lifted

/-- Compact carrier pairs separate all valid periodic carrier prototypes. -/
theorem carrierPair_injective_of_valid
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ∀ first : PeriodicCarrierNode,
      RetainedDrawingPeriodicPlanarSATVariableValid formula
          (periodicCarrierNodeToPlanarSATVariable first) →
      ∀ second : PeriodicCarrierNode,
        RetainedDrawingPeriodicPlanarSATVariableValid formula
            (periodicCarrierNodeToPlanarSATVariable second) →
        carrierPair first = carrierPair second → first = second := by
  intro first firstValid second secondValid pairEq
  have firstMember := zeroCarrierNode_mem_of_valid
    formula first firstValid
  have secondMember := zeroCarrierNode_mem_of_valid
    formula second secondValid
  have firstDescriptorMember :
      zeroCarrierNode first ∈ routeDescriptorRetainedCarrierNodesAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (PeriodicCNF.numericRouteDescriptors formula) := by
    rw [PeriodicCNF.routeDescriptorRetainedCarrierNodes_numeric_eq formula]
    exact firstMember
  have secondDescriptorMember :
      zeroCarrierNode second ∈ routeDescriptorRetainedCarrierNodesAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (PeriodicCNF.numericRouteDescriptors formula) := by
    rw [PeriodicCNF.routeDescriptorRetainedCarrierNodes_numeric_eq formula]
    exact secondMember
  apply zeroCarrierNode_injective
  exact sourceKeyPair_injectiveOn_routeDescriptorRetainedCarrierNodesAtPeriod
    (drawingGridSize formula.incidenceGraph)
    (PeriodicCNF.numericRouteDescriptors formula)
    (zeroCarrierNode first) firstDescriptorMember
    (zeroCarrierNode second) secondDescriptorMember pairEq

/-- A canonical crossing's fixed left boundary is valid whenever the
crossing-internal family itself is valid. -/
theorem crossingLeft_valid_of_internal_valid
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (internal : PlanarThreeSAT.CrossoverInternal)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula
      (.crossoverInternal (crossing, internal))) :
    RetainedDrawingPeriodicPlanarSATVariableValid formula
      (.boundary ⟨crossing, .left⟩) := by
  simpa [RetainedDrawingPeriodicPlanarSATVariableValid,
    drawingCrossingBoundaries] using valid

/-- The compact word separates all geometrically valid retained periodic
atoms. This is the exact domain needed by the final occurrence square. -/
theorem word_injective_on_valid
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (sourceWordInjective : Function.Injective sourceWord) :
    ∀ first : WrappedPeriodicPlanarSATVariable Variable,
      RetainedDrawingPeriodicPlanarSATVariableValid formula first.original →
      ∀ second : WrappedPeriodicPlanarSATVariable Variable,
        RetainedDrawingPeriodicPlanarSATVariableValid
            formula second.original →
        word sourceWord first = word sourceWord second → first = second := by
  rintro ⟨first⟩ firstValid ⟨second⟩ secondValid wordsEq
  cases first with
  | terminal firstIndexed firstEndpoint =>
      cases second with
      | terminal secondIndexed secondEndpoint =>
          have keyEq := CarrierKeyWords.word_injective
            (List.cons.inj (List.cons.inj wordsEq).2).2
          have pairEq :
              carrierPair (.terminal firstIndexed firstEndpoint) =
                carrierPair (.terminal secondIndexed secondEndpoint) := by
            apply Prod.ext <;>
              simpa [carrierPair, zeroCarrierNode,
                CarrierNodeSourceKeys.pair] using keyEq
          have carrierEq := carrierPair_injective_of_valid formula
            (.terminal firstIndexed firstEndpoint) firstValid
            (.terminal secondIndexed secondEndpoint) secondValid pairEq
          cases carrierEq
          rfl
      | boundary secondBoundary => simp [word] at wordsEq
      | atom secondAtom => simp [word] at wordsEq
      | crossoverInternal secondInternal => simp [word] at wordsEq
  | boundary firstBoundary =>
      cases second with
      | terminal secondIndexed secondEndpoint => simp [word] at wordsEq
      | boundary secondBoundary =>
          have pairEq := CarrierNodeSourceKeys.word_injective
            (List.cons.inj (List.cons.inj wordsEq).2).2
          have carrierEq := carrierPair_injective_of_valid formula
            (.boundary firstBoundary) firstValid
            (.boundary secondBoundary) secondValid pairEq
          cases carrierEq
          rfl
      | atom secondAtom => simp [word] at wordsEq
      | crossoverInternal secondInternal => simp [word] at wordsEq
  | atom firstAtom =>
      cases second with
      | terminal secondIndexed secondEndpoint => simp [word] at wordsEq
      | boundary secondBoundary => simp [word] at wordsEq
      | atom secondAtom =>
          have atomEq : firstAtom = secondAtom :=
            sourceWordInjective (by simpa [word] using wordsEq)
          cases atomEq
          rfl
      | crossoverInternal secondInternal => simp [word] at wordsEq
  | crossoverInternal firstInternal =>
      rcases firstInternal with ⟨firstCrossing, firstRole⟩
      cases second with
      | terminal secondIndexed secondEndpoint => simp [word] at wordsEq
      | boundary secondBoundary => simp [word] at wordsEq
      | atom secondAtom => simp [word] at wordsEq
      | crossoverInternal secondInternal =>
          rcases secondInternal with ⟨secondCrossing, secondRole⟩
          have payloadEq :
              CarrierNodeSourceKeys.word (crossingPair firstCrossing) ++
                  crossoverInternalWord firstRole =
                CarrierNodeSourceKeys.word (crossingPair secondCrossing) ++
                  crossoverInternalWord secondRole := by
            simpa [word] using wordsEq
          have decodedEq :
              (crossingPair firstCrossing,
                  crossoverInternalWord firstRole) =
                (crossingPair secondCrossing,
                  crossoverInternalWord secondRole) := by
            apply Option.some.inj
            simpa using congrArg CarrierNodeSourceKeys.decode payloadEq
          have pairEq := congrArg Prod.fst decodedEq
          have roleWordEq := congrArg Prod.snd decodedEq
          have firstLeftValid := crossingLeft_valid_of_internal_valid
            formula firstCrossing firstRole firstValid
          have secondLeftValid := crossingLeft_valid_of_internal_valid
            formula secondCrossing secondRole secondValid
          have boundaryEq := carrierPair_injective_of_valid formula
            (.boundary ⟨firstCrossing, .left⟩) firstLeftValid
            (.boundary ⟨secondCrossing, .left⟩) secondLeftValid pairEq
          have crossingEq : firstCrossing = secondCrossing := by
            exact congrArg
              (fun node : PeriodicCarrierNode =>
                match node with
                | .boundary boundary => boundary.crossing
                | .terminal _ _ => firstCrossing)
              boundaryEq
          have roleEq : firstRole = secondRole := by
            have appendedEq :
                crossoverInternalWord firstRole ++ [] =
                  crossoverInternalWord secondRole ++ [] := by
              simpa using roleWordEq
            have decodedRoleEq := congrArg decodeCrossoverInternal appendedEq
            have decodedSomeEq :
                some (firstRole, ([] : List Bool)) =
                  some (secondRole, ([] : List Bool)) := by
              simpa only [decodeCrossoverInternal_word_append] using decodedRoleEq
            exact congrArg Prod.fst (Option.some.inj decodedSomeEq)
          cases crossingEq
          cases roleEq
          rfl

end RetainedCompactAtomWords
end PeriodicOrthocrossing
end LeanTrominoes
