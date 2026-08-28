/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Semantics of normalized compact carrier source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeNormalizedSourceKeys

/-- Reconstructing a rank datum's reversible node recovers the same normalized
source pair. -/
@[simp] theorem datumPairAtPeriod_carrierNodeRankDatumAtPeriod
    (period : Nat) (node : CarrierNode) :
    datumPairAtPeriod period (carrierNodeRankDatumAtPeriod period node) =
      pairAtPeriod period node := by
  simp [datumPairAtPeriod, carrierNodeRankDatumAtPeriod]

/-- At a graph's drawing period, graph-free normalization is exactly the
translation-zero representative of semantic carrier normalization. -/
theorem nodeAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    nodeAtPeriod (drawingGridSize graph) node =
      RetainedCompactAtomWords.zeroCarrierNode
        (normalizeCarrierNode graph node).1 := by
  cases node with
  | terminal terminal => rfl
  | boundary boundary =>
      simp only [nodeAtPeriod, normalizeCarrierNode,
        RetainedCompactAtomWords.zeroCarrierNode]
      congr 2

/-- The graph-free pair is the exact compact pair of the semantically
normalized periodic carrier prototype. -/
theorem pairAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    pairAtPeriod (drawingGridSize graph) node =
      RetainedCompactAtomWords.carrierPair
        (normalizeCarrierNode graph node).1 := by
  unfold pairAtPeriod RetainedCompactAtomWords.carrierPair
  rw [nodeAtPeriod_drawingGridSize]

/-- The graph-free constructor-tagged word is exactly the final compact word
of the normalized carrier endpoint. -/
theorem compactWordAtPeriod_drawingGridSize
    {Variable : Type*} [DecidableEq Variable]
    (graph : PeriodicGraph Variable) (sourceWord : Variable → List Bool)
    (node : CarrierNode) :
    compactWordAtPeriod (drawingGridSize graph) node =
      RetainedCompactAtomWords.word sourceWord
        ⟨periodicCarrierNodeToPlanarSATVariable
          (normalizeCarrierNode graph node).1⟩ := by
  cases node with
  | terminal terminal =>
      simp [compactWordAtPeriod, RetainedCompactAtomWords.word,
        periodicCarrierNodeToPlanarSATVariable,
        pairAtPeriod_drawingGridSize]
  | boundary boundary =>
      simp [compactWordAtPeriod, RetainedCompactAtomWords.word,
        periodicCarrierNodeToPlanarSATVariable,
        pairAtPeriod_drawingGridSize]

end CarrierNodeNormalizedSourceKeys
end LeanTrominoes.PeriodicOrthocrossing
