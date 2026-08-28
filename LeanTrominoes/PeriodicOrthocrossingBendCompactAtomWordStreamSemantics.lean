/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordGuardedStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordStreamCompiler

/-! # Semantics of exact compact bend atom-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendCompactAtomWordStream

@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.affineBaseBendCompactAtomWordStream
          pairs⟩ := by
  unfold emittedStream
  rw [BendCompactAtomWordGuardedStream.emittedStream_encodeDescriptorPairs,
    GuardedCarrierKeyCompactAtomWords.tokens_encode]
  congr 1
  unfold GuardedCarrierKeyCompactAtomWords.compact
    BendCompactAtomWordGuardedStream.guardedWords
    RouteDescriptorPairAffine.affineBaseBendCompactAtomWordStream
    RouteDescriptorPairAffine.bendCompactAtomWords
    GuardedCarrierKeyCompactAtomWords.words
  rw [List.flatMap_assoc]

end BendCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing
