/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterSemantics

/-! # End-delimited blocks of canonical route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

open TM2EndDelimitedBlockMap

theorem blocksAux_descriptorPairTokens_append
    (pair : RouteDescriptor × RouteDescriptor) (rest : List Token) :
    blocksAux isPairEnd [] (descriptorPairTokens pair ++ rest) =
      descriptorPairTokens pair :: blocksAux isPairEnd [] rest := by
  rw [descriptorPairTokens_eq_body]
  rw [List.append_assoc]
  exact blocksAux_append_pairEnd [] (descriptorPairBody pair) rest
    (descriptorPairBody_continue pair)

theorem blocksAux_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    blocksAux isPairEnd [] (encodeDescriptorPairs pairs) =
      pairs.map descriptorPairTokens := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      change blocksAux isPairEnd []
          (descriptorPairTokens pair ++ encodeDescriptorPairs pairs) =
        descriptorPairTokens pair :: pairs.map descriptorPairTokens
      rw [blocksAux_descriptorPairTokens_append, induction]

@[simp] theorem blocks_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    blocks isPairEnd (encodeDescriptorPairs pairs) =
      pairs.map descriptorPairTokens := by
  exact blocksAux_encodeDescriptorPairs pairs

theorem mappedOutput_encodeDescriptorPairs
    {Target : Type} (function : List Token → List Target)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    mappedOutput isPairEnd function (encodeDescriptorPairs pairs) =
      pairs.flatMap (fun pair => function (descriptorPairTokens pair)) := by
  unfold mappedOutput
  rw [blocks_encodeDescriptorPairs, List.flatMap_map]

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
