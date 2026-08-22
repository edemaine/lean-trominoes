/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValues
import Mathlib.Tactic.FinCases

/-! # Exact semantics of tagged descriptor-pair field values -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

/-- Counting one field's tags in its own descriptor block recovers exactly
the corresponding unary descriptor field. -/
theorem tokenFieldValue_descriptorUnits_same
    (side : Side) (descriptor : RouteDescriptor) (field : Fin 11) :
    tokenFieldValue (descriptorUnits side descriptor) side field =
      descriptorFieldValue descriptor field := by
  rcases descriptor with
    ⟨vertexCount, edgeCount, edgeIndex, sourceVertexIndex,
      targetVertexIndex, sourcePortRank, targetPortRank,
      ⟨horizontal, vertical⟩⟩
  fin_cases field <;> cases side <;>
    simp [tokenFieldValue, descriptorUnits, descriptorFieldValue,
      RouteDescriptor.unaryFields, signedUnaryFields, taggedFields,
      nextField, List.count_replicate]

/-- Tags from the other descriptor side never contribute to a field count. -/
theorem tokenFieldValue_descriptorUnits_other
    (descriptor : RouteDescriptor) (field : Fin 11) :
    tokenFieldValue (descriptorUnits .second descriptor) .first field = 0 ∧
      tokenFieldValue (descriptorUnits .first descriptor) .second field = 0 := by
  rcases descriptor with
    ⟨vertexCount, edgeCount, edgeIndex, sourceVertexIndex,
      targetVertexIndex, sourcePortRank, targetPortRank,
      ⟨horizontal, vertical⟩⟩
  simp [tokenFieldValue, descriptorUnits,
    RouteDescriptor.unaryFields, signedUnaryFields, taggedFields,
    nextField, List.count_replicate]

/-- Counting tags in a complete canonical pair block recovers the semantic
field valuation of that pair. -/
theorem tokenFieldValue_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) (field : Fin 11) :
    tokenFieldValue (descriptorPairTokens pair) side field =
      pairFieldValue pair side field := by
  rcases pair with ⟨first, second⟩
  cases side with
  | first =>
      have same :
          List.count (.unit .first field) (descriptorUnits .first first) =
            descriptorFieldValue first field :=
        tokenFieldValue_descriptorUnits_same .first first field
      have other :
          List.count (.unit .first field) (descriptorUnits .second second) = 0 :=
        (tokenFieldValue_descriptorUnits_other second field).1
      simp [descriptorPairTokens, pairFieldValue, tokenFieldValue,
        same, other]
  | second =>
      have same :
          List.count (.unit .second field) (descriptorUnits .second second) =
            descriptorFieldValue second field :=
        tokenFieldValue_descriptorUnits_same .second second field
      have other :
          List.count (.unit .second field) (descriptorUnits .first first) = 0 :=
        (tokenFieldValue_descriptorUnits_other first field).2
      simp [descriptorPairTokens, pairFieldValue, tokenFieldValue,
        same, other]

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
