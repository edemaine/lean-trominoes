/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnaryData

/-! # Correctness of unary numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Splitting an integer into its positive and negative magnitudes and then
subtracting them recovers the integer. -/
@[simp] theorem signedOfUnaryFields_signedUnaryFields (value : Int) :
    signedOfUnaryFields value.toNat (-value).toNat = value := by
  cases value with
  | ofNat value => simp [signedOfUnaryFields]
  | negSucc value => simp [signedOfUnaryFields]; omega

/-- The canonical eleven-field encoding round-trips exactly. -/
@[simp] theorem RouteDescriptor.ofUnaryFields?_unaryFields
    (descriptor : RouteDescriptor) :
    RouteDescriptor.ofUnaryFields? descriptor.unaryFields =
      some descriptor := by
  rcases descriptor with
    ⟨vertexCount, edgeCount, edgeIndex, sourceVertexIndex,
      targetVertexIndex, sourcePortRank, targetPortRank, ⟨horizontal, vertical⟩⟩
  cases horizontal <;> cases vertical <;>
    simp [RouteDescriptor.unaryFields, signedUnaryFields,
      RouteDescriptor.ofUnaryFields?, signedOfUnaryFields] <;> omega

end PeriodicOrthocrossing
end LeanTrominoes
