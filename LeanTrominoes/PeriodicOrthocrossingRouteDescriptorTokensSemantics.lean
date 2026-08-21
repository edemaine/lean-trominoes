/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnarySemantics

/-! # Exact semantics of counted route-descriptor tokens -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicCNF.UnaryProgramTokens

/-- The counted token stream has exactly one marker per descriptor. -/
@[simp] theorem selectedCount_routeDescriptorTokens
    (descriptors : List RouteDescriptor) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
        (routeDescriptorTokens descriptors) =
      descriptors.length := by
  unfold routeDescriptorTokens routeDescriptorFieldBlocks
  simp

/-- Unary expansion exposes the eleven fields of every descriptor in exact
record order. -/
@[simp] theorem unaryEncode_routeDescriptorTokens
    (descriptors : List RouteDescriptor) :
    unaryEncode (routeDescriptorTokens descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((descriptors.map RouteDescriptor.unaryFields).flatten) := by
  unfold routeDescriptorTokens routeDescriptorFieldBlocks
  simp

/-- Every field block in the token stream decodes to its source descriptor. -/
@[simp] theorem map_ofUnaryFields?_routeDescriptorFieldBlocks
    (descriptors : List RouteDescriptor) :
    (routeDescriptorFieldBlocks descriptors).map
        RouteDescriptor.ofUnaryFields? =
      descriptors.map some := by
  simp [routeDescriptorFieldBlocks]

end PeriodicOrthocrossing
end LeanTrominoes
