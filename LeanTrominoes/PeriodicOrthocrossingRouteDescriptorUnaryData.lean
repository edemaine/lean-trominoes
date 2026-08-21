/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Unary fields for numeric orthocrossing route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A signed integer as separate unary positive and negative magnitudes.  At
most one field is nonzero for values produced by this encoder. -/
def signedUnaryFields (value : Int) : List Nat :=
  [value.toNat, (-value).toNat]

/-- Recover a signed integer from positive and negative unary magnitudes. -/
def signedOfUnaryFields (positive negative : Nat) : Int :=
  (positive : Int) - (negative : Int)

/-- Eleven unary naturals encode the seven natural descriptor fields followed
by two signed coordinates. -/
def RouteDescriptor.unaryFields (descriptor : RouteDescriptor) : List Nat :=
  [descriptor.vertexCount, descriptor.edgeCount, descriptor.edgeIndex,
    descriptor.sourceVertexIndex, descriptor.targetVertexIndex,
    descriptor.sourcePortRank, descriptor.targetPortRank] ++
    signedUnaryFields descriptor.offset.1 ++
    signedUnaryFields descriptor.offset.2

/-- Parse exactly one canonical eleven-field route descriptor. -/
def RouteDescriptor.ofUnaryFields? : List Nat → Option RouteDescriptor
  | [vertexCount, edgeCount, edgeIndex, sourceVertexIndex,
      targetVertexIndex, sourcePortRank, targetPortRank,
      horizontalPositive, horizontalNegative,
      verticalPositive, verticalNegative] =>
      some
        { vertexCount := vertexCount
          edgeCount := edgeCount
          edgeIndex := edgeIndex
          sourceVertexIndex := sourceVertexIndex
          targetVertexIndex := targetVertexIndex
          sourcePortRank := sourcePortRank
          targetPortRank := targetPortRank
          offset :=
            (signedOfUnaryFields horizontalPositive horizontalNegative,
              signedOfUnaryFields verticalPositive verticalNegative) }
  | _ => none

end PeriodicOrthocrossing
end LeanTrominoes
