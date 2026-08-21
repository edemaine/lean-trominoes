/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Extensionality for numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptor

/-- Numeric route descriptors are equal when all eight fields are equal. -/
@[ext] theorem ext
    (first second : RouteDescriptor)
    (vertexCount : first.vertexCount = second.vertexCount)
    (edgeCount : first.edgeCount = second.edgeCount)
    (edgeIndex : first.edgeIndex = second.edgeIndex)
    (sourceVertexIndex :
      first.sourceVertexIndex = second.sourceVertexIndex)
    (targetVertexIndex :
      first.targetVertexIndex = second.targetVertexIndex)
    (sourcePortRank : first.sourcePortRank = second.sourcePortRank)
    (targetPortRank : first.targetPortRank = second.targetPortRank)
    (offset : first.offset = second.offset) :
    first = second := by
  cases first
  cases second
  simp_all

end RouteDescriptor
end PeriodicOrthocrossing
end LeanTrominoes
