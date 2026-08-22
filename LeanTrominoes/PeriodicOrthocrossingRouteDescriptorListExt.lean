/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorExt

/-! # Extensionality for lists of numeric route descriptors -/

namespace LeanTrominoes

namespace List

theorem getElem_map_eq_of_map_eq
    {First Second Output : Type*}
    (first : List First) (second : List Second)
    (firstMap : First → Output) (secondMap : Second → Output)
    (mapEq : first.map firstMap = second.map secondMap)
    (index : Nat) (firstLt : index < first.length)
    (secondLt : index < second.length) :
    firstMap first[index] = secondMap second[index] := by
  have point := congrArg (fun values : List Output => values[index]?) mapEq
  rw [List.getElem?_map,
    List.getElem?_eq_getElem firstLt,
    List.getElem?_map,
    List.getElem?_eq_getElem secondLt] at point
  exact Option.some.inj point

end List

namespace PeriodicOrthocrossing
namespace RouteDescriptor

/-- Descriptor lists are equal when they have equal length and every field
projection agrees in order. -/
theorem list_ext
    (first second : List RouteDescriptor)
    (lengthEq : first.length = second.length)
    (vertexCountEq : first.map (·.vertexCount) =
      second.map (·.vertexCount))
    (edgeCountEq : first.map (·.edgeCount) =
      second.map (·.edgeCount))
    (edgeIndexEq : first.map (·.edgeIndex) =
      second.map (·.edgeIndex))
    (sourceVertexIndexEq : first.map (·.sourceVertexIndex) =
      second.map (·.sourceVertexIndex))
    (targetVertexIndexEq : first.map (·.targetVertexIndex) =
      second.map (·.targetVertexIndex))
    (sourcePortRankEq : first.map (·.sourcePortRank) =
      second.map (·.sourcePortRank))
    (targetPortRankEq : first.map (·.targetPortRank) =
      second.map (·.targetPortRank))
    (offsetEq : first.map (·.offset) = second.map (·.offset)) :
    first = second := by
  apply List.ext_getElem lengthEq
  intro index firstLt secondLt
  apply RouteDescriptor.ext
  · exact List.getElem_map_eq_of_map_eq first second
      (·.vertexCount) (·.vertexCount) vertexCountEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.edgeCount) (·.edgeCount) edgeCountEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.edgeIndex) (·.edgeIndex) edgeIndexEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.sourceVertexIndex) (·.sourceVertexIndex) sourceVertexIndexEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.targetVertexIndex) (·.targetVertexIndex) targetVertexIndexEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.sourcePortRank) (·.sourcePortRank) sourcePortRankEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.targetPortRank) (·.targetPortRank) targetPortRankEq
      index firstLt secondLt
  · exact List.getElem_map_eq_of_map_eq first second
      (·.offset) (·.offset) offsetEq index firstLt secondLt

end RouteDescriptor
end PeriodicOrthocrossing
end LeanTrominoes
