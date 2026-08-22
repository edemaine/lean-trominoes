/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstructedEdgeRouteLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Uniform segment bounds for numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem fanout_length_le_three (centerX portColumn : Int) :
    (fanout centerX portColumn).length ≤ 3 := by
  rw [fanout_length]
  split <;> simp

/-- Every offset case has at most six central-track points. -/
theorem RouteDescriptor.core_length_le_six (descriptor : RouteDescriptor) :
    descriptor.core.length ≤ 6 := by
  unfold RouteDescriptor.core
  split <;> simp_all
  all_goals split <;> simp_all

/-- The complete fixed track construction contributes at most nine segments
for any numeric descriptor, including malformed nonlocal offsets. -/
theorem RouteDescriptor.route_segments_length_le_nine
    (descriptor : RouteDescriptor) :
    (gridPolylineSegments descriptor.route).length ≤ 9 := by
  rw [gridPolylineSegments_length]
  unfold RouteDescriptor.route joinPolylines translatePolyline
  simp only [List.length_append, List.length_tail, List.length_map,
    List.length_reverse]
  have sourceLe := fanout_length_le_three
    (vertexX descriptor.sourceVertexIndex)
    (descriptorPortX descriptor.sourceVertexIndex descriptor.sourcePortRank)
  have targetLe := fanout_length_le_three
    (vertexX descriptor.targetVertexIndex)
    (descriptorPortX descriptor.targetVertexIndex descriptor.targetPortRank)
  have coreLe := descriptor.core_length_le_six
  omega

end PeriodicOrthocrossing
end LeanTrominoes
