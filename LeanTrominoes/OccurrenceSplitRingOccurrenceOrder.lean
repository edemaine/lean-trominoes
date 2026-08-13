/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitRingCycleDrawing
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder

/-!
# Occurrence order around the Figure 7 split ring

The separator-cut implication presentation was chosen so that every real
source-port copy has one linear occurrence order:

1. its copied source spoke;
2. the incoming implication incidence;
3. the outgoing implication incidence.

This file exposes the two local cycle incidences of each ring vertex and
certifies the geometric consequence needed by the 3DM ribbon construction.
For every source port, the spoke and those two cycle routes leave the variable
in clockwise cardinal order.  The separator has only its two cycle
incidences, so it can never create a degree-three ordering obligation.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT

/-- Presentation indices of the implication-cycle incidences at one local
ring vertex. -/
def cycleOccurrenceIndicesAt
    (vertex : RingVertex) : List (Nat × Nat) :=
  (embeddedCNFIncidences cycleFormula)
    |>.filter (fun incidence => incidence.literal.1 = vertex)
    |>.map fun incidence =>
      (incidence.clauseIndex, incidence.literalIndex)

/-- Outgoing variable-to-clause direction of one presentation-indexed local
cycle route. -/
def cycleOccurrenceDirection
    (occurrence : Nat × Nat) : AxisDirection :=
  (AxisDirection.polylineLastDirection
    (cycleRoutes occurrence.1 occurrence.2)).opposite

/-- The two cycle-incidence directions at one local ring vertex, retained in
formula presentation order. -/
def cycleOccurrenceDirectionsAt
    (vertex : RingVertex) : List AxisDirection :=
  (cycleOccurrenceIndicesAt vertex).map cycleOccurrenceDirection

/-- Outgoing variable-to-clause direction of one retained source spoke. -/
def spokeOccurrenceDirection (port : Port) : AxisDirection :=
  (AxisDirection.polylineLastDirection (spokeRoute port)).opposite

/-- Every real port occurs exactly twice in the implication-cycle suffix. -/
@[simp]
theorem cycleOccurrenceIndicesAt_port_length (port : Port) :
    (cycleOccurrenceIndicesAt (.port port)).length = 2 := by
  cases port <;> native_decide

/-- The degree-two separator also occurs exactly twice in the implication
cycle. -/
@[simp]
theorem cycleOccurrenceIndicesAt_separator_length :
    (cycleOccurrenceIndicesAt .separator).length = 2 := by
  native_decide

/-- At every real port, the source spoke followed by the two implication
incidences in syntactic presentation order has clockwise terminal
directions. -/
theorem port_occurrenceDirections_inClockwiseOrder (port : Port) :
    AxisDirection.InClockwiseOrder
      (spokeOccurrenceDirection port)
      ((cycleOccurrenceDirectionsAt (.port port)).getD
        0 .invalid)
      ((cycleOccurrenceDirectionsAt (.port port)).getD
        1 .invalid) := by
  cases port <;> native_decide

end OccurrenceSplitRing
end LeanTrominoes
