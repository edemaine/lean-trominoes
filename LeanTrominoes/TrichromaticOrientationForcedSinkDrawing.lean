/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticOrientationForcedSink
import LeanTrominoes.PeriodicGraphDrawingCertificate

/-! # A checked planar orthogonal drawing of the forced-sink fragment -/
namespace LeanTrominoes.TrichromaticGraphOrientation.ForcedSink

def underlyingGraph : PeriodicGraph Nat := ⟨List.range 8,graph.2.map Prod.fst⟩

def drawing : PeriodicGridDrawing where
  gridSizePred := 15
  vertexPositions := [(6,10),(6,4),(3,7),(9,10),(9,4),(12,10),(12,4),(2,7)]
  edgeRoutes :=
    [[(6,10),(3,10),(3,7)],[(6,4),(3,4),(3,7)],
     [(6,10),(9,10)],[(6,4),(9,4)],
     [(9,10),(9,4)],[(9,10),(10,10),(10,4),(9,4)],
     [(6,10),(6,12),(12,12),(12,10)],[(6,4),(6,2),(12,2),(12,4)],
     [(12,10),(12,4)],[(12,10),(13,10),(13,4),(12,4)],
     [(2,7),(3,7)]]

theorem underlyingGraph_wellFormed : underlyingGraph.IsWellFormed := by
  unfold PeriodicGraph.IsWellFormed underlyingGraph graph
  decide +kernel

theorem drawing_compatible : PeriodicGridDrawing.FiniteCertificate.Compatible underlyingGraph drawing := by
  unfold PeriodicGridDrawing.FiniteCertificate.Compatible PeriodicGridDrawing.RoutesMatch
    PeriodicGridDrawing.PositionInFundamentalSquare
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem drawing_geometry : PeriodicGridDrawing.FiniteCertificate.Geometry drawing := by
  unfold PeriodicGridDrawing.FiniteCertificate.Geometry
  decide +kernel

theorem drawing_planar : drawing.IsContinuouslyPlanar :=
  (PeriodicGridDrawing.FiniteCertificate.valid_sound underlyingGraph_wellFormed
    ⟨drawing_compatible,drawing_geometry⟩).2

theorem drawing_isCompatible : drawing.IsCompatible underlyingGraph :=
  (PeriodicGridDrawing.FiniteCertificate.valid_sound underlyingGraph_wellFormed
    ⟨drawing_compatible,drawing_geometry⟩).1

theorem drawing_orthogonal : drawing.IsOrthogonal := by
  unfold PeriodicGridDrawing.IsOrthogonal
  decide +kernel

end LeanTrominoes.TrichromaticGraphOrientation.ForcedSink
