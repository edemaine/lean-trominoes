/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMLocality
import LeanTrominoes.PeriodicCNFStripNativeThreeDMDrawingRoutes
import LeanTrominoes.PeriodicThreeDMUnitDrawingCertificate

/-! # The native subdivided 3DM drawing passes the finite verifier -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicThreeDM
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

theorem nativeThreeDMUnit_verified (s : List encoding.Γ) :
    FiniteDrawingCertificate.verifies (nativeThreeDMProblem decider s) (nativeThreeDMUnitDrawing decider s) = true := by
  apply FiniteDrawingCertificate.verifies_unitSubdivide (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s)
    (nativeThreeDMDrawing_compatible decider s) (nativeThreeDMDrawing_orthogonal decider s)
    (nativeThreeDMDrawing_halo decider s)
  · rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing]
    exact (presentation _).continuouslyPlanar
  · rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing]
    exact presentation_separated _
  · rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_eq_presentationDrawing]
    exact presentation_routesSimple _

end LeanTrominoes.PeriodicCNFStripReduction
end
