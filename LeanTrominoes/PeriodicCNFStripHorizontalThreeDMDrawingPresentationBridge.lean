/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticDrawingWitness
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingAssembledBridge

/-! # Executable horizontal drawing equals the semantic presentation -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMDrawingComputed_eq_presentationDrawing
    (source : PeriodicCNF Nat) :
    horizontalThreeDMDrawingComputed source = (presentation source).drawing := by
  let certificate := horizontalSemanticDrawing_routingCertificate source
  have computedEq :
      horizontalThreeDMDrawingComputed source =
        assembledDrawing
          (paddedNormalizedCoordinatedRibbonThreeStrandRouting
            (horizontalSemanticRoutedRibbonReadyPresentation source)
            certificate.width certificate.occurrences certificate.arity
            certificate.variableOrdered certificate.clauseOrdered) := by
    unfold paddedNormalizedCoordinatedRibbonThreeStrandRouting
    exact horizontalThreeDMDrawingComputed_eq_assembled source
      (paddedNormalizedSource_widthAtMostThree certificate.width)
      (paddedNormalizedRibbonReady_sourceRibbonFansClockwiseCompatible
        (horizontalSemanticRoutedRibbonReadyPresentation source)
        certificate.width certificate.occurrences certificate.arity
        certificate.variableOrdered certificate.clauseOrdered)
  exact computedEq.trans certificate.drawing_eq.symm

end PeriodicCNFStripReduction
end LeanTrominoes
