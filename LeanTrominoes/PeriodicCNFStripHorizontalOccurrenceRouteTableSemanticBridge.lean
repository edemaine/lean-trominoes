/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRouteTableDataBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRoutingSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge
import LeanTrominoes.ListAttachFlatMap

/-! # Semantic correctness of the colored occurrence-route table -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PeriodicThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The certified routing enumerated in the same occurrence/color order as
the proof-free table. -/
def horizontalSemanticOccurrenceRouteTable
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) : List (List Cell) :=
  (occurrenceEntries
      (horizontalSemanticNormalizedRibbonSource source).erase).attach.flatMap
    fun entry =>
      incidenceColors.map fun color =>
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible).route entry color

theorem horizontalOccurrenceRouteTableComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    horizontalOccurrenceRouteTableComputed source =
      horizontalSemanticOccurrenceRouteTable source width compatible := by
  rw [horizontalOccurrenceRouteTableComputed_eq_rows]
  unfold horizontalOccurrenceEntriesComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
  unfold horizontalSemanticOccurrenceRouteTable
  apply List.flatMap_eq_attach_flatMap
  intro entry
  apply List.map_congr_left
  intro color colorMember
  exact horizontalOccurrenceCoordinatedRouteComputed_eq_routing
    source width compatible entry color

end PeriodicCNFStripReduction
end LeanTrominoes
