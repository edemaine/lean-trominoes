/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidencePrefixSemanticBridge

/-! # Semantic bridge for horizontal ordinary variable prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidencePrefixComputed_eq_assembledOrdinary
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member : Triple.ordinary atom slot variant localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalVariableIncidencePrefixComputed
        (((source, atom),
          Triple.ordinary atom slot variant localTriple), color) =
      assembledOrdinaryPrefix
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        atom slot variant localTriple member color := by
  let location := ordinaryTriple_location
    (horizontalSemanticNormalizedRibbonSource source).erase
    atom slot variant localTriple member
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨location.1, location.2.1⟩⟩
  have bridge := horizontalVariableIncidencePrefixComputed_eq_semantic
    source width compatible entry
    (Triple.ordinary atom slot variant localTriple)
    location.2.2 color
  unfold assembledOrdinaryPrefix
  convert bridge using 1 <;> simp only [entry]
  congr 1

end PeriodicCNFStripReduction
end LeanTrominoes
