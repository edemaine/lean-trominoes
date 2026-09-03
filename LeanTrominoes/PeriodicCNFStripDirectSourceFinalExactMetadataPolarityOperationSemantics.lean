/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSourceIndexedPolarityOperationSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteSourceIndexedListSemantics

/-! # Direct polarity operations agree with exact metadata route blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalExactMetadataPolarityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalExactMetadataPolarityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceIsLocal
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).IsLocal := by
  simpa only [directSourceFormula] using
    sourceFormula_isLocal
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceWidthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  simpa only [directSourceFormula] using
    sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceOccurrencesAtMostThree
    (symbols : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 (directSourceFormula decider symbols) := by
  unfold directSourceFormula
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_occurrencesAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols))

private theorem directSourceClausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  simpa only [directSourceFormula] using
    sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- The named placement paired with `directSourceFinalGaugedFormula`. -/
def directSourceFinalGaugedPlacement
    (symbols : List encoding.Γ) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
    (directSourceFormula decider symbols)

/-- The named exact incidence routes paired with the direct final gauged
formula and placement. -/
noncomputable def directSourceFinalGaugedIncidenceRoutes
    (symbols : List encoding.Γ) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
    (directSourceFormula decider symbols)
    (directSourceIsLocal decider symbols)
    (directSourceWidthAtMostThree decider symbols)
    (directSourceOccurrencesAtMostThree decider symbols)
    (directSourceClausesNonempty decider symbols)

/-- After attaching the exact global source-clause indices, the direct
Figure 9 route pairs and the semantic exact route blocks have identical
source incidence coordinates and polarity operations. -/
theorem directFigureNinePolarityRoutePairs_sourceIndexedDescriptor_eq_exactMetadata
    (symbols : List encoding.Γ) :
    List.zipWith
        (fun sourceClauseIndex pair =>
          sourceIndexedDescriptorOf sourceClauseIndex
            pair.1.polarity.indexed)
        (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols)
        (directFigureNinePolarityRoutePairs decider symbols) =
      (exactMetadataRouteBlocks
        (directSourceFinalGaugedFormula decider symbols)
        (directSourceFinalGaugedPlacement decider symbols)
        (directSourceFinalGaugedIncidenceRoutes decider symbols)).map
          RouteDirectionBlock.sourceIndexedDescriptor := by
  rw [directFigureNinePolarityRoutePairs_zipWith_sourceIndexedDescriptor]
  exact
    (exactMetadataRouteBlocks_map_sourceIndexedDescriptor_eq_values
      (directSourceFinalGaugedFormula decider symbols)
      (directSourceFinalGaugedPlacement decider symbols)
      (directSourceFinalGaugedIncidenceRoutes decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
