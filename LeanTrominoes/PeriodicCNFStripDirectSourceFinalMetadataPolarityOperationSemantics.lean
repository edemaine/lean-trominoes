/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityOperationSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteOperationListSemantics
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeValueProjection

/-! # Direct Figure 9 headers agree with semantic polarity metadata -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalMetadataPolarityOperationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalMetadataPolarityOperationVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The named direct final-clockwise formula after the same canonical
variable gauge used by the routed horizontal construction. -/
noncomputable def directSourceFinalGaugedFormula
    (symbols : List encoding.Γ) :=
  (directSourceFinalClockwiseFormula decider symbols).variableGauge
    (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      (directSourceFormula decider symbols))

/-- The direct pair headers and the semantic polarity-normalization metadata
have the same local source-literal indices and operations, in the same
clause-major output order. -/
theorem directFigureNinePolarityRoutePairs_map_indexedPolarity_eq_metadata
    (symbols : List encoding.Γ)
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions
        (OneInThreeNoUnitVariable
          (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
            Variable))) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair => pair.1.polarity.indexed) =
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions
        (directSourceFinalGaugedFormula decider symbols)).flatMap
            metadataIndexedDescriptorBlock := by
  have gaugedValueEq :=
    PositionedPeriodicCNF.variableGauge_clauseLiteralValues
      (directSourceFinalClockwiseFormula decider symbols)
      (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        (directSourceFormula decider symbols))
  have gaugedScheduleEq :=
    congrArg (List.flatMap indexedDescriptors) gaugedValueEq
  calc
    _ = (directSourceFinalClockwiseFormula decider symbols).clauses.flatMap
          (fun clause => indexedDescriptors
            (clause.literals.map PeriodicLiteral.value)) :=
      directFigureNinePolarityRoutePairs_map_indexedPolarity decider symbols
    _ = (directSourceFinalGaugedFormula decider symbols).clauses.flatMap
            (fun clause => indexedDescriptors
              (clause.literals.map PeriodicLiteral.value)) := by
      simpa only [directSourceFinalGaugedFormula,
        List.flatMap_map, Function.comp_apply] using
        gaugedScheduleEq.symm
    _ = _ := by
      exact
        (formulaClauseMetadata_flatMap_metadataIndexedDescriptorBlock_eq_values
          positions (directSourceFinalGaugedFormula decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
