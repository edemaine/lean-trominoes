/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics

/-! # Direct-source semantics of rank-ordered normalized carrier fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRankedFieldSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The compiled direct-source field column contains the normalized pair of
every carrier rank datum in exact global stable-rank order. -/
theorem directSourceCarrierNormalizedSourceKeyRankOrderedFields_numeric
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeyRankOrderedFields decider symbols =
      let formula := directSourceFormula decider symbols
      let descriptors := numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      (CarrierRankGlobal.enumeration datums).flatMap fun entry =>
        CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
          (some (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod
            period entry.1)) := by
  let formula := directSourceFormula decider symbols
  have isLocal : formula.incidenceGraph.IsLocal := by
    unfold formula directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  unfold directSourceCarrierNormalizedSourceKeyRankOrderedFields
  exact
    CarrierNormalizedSourceKeyRankOrderedFields.values_numericRouteDescriptors
      formula
      (PeriodicCNF.incidenceGraph_isWellFormed formula)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      isLocal
      (directSourceFormula_isForwardLocal decider symbols)
      (directSource_incidencesWithMetadata_ne_nil decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
