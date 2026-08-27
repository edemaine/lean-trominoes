/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamNumericSemantics

/-! # Direct compilation of retained carrier Figure 9 tail records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierTailRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceCarrierTailRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Exact flat Figure 9 record blocks for every retained carrier selected
from the direct source's numeric route descriptors. -/
def directSourceCarrierRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  CarrierRankOrderedPairs.retainedRouteTailRecordStream
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- The direct output has the exact global selected-pair semantics. -/
theorem directSourceCarrierRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierRouteTailRecordTokens decider symbols =
      let formula := directSourceFormula decider symbols
      let descriptors := numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          period descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      entries.zipIdx.flatMap fun first =>
        entries.zipIdx.flatMap fun second =>
          if CarrierRankOrderedPairs.retainedPredicate first second then
            FormulaShapeRetainedPlanarMetadataDirection.carrierLensRouteTailRecordBlock
              first.1.1.horizontal
              (first.1.1.pairNextSlice second.1.1)
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  unfold directSourceCarrierRouteTailRecordTokens
  exact
    CarrierRankOrderedPairs.retainedRouteTailRecordStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)
      (directSource_incidencesWithMetadata_ne_nil decider symbols)

/-- Direct PSPACE-source symbols compile to the complete retained-carrier
Figure 9 tail-record stream in polynomial time. -/
noncomputable def
    directSourceCarrierRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierRouteTailRecordTokens decider) := by
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      CarrierRankOrderedPairs.retainedRouteTailRecordStream
        (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierRankOrderedPairs.retainedRouteTailRecordStreamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
