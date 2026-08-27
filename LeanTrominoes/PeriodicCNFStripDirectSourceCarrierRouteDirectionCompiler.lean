/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamNumericSemantics

/-! # Direct compilation of retained carrier route-direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierRouteDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceCarrierRouteDirectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete route-delimited canonical blocks of all retained carriers in
the global rank order reconstructed from the direct source. -/
def directSourceCarrierRouteDirectionBlocks
    (symbols : List encoding.Γ) :
    List CarrierSpanRouteDirections.Token :=
  CarrierRankOrderedPairs.retainedRouteDirectionStream
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- The direct compiler's output has the exact selected rank-pair semantics
of the complete carrier stream. -/
theorem directSourceCarrierRouteDirectionBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierRouteDirectionBlocks decider symbols =
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
            CarrierSpanRouteDirections.canonicalBlock
              first.1.1.horizontal
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  unfold directSourceCarrierRouteDirectionBlocks
  exact
    CarrierRankOrderedPairs.retainedRouteDirectionStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)
      (directSource_incidencesWithMetadata_ne_nil decider symbols)

/-- Direct PSPACE source symbols compile to the complete retained carrier
direction stream in polynomial time. -/
noncomputable def
    directSourceCarrierRouteDirectionBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierRouteDirectionBlocks decider) := by
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      CarrierRankOrderedPairs.retainedRouteDirectionStream
        (numericRouteDescriptors (directSourceFormula decider symbols)))
  let descriptors :=
    directSourceNumericRouteDescriptorsComputableInPolyTime decider
  exact TM2CompositionMachine.computableInPolyTime descriptors
    CarrierRankOrderedPairs.retainedRouteDirectionStreamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
