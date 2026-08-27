/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordStreamSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendRouteDirectionCompiler

/-! # Direct compilation of retained base-bend Figure 9 tail records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceBaseBendTailRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceBaseBendTailRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Exact flat Figure 9 record blocks for every untranslated retained bend
in direct numeric-route order. -/
def directSourceBaseBendRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

theorem directSourceBaseBendRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceBaseBendRouteTailRecordTokens decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            FormulaShapeRetainedPlanarMetadataDirection.bendRouteTailRecordBlock
              routeBend.incomingPort routeBend.outgoingPort false := by
  unfold directSourceBaseBendRouteTailRecordTokens
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact
    RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)

noncomputable def
    directSourceBaseBendRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceBaseBendRouteTailRecordTokens decider) := by
  change TM2ComputableInPolyTime id id (fun symbols =>
    RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider)
    RouteDescriptorPairAffine.affineBaseBendRouteTailRecordStreamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
