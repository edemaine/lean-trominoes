/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionStreamSemantics
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compilation of retained base-bend route direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceBaseBendRouteDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceBaseBendRouteDirectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete route-delimited words of every untranslated retained bend in the
direct source, ordered by numeric route and then bend. -/
def directSourceBaseBendRouteDirectionBlocks
    (symbols : List encoding.Γ) :
    List RouteDescriptorPairAffine.BendRouteDirectionToken :=
  RouteDescriptorPairAffine.affineBaseBendRouteDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- The direct stream is exactly the semantic untranslated bend family. -/
theorem directSourceBaseBendRouteDirectionBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceBaseBendRouteDirectionBlocks decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            RouteDescriptorPairAffine.canonicalBendRouteDirectionBlock
              routeBend.incomingPort routeBend.outgoingPort := by
  unfold directSourceBaseBendRouteDirectionBlocks
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact
    RouteDescriptorPairAffine.affineBaseBendRouteDirectionStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)

/-- Direct PSPACE source symbols compile to all retained base-bend route
words in polynomial time. -/
noncomputable def
    directSourceBaseBendRouteDirectionBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceBaseBendRouteDirectionBlocks decider) := by
  let tagged :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let selected := TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.affineBaseBendRouteDirectionStreamComputableInPolyTime
  exact selected

end PeriodicCNFStripReduction
end LeanTrominoes

end
