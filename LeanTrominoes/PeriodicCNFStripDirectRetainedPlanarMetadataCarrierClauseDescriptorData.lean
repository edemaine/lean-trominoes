/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorData
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordData

/-! # Direct retained carrier descriptors from numeric route data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCarrierDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedCarrierDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Apply the rank-ordered retained carrier scan to the direct source's exact
numeric route-descriptor list. -/
def directRetainedPlanarMetadataCompiledCarrierClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.rankOrderedCarrierLinkDescriptorScan
    (numericRouteDescriptors (directSourceFormula decider symbols))

private theorem routeDescriptorBinaryWords_encode_eq_carrierInput
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.finEncoding.encode
        (RouteDescriptorBinaryWords.words descriptors) =
      CarrierRankOrderedPairs.InputEncoding descriptors := by
  rfl

/-- The existing direct binary-word target is definitionally the canonical
input encoding expected by the rank-ordered carrier compiler. -/
theorem directSourceRouteDescriptorBinaryWords_encode_eq_carrierInput
    (symbols : List encoding.Γ) :
    DelimitedBinaryWords.finEncoding.encode
        (directSourceRouteDescriptorBinaryWords decider symbols) =
      PeriodicOrthocrossing.CarrierRankOrderedPairs.InputEncoding
        (numericRouteDescriptors (directSourceFormula decider symbols)) := by
  unfold directSourceRouteDescriptorBinaryWords
  exact routeDescriptorBinaryWords_encode_eq_carrierInput _

abbrev DirectRetainedPlanarMetadataCompiledCarrierClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCompiledCarrierClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
