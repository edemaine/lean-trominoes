/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackSuffixSemantics
import LeanTrominoes.RetainedAngularFanNormalizedFallbackJoinedDirectionAllSemantics

/-! # Complete normalized fallback direction words of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedFallbackRouteSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierNormalizedFallbackRouteSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete canonical normalized words obtained by pairing every scaled
semantic carrier prefix with its aligned retained-fan suffix query. -/
def directSourceFinalCarrierNormalizedFallbackGeometricDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.retainedJoinedDirections
    ((directSourceFinalCarrierFallbackPrefixWords decider symbols).zip
      (directSourceFinalCarrierFallbackSemanticQueries decider symbols))

private theorem
    directSourceFinalCarrierNormalizedFallbackPrefixWords_terminalData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackPrefixWords decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).length := by
  rw [directSourceFinalCarrierFallbackPrefixWords_length]
  unfold directSourceFinalCarrierFallbackTerminalData
    CarrierFallbackTerminalData.terminalData
    directSourceFinalCarrierFallbackPrefixBlocks
  simp [List.length_flatMap]
  omega

private theorem
    directSourceFinalCarrierNormalizedFallbackSlots_terminalData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierOccurrenceSlots decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).length := by
  have aligned :=
    directSourceFinalCarrierFallbackRolesSlots_length decider symbols
  unfold directSourceFinalCarrierFallbackHeaderRoles at aligned
  rw [directSourceFinalCarrierFallbackTerminalDirections_eq,
    FallbackSuffixHeaderRoles.carrierRoles_length] at aligned
  simp only [List.length_map] at aligned
  exact aligned.symm

private theorem
    directSourceFinalCarrierNormalizedFallbackSemanticQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackSemanticQueries decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).length := by
  unfold directSourceFinalCarrierFallbackSemanticQueries
  rw [FallbackSuffixQueryColumns.alignedQueries_length,
    FallbackSuffixHeaderRoles.carrierRoles_length,
    directSourceFinalCarrierNormalizedFallbackSlots_terminalData_length]
  simp

/-- The direct joined carrier compiler emits exactly the complete canonical
normalized source-prefix-plus-retained-fan word for every carrier incidence. -/
theorem directSourceFinalCarrierNormalizedFallbackRouteDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackRouteDirections
        decider symbols =
      directSourceFinalCarrierNormalizedFallbackGeometricDirections
        decider symbols := by
  have lengthEq :
      (directSourceFinalCarrierFallbackPrefixWords decider symbols).length =
        (directSourceFinalCarrierFallbackSemanticQueries
          decider symbols).length :=
    (directSourceFinalCarrierNormalizedFallbackPrefixWords_terminalData_length
      decider symbols).trans
        (directSourceFinalCarrierNormalizedFallbackSemanticQueries_length
          decider symbols).symm
  unfold directSourceFinalCarrierNormalizedFallbackRouteDirections
    directSourceFinalCarrierNormalizedFallbackSuffixDirections
    directSourceFinalCarrierNormalizedFallbackGeometricDirections
  rw [directSourceFinalCarrierFallbackPrefixDirections_eq,
    directSourceFinalCarrierFallbackSuffixQueries_eq]
  exact
    NormalizedFallbackSuffixDirectionCompiler.joined_prefixWords_directions_eq
      (directSourceFinalCarrierFallbackPrefixWords decider symbols)
      (directSourceFinalCarrierFallbackSemanticQueries decider symbols)
      lengthEq
      (directSourceFinalCarrierFallbackSemanticQueries_lengthPositive
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
