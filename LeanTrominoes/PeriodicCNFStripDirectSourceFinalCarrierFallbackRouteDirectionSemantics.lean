/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteDirectionCompiler
import LeanTrominoes.RetainedAngularFanFallbackJoinedDirectionSemantics

/-! # Complete geometric fallback direction words of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackRouteSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackRouteSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete geometric words obtained by pairing every scaled semantic
carrier prefix with its aligned terminal-data/slot suffix query. -/
def directSourceFinalCarrierFallbackGeometricDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  FallbackSuffixDirectionCompiler.retainedJoinedDirections
    ((directSourceFinalCarrierFallbackPrefixWords decider symbols).zip
      (directSourceFinalCarrierFallbackSemanticQueries decider symbols))

private theorem directSourceFinalCarrierFallbackPrefixWords_terminalData_length
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

private theorem directSourceFinalCarrierFallbackSlots_terminalData_length
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

private theorem directSourceFinalCarrierFallbackSemanticQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackSemanticQueries
      decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).length := by
  unfold directSourceFinalCarrierFallbackSemanticQueries
  rw [FallbackSuffixQueryColumns.alignedQueries_length,
    FallbackSuffixHeaderRoles.carrierRoles_length,
    directSourceFinalCarrierFallbackSlots_terminalData_length]
  simp

/-- The direct joined carrier compiler emits exactly the complete geometric
source-prefix-plus-retained-fan word for every carrier incidence. -/
theorem directSourceFinalCarrierFallbackRouteDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackRouteDirections decider symbols =
      directSourceFinalCarrierFallbackGeometricDirections
        decider symbols := by
  have lengthEq :
      (directSourceFinalCarrierFallbackPrefixWords
        decider symbols).length =
        (directSourceFinalCarrierFallbackSemanticQueries
          decider symbols).length :=
    (directSourceFinalCarrierFallbackPrefixWords_terminalData_length
      decider symbols).trans
        (directSourceFinalCarrierFallbackSemanticQueries_length
          decider symbols).symm
  have positive :
      ∀ query ∈ directSourceFinalCarrierFallbackSemanticQueries
          decider symbols,
        0 < query.rawLength := by
    rw [← directSourceFinalCarrierFallbackSuffixQueries_eq]
    exact directSourceFinalCarrierFallbackSuffixQueries_lengthPositive
      decider symbols
  unfold directSourceFinalCarrierFallbackRouteDirections
    directSourceFinalCarrierFallbackSuffixDirections
    directSourceFinalCarrierFallbackGeometricDirections
  rw [directSourceFinalCarrierFallbackPrefixDirections_eq,
    directSourceFinalCarrierFallbackSuffixQueries_eq]
  exact
    FallbackSuffixDirectionCompiler.joined_prefixWords_directions_eq
      (directSourceFinalCarrierFallbackPrefixWords decider symbols)
      (directSourceFinalCarrierFallbackSemanticQueries decider symbols)
      lengthEq positive

end LeanTrominoes.PeriodicCNFStripReduction

end
