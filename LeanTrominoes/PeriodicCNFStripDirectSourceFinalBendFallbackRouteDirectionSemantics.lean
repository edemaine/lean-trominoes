/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackPrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteDirectionCompiler
import LeanTrominoes.RetainedAngularFanFallbackJoinedDirectionSemantics

/-! # Complete geometric fallback direction words of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackRouteSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackRouteSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete geometric words obtained by pairing every scaled semantic bend
prefix with its aligned terminal-data/slot suffix query. -/
def directSourceFinalBendFallbackGeometricDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  FallbackSuffixDirectionCompiler.retainedJoinedDirections
    ((directSourceFinalBendFallbackPrefixWords decider symbols).zip
      (directSourceFinalBendFallbackSemanticQueries decider symbols))

private theorem directSourceFinalBendFallbackPrefixWords_terminalData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackPrefixWords decider symbols).length =
      (directSourceFinalBendFallbackTerminalData decider symbols).length := by
  unfold directSourceFinalBendFallbackPrefixWords
    directSourceFinalBendFallbackTerminalData
    PeriodicEightOccurrenceSplit.baseBendTerminalData
  simp [List.length_flatMap]

private theorem directSourceFinalBendFallbackSlots_terminalData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendOccurrenceSlots decider symbols).length =
      (directSourceFinalBendFallbackTerminalData decider symbols).length := by
  have aligned :=
    directSourceFinalBendFallbackRolesSlots_length decider symbols
  unfold directSourceFinalBendFallbackHeaderRoles at aligned
  rw [directSourceFinalBendFallbackTerminalDirections_eq,
    FallbackSuffixHeaderRoles.bendRoles_length] at aligned
  simp only [List.length_map] at aligned
  exact aligned.symm

private theorem directSourceFinalBendFallbackSemanticQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackSemanticQueries
      decider symbols).length =
      (directSourceFinalBendFallbackTerminalData
        decider symbols).length := by
  unfold directSourceFinalBendFallbackSemanticQueries
  rw [FallbackSuffixQueries.alignedQueries_length,
    List.length_replicate,
    directSourceFinalBendFallbackSlots_terminalData_length]
  simp

/-- The direct joined bend compiler emits exactly the complete geometric
source-prefix-plus-retained-fan word for every bend incidence. -/
theorem directSourceFinalBendFallbackRouteDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackRouteDirections decider symbols =
      directSourceFinalBendFallbackGeometricDirections
        decider symbols := by
  have lengthEq :
      (directSourceFinalBendFallbackPrefixWords
        decider symbols).length =
        (directSourceFinalBendFallbackSemanticQueries
          decider symbols).length :=
    (directSourceFinalBendFallbackPrefixWords_terminalData_length
      decider symbols).trans
        (directSourceFinalBendFallbackSemanticQueries_length
          decider symbols).symm
  have positive :
      ∀ query ∈ directSourceFinalBendFallbackSemanticQueries
          decider symbols,
        0 < query.rawLength := by
    rw [← directSourceFinalBendFallbackSuffixQueries_eq]
    exact directSourceFinalBendFallbackSuffixQueries_lengthPositive
      decider symbols
  unfold directSourceFinalBendFallbackRouteDirections
    directSourceFinalBendFallbackSuffixDirections
    directSourceFinalBendFallbackGeometricDirections
  rw [directSourceFinalBendFallbackPrefixDirections_eq,
    directSourceFinalBendFallbackSuffixQueries_eq]
  exact
    FallbackSuffixDirectionCompiler.joined_prefixWords_directions_eq
      (directSourceFinalBendFallbackPrefixWords decider symbols)
      (directSourceFinalBendFallbackSemanticQueries decider symbols)
      lengthEq positive

end LeanTrominoes.PeriodicCNFStripReduction

end
