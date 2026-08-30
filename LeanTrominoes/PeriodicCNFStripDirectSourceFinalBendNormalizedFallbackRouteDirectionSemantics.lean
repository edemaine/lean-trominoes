/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackPrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackSuffixSemantics
import LeanTrominoes.RetainedAngularFanNormalizedFallbackJoinedDirectionSemantics

/-! # Complete normalized fallback direction words of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedFallbackRouteSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendNormalizedFallbackRouteSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete pre-cancellation words obtained by pairing every scaled prefix
with its aligned normalized ordinary retained-fan suffix query. -/
def directSourceFinalBendPreCancellationGeometricDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.retainedOrdinaryJoinedDirections
    ((directSourceFinalBendFallbackPrefixWords decider symbols).zip
      (directSourceFinalBendFallbackSemanticQueries decider symbols))

/-- Apply bounded junction cancellation to the geometric bend-word batch. -/
def directSourceFinalBendNormalizedFallbackGeometricDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  BoundedDelimitedDirectionCancellation.output
    (directSourceFinalBendPreCancellationGeometricDirections
      decider symbols)

private theorem directSourceFinalBendNormalizedFallbackPrefixWords_terminalData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackPrefixWords decider symbols).length =
      (directSourceFinalBendFallbackTerminalData decider symbols).length := by
  unfold directSourceFinalBendFallbackPrefixWords
    directSourceFinalBendFallbackTerminalData
    PeriodicEightOccurrenceSplit.baseBendTerminalData
  simp [List.length_flatMap]

private theorem directSourceFinalBendNormalizedFallbackSlots_terminalData_length
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

private theorem directSourceFinalBendNormalizedFallbackSemanticQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackSemanticQueries decider symbols).length =
      (directSourceFinalBendFallbackTerminalData decider symbols).length := by
  unfold directSourceFinalBendFallbackSemanticQueries
  rw [FallbackSuffixQueries.alignedQueries_length,
    List.length_replicate,
    directSourceFinalBendNormalizedFallbackSlots_terminalData_length]
  simp

/-- The joined compiler emits exactly the geometric batch before bounded
junction cancellation. -/
theorem directSourceFinalBendPreCancellationRouteDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalBendPreCancellationRouteDirections decider symbols =
      directSourceFinalBendPreCancellationGeometricDirections
        decider symbols := by
  have lengthEq :
      (directSourceFinalBendFallbackPrefixWords decider symbols).length =
        (directSourceFinalBendFallbackSemanticQueries
          decider symbols).length :=
    (directSourceFinalBendNormalizedFallbackPrefixWords_terminalData_length
      decider symbols).trans
        (directSourceFinalBendNormalizedFallbackSemanticQueries_length
          decider symbols).symm
  unfold directSourceFinalBendPreCancellationRouteDirections
    directSourceFinalBendNormalizedFallbackSuffixDirections
    directSourceFinalBendPreCancellationGeometricDirections
  rw [directSourceFinalBendFallbackPrefixDirections_eq,
    directSourceFinalBendFallbackSuffixQueries_eq]
  exact
    NormalizedFallbackSuffixDirectionCompiler.joined_ordinary_prefixWords_directions_eq
      (directSourceFinalBendFallbackPrefixWords decider symbols)
      (directSourceFinalBendFallbackSemanticQueries decider symbols)
      lengthEq
      (directSourceFinalBendFallbackSemanticQueries_kind decider symbols)
      (directSourceFinalBendFallbackSemanticQueries_lengthPositive
        decider symbols)

/-- The composed compiler agrees with bounded cancellation of the complete
geometric pre-cancellation batch. -/
theorem directSourceFinalBendNormalizedFallbackRouteDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackRouteDirections decider symbols =
      directSourceFinalBendNormalizedFallbackGeometricDirections
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackRouteDirections
    directSourceFinalBendNormalizedFallbackGeometricDirections
  rw [directSourceFinalBendPreCancellationRouteDirections_eq_geometric]

end LeanTrominoes.PeriodicCNFStripReduction

end
