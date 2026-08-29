/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixQueryCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixQueryLength
import LeanTrominoes.RetainedAngularBendTerminalCoordinateData
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnSemantics

/-! # Semantic fallback-suffix queries of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackSuffixSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackSuffixSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Compiler-ordered semantic terminal data of all untranslated bends. -/
def directSourceFinalBendFallbackTerminalData
    (symbols : List encoding.Γ) : List RetainedTerminalData :=
  baseBendTerminalData (directSourceFormula decider symbols)

theorem directSourceFinalBendFallbackTerminalDirections_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackTerminalDirections decider symbols =
      (directSourceFinalBendFallbackTerminalData
        decider symbols).map Prod.fst := by
  unfold directSourceFinalBendFallbackTerminalDirections
    directSourceFinalBendFallbackTerminalData
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
    directSourceBaseBendTerminalDirectionRanks
    baseBendTerminalData terminalDataDirectionRanks
  simp [List.map_flatMap, Function.comp_def]

theorem directSourceFinalBendFallbackTerminalRadialLengths_eq
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalRadialLengths decider symbols =
      (directSourceFinalBendFallbackTerminalData
        decider symbols).map Prod.snd := by
  unfold directSourceFinalBendFallbackTerminalData
    directSourceBaseBendTerminalRadialLengths
    baseBendTerminalData terminalDataRadialLengths
  simp [List.map_flatMap]

/-- The direct query columns reconstruct the ordinary policy, exact terminal
data, and selected final occurrence slots in one semantic zipper. -/
def directSourceFinalBendFallbackSemanticQueries
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  let terminals :=
    directSourceFinalBendFallbackTerminalData decider symbols
  FallbackSuffixQueries.alignedQueries
    (List.replicate terminals.length .ordinary)
    terminals
    (directSourceFinalBendOccurrenceSlots decider symbols)

theorem directSourceFinalBendFallbackSuffixQueries_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackSuffixQueries decider symbols =
      directSourceFinalBendFallbackSemanticQueries decider symbols := by
  unfold directSourceFinalBendFallbackSuffixQueries
    directSourceFinalBendFallbackHeaderRoles
    directSourceFinalBendFallbackSemanticQueries
  rw [directSourceFinalBendFallbackTerminalDirections_eq,
    directSourceFinalBendFallbackTerminalRadialLengths_eq]
  exact
    FallbackSuffixQueryColumns.alignedQueries_bendRoles_terminalData
      (directSourceFinalBendFallbackTerminalData decider symbols)
      (directSourceFinalBendOccurrenceSlots decider symbols)

theorem directSourceFinalBendFallbackTerminalData_lengthPositive
    (symbols : List encoding.Γ) :
    ∀ terminal ∈
        directSourceFinalBendFallbackTerminalData decider symbols,
      0 < terminal.2 := by
  intro terminal terminalMember
  unfold directSourceFinalBendFallbackTerminalData
    baseBendTerminalData at terminalMember
  rcases List.mem_flatMap.mp terminalMember with
    ⟨descriptor, descriptorMember, terminalMember⟩
  rcases List.mem_flatMap.mp terminalMember with
    ⟨routeBend, routeBendMember, terminalMember⟩
  exact FallbackSuffixQueries.bendRouteTerminalDataBlock_lengthPositive
    routeBend.incomingPort routeBend.outgoingPort
    terminal terminalMember

/-- Every direct bend fallback query has a positive raw terminal length. -/
theorem directSourceFinalBendFallbackSuffixQueries_lengthPositive
    (symbols : List encoding.Γ) :
    ∀ query ∈ directSourceFinalBendFallbackSuffixQueries decider symbols,
      0 < query.rawLength := by
  rw [directSourceFinalBendFallbackSuffixQueries_eq]
  unfold directSourceFinalBendFallbackSemanticQueries
  exact FallbackSuffixQueries.alignedQueries_lengthPositive _ _ _
    (directSourceFinalBendFallbackTerminalData_lengthPositive
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
