/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskData
import LeanTrominoes.RetainedAngularFanFallbackHeaderRoleCompiler
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnCompiler
import LeanTrominoes.RetainedTerminalDirectionRankDecoderCompiler

/-! # Direct-source fallback-suffix query-column targets -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackSuffixQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalCarrierFallbackTerminalCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  retainedFinalTerminalCoordinatesFrom
    (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
      (directSourceFormula decider symbols))
    (directSourceFinalCarrierStart decider symbols)
    (directSourceFinalCarrierClauses decider symbols)

def directSourceFinalBendFallbackTerminalCoordinates
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  retainedFinalTerminalCoordinatesFrom
    (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
      (directSourceFormula decider symbols))
    (directSourceFinalBendStart decider symbols)
    (directSourceFinalBendClauses decider symbols)

def directSourceFinalCarrierFallbackTerminalDirections
    (symbols : List encoding.Γ) : List RetainedTerminalDirection :=
  RetainedTerminalDirectionRankDecoder.directionsOfRanks
    (directSourceCarrierTerminalDirectionRanks decider symbols)

def directSourceFinalBendFallbackTerminalDirections
    (symbols : List encoding.Γ) : List RetainedTerminalDirection :=
  RetainedTerminalDirectionRankDecoder.directionsOfRanks
    (directSourceBaseBendTerminalDirectionRanks decider symbols)

def directSourceFinalCarrierFallbackHeaderRoles
    (symbols : List encoding.Γ) :
    List FallbackSuffixQueryFormatter.HeaderRole :=
  FallbackSuffixHeaderRoles.carrierRoles
    (directSourceFinalCarrierFallbackTerminalDirections decider symbols)

def directSourceFinalBendFallbackHeaderRoles
    (symbols : List encoding.Γ) :
    List FallbackSuffixQueryFormatter.HeaderRole :=
  FallbackSuffixHeaderRoles.bendRoles
    (directSourceFinalBendFallbackTerminalDirections decider symbols)

def directSourceFinalCarrierFallbackSuffixQueries
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  FallbackSuffixQueryColumns.alignedQueries
    (directSourceFinalCarrierFallbackHeaderRoles decider symbols)
    (directSourceCarrierTerminalRadialLengths decider symbols)
    (directSourceFinalCarrierOccurrenceSlots decider symbols)

def directSourceFinalBendFallbackSuffixQueries
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  FallbackSuffixQueryColumns.alignedQueries
    (directSourceFinalBendFallbackHeaderRoles decider symbols)
    (directSourceBaseBendTerminalRadialLengths decider symbols)
    (directSourceFinalBendOccurrenceSlots decider symbols)

def directSourceFinalCarrierFallbackSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  FallbackSuffixDirectionCompiler.Batch.directions
    (directSourceFinalCarrierFallbackSuffixQueries decider symbols)

def directSourceFinalBendFallbackSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  FallbackSuffixDirectionCompiler.Batch.directions
    (directSourceFinalBendFallbackSuffixQueries decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
