/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorData

/-! # Direct final fallback-family clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Retained carriers use their already-final metadata directions. -/
def directRetainedFinalCarrierClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  retainedFinalPrecomputedClauseQueries
    (directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols)

/-- Retained bends use their already-final metadata directions. -/
def directRetainedFinalBendClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  retainedFinalPrecomputedClauseQueries
    (directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols)

abbrev DirectRetainedFinalCarrierClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalCarrierClauseQueries decider)

abbrev DirectRetainedFinalBendClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalBendClauseQueries decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
