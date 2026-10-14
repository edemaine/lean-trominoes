/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorData

/-! # Direct final fallback-family clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
