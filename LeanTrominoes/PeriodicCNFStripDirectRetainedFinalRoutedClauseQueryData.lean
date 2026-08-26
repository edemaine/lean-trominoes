/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorData

/-! # Direct final routed-clause query blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One stable direct query for a normalized routed source-clause profile. -/
def directRetainedFinalRoutedClauseQueryBlock
    (profile : ClauseProfile) :
    List RetainedFinalCopiedClauseQuery :=
  [retainedFinalDirectRoutedClauseQuery
    (currentizeRoutedClauseProfiles profile)]

/-- One stable direct routed-clause query per exact source clause profile. -/
def directRetainedFinalRoutedClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  (directSourceFormulaClauseProfiles decider symbols).flatMap
    directRetainedFinalRoutedClauseQueryBlock

abbrev DirectRetainedFinalRoutedClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalRoutedClauseQueries decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
