/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFacts
import LeanTrominoes.PeriodicThreeSATThreeRoutedClauseLookup

/-! # Indexed membership of final routed clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseMembershipStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseMembershipVariableDecidableEq :
    DecidableEq Variable := directSourceVariableDecidableEq

def directSourceFinalRoutedClauseTaggedClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (directSourceFinalRoutedClauseClauses decider symbols).zipIdx
    (directSourceFinalRoutedClauseStart decider symbols)

def directSourceFinalRoutedClauseTaggedSourceClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (deduplicatedClauses (directSourceFormula decider symbols)).zipIdx

theorem directSourceFinalRoutedClauseClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        directSourceFinalRoutedClauseTaggedClauses decider symbols,
      taggedClause ∈
        directSourceFinalRoutedClauseTaggedSourceClauses decider symbols := by
  intro taggedClause taggedMember
  unfold directSourceFinalRoutedClauseTaggedClauses at taggedMember
  unfold directSourceFinalRoutedClauseTaggedSourceClauses
  apply List.mem_zipIdx_iff_getElem?.mpr
  have lookup :=
    PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses_getElem?_of_mem_zipIdx
      (directThreeCNFSourceFormula decider symbols)
      (directThreeCNFSource_isLocal decider symbols)
      (directThreeCNFSource_widthAtMostThree decider symbols)
      (directThreeCNFSource_clausesNonempty decider symbols)
      (directThreeCNFSource_positiveOffsets decider symbols)
      taggedClause
      (by
        simpa only [directSourceFinalRoutedClauseClauses,
          directSourceFinalRoutedClauseStart,
          directSourceFinalBendStart,
          directSourceFinalCarrierStart,
          directSourceFinalCrossoverClauses,
          directSourceFinalCarrierClauses,
          directSourceFinalBendClauses]
          using taggedMember)
  rw [directSourceFormula_eq_finalNormalized decider symbols]
  simpa only [directSourceFinalNormalizedFormula] using lookup

end LeanTrominoes.PeriodicCNFStripReduction

end
