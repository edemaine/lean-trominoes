/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListSubfamilyLookup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Indexed membership of final crossover clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverMembershipStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverMembershipVariableDecidableEq :
    DecidableEq Variable := directSourceVariableDecidableEq

def directSourceFinalCrossoverTaggedClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (directSourceFinalCrossoverClauses decider symbols).zipIdx 0

def directSourceFinalCrossoverTaggedSourceClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (deduplicatedClauses (directSourceFormula decider symbols)).zipIdx

theorem directSourceFinalCrossoverClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        directSourceFinalCrossoverTaggedClauses decider symbols,
      taggedClause ∈
        directSourceFinalCrossoverTaggedSourceClauses decider symbols := by
  intro taggedClause taggedMember
  unfold directSourceFinalCrossoverTaggedClauses at taggedMember
  unfold directSourceFinalCrossoverTaggedSourceClauses
  apply List.mem_zipIdx_iff_getElem?.mpr
  have clausesEq :
      deduplicatedClauses (directSourceFormula decider symbols) =
        [] ++ directSourceFinalCrossoverClauses decider symbols ++
          (directSourceFinalCarrierClauses decider symbols ++
            directSourceFinalBendClauses decider symbols ++
            directSourceFinalRoutedClauseClauses decider symbols ++
            directSourceFinalRoutedVariableClauses decider symbols) := by
    rw [directSource_deduplicatedClauses_eq_fiveFamilies,
      directSourceFinalFiveFamilyClauses_eq_named]
    simp only [List.nil_append, List.append_assoc]
  exact IndexedListScan.getElem?_of_eq_append_middle_of_mem_zipIdx
    (deduplicatedClauses (directSourceFormula decider symbols))
    []
    (directSourceFinalCrossoverClauses decider symbols)
    (directSourceFinalCarrierClauses decider symbols ++
      directSourceFinalBendClauses decider symbols ++
      directSourceFinalRoutedClauseClauses decider symbols ++
      directSourceFinalRoutedVariableClauses decider symbols)
    clausesEq taggedClause (by simpa only [List.length_nil] using taggedMember)

end LeanTrominoes.PeriodicCNFStripReduction

end
