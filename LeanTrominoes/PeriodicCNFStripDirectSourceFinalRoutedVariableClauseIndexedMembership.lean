/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListSubfamilyLookup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Indexed membership of final routed-variable clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableMembershipStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableMembershipVariableDecidableEq :
    DecidableEq Variable := directSourceVariableDecidableEq

def directSourceFinalRoutedVariableTaggedClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (directSourceFinalRoutedVariableClauses decider symbols).zipIdx
    (directSourceFinalRoutedVariableStart decider symbols)

def directSourceFinalRoutedVariableTaggedSourceClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (deduplicatedClauses (directSourceFormula decider symbols)).zipIdx

theorem directSourceFinalRoutedVariableClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        directSourceFinalRoutedVariableTaggedClauses decider symbols,
      taggedClause ∈
        directSourceFinalRoutedVariableTaggedSourceClauses decider symbols := by
  intro taggedClause taggedMember
  unfold directSourceFinalRoutedVariableTaggedClauses at taggedMember
  unfold directSourceFinalRoutedVariableTaggedSourceClauses
  apply List.mem_zipIdx_iff_getElem?.mpr
  let head :=
    ((directSourceFinalCrossoverClauses decider symbols ++
        directSourceFinalCarrierClauses decider symbols) ++
      directSourceFinalBendClauses decider symbols) ++
      directSourceFinalRoutedClauseClauses decider symbols
  have clausesEq :
      deduplicatedClauses (directSourceFormula decider symbols) =
        head ++ directSourceFinalRoutedVariableClauses decider symbols ++ [] := by
    rw [directSource_deduplicatedClauses_eq_fiveFamilies,
      directSourceFinalFiveFamilyClauses_eq_named]
    simp only [head, List.append_nil, List.append_assoc]
  have indexedMember : taggedClause ∈
      (directSourceFinalRoutedVariableClauses decider symbols).zipIdx
        head.length := by
    unfold head
    unfold directSourceFinalRoutedVariableStart
      directSourceFinalRoutedClauseStart directSourceFinalBendStart
      directSourceFinalCarrierStart at taggedMember
    simpa only [List.length_append, Nat.add_assoc] using taggedMember
  exact IndexedListScan.getElem?_of_eq_append_middle_of_mem_zipIdx
    (deduplicatedClauses (directSourceFormula decider symbols))
    head
    (directSourceFinalRoutedVariableClauses decider symbols)
    []
    clausesEq taggedClause indexedMember

end LeanTrominoes.PeriodicCNFStripReduction

end
