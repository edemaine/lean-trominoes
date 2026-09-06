/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSemanticSlotBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedClauseSemantics

/-! # Semantic occurrence-slot blocks of direct final carrier clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierSemanticSlotBlockFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierSemanticSlotBlockFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

/-- Each indexed direct carrier clause contributes the two named semantic
occurrence slots of its tagged physical link. -/
theorem directSourceFinalCarrierSemanticOccurrenceSlotBlocks_eq_taggedLinks
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierSemanticOccurrenceSlotBlocks decider symbols =
      (directSourceFinalCarrierTaggedLinks decider symbols).map fun tagged =>
        [finalCarrierSemanticOccurrenceSlotAt
            (directThreeCNFSourceFormula decider symbols)
            tagged.1 tagged.2 0,
          finalCarrierSemanticOccurrenceSlotAt
            (directThreeCNFSourceFormula decider symbols)
            tagged.1 tagged.2 1] := by
  have taggedClausesEq :=
    directSourceFinalCarrierTaggedClauses_eq decider symbols
  unfold directSourceFinalCarrierSemanticOccurrenceSlotBlocks
  rw [taggedClausesEq, List.map_map]
  apply List.map_congr_left
  intro tagged _
  dsimp only [Function.comp_apply]
  have clauseEquality : directFinalCarrierTaggedClauseVariableDecidableEq =
      @PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (ThreeCNFVariable Nat) directSourceFinalStructuralBaseDecidableEq :=
    Subsingleton.elim _ _
  rw [clauseEquality]
  exact directSourceFinalCarrierSemanticOccurrenceSlotBlock_eq decider symbols tagged

end LeanTrominoes.PeriodicCNFStripReduction

end
