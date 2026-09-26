/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceProjection
import LeanTrominoes.FiniteTemplateQueries

/-! # Native indices selecting the original ordinary SAT literal records -/
noncomputable section
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation Turing

 theorem selectedIndex_lt (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) :
    selectedIndex profile slot < (sourceClauseHeaders profile).length := by
  apply List.findIdx_lt_length_of_exists
  obtain ⟨header, member, equal⟩ := List.mem_map.mp (inheritedSlot_present profile slot active)
  exact ⟨header, member, by simp [equal]⟩

def selectedHeader (profile : DirectedClauseProfile) (slot : SourceLiteralSlot) : Header :=
  (sourceClauseHeaders profile).getD (selectedIndex profile slot) default

theorem selectedHeader_slot (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) :
    inheritedSlot (selectedHeader profile slot) = some slot := by
  unfold selectedHeader
  rw [List.getD_eq_getElem _ _ (selectedIndex_lt profile slot active)]
  exact beq_iff_eq.mp (List.findIdx_getElem (w := selectedIndex_lt profile slot active))

theorem selectedHeader_mem (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (active : sourceSlotNat slot < profile.taggedLiterals.length) :
    selectedHeader profile slot ∈ sourceClauseHeaders profile := by
  unfold selectedHeader
  rw [List.getD_eq_getElem _ _ (selectedIndex_lt profile slot active)]
  exact List.getElem_mem _

def slots (profile : DirectedClauseProfile) : List SourceLiteralSlot :=
  [SourceLiteralSlot.first, .second, .third].take profile.taggedLiterals.length

theorem slots_active (profile : DirectedClauseProfile) (slot : SourceLiteralSlot) :
    slot ∈ slots profile ↔ sourceSlotNat slot < profile.taggedLiterals.length := by
  cases profile <;> cases slot <;> simp [slots, DirectedClauseProfile.taggedLiterals, sourceSlotNat]

def tokenSize : Token → Nat
  | .variable => 0
  | .clause profile => (sourceClauseHeaders profile).length

def tokenOffsets : Token → List Nat
  | .variable => []
  | .clause profile => (slots profile).map (selectedIndex profile)

def queries : List Token → List Nat := FiniteTemplateQueries.queriesFrom tokenSize tokenOffsets 0

def compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields queries := by
  apply FiniteTemplateQueries.compiler
  intro token empty
  cases token with
  | «variable» => rfl
  | clause profile =>
    cases profile <;> simp [tokenOffsets, slots, DirectedClauseProfile.taggedLiterals] at empty

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
end
