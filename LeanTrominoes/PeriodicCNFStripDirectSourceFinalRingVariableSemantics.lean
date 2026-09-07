/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedRingAtomSemantics

/-! # Numeric codes of actual compass and separator variables -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open OccurrenceSplitRing PeriodicEightOccurrenceSplit PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance ringVariableSemanticStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance ringVariableSemanticVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Interpret an actual ring variable in the compiler's angular slot
numbering. Actual compass indices start at northwest; numeric slots start at
east. Both encodings reserve eight for the separator. -/
noncomputable def directSourceFinalRingVariableCode
    (symbols : List encoding.Γ)
    (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable)) : Nat :=
  directSourceFinalInheritedRingCode decider symbols atom.1
    (if atom.2.1 = 8 then 8 else (portOfIndex atom.2.1).angularRank)

/-- The semantic code of every actual ring copy is its source identity paired
with the compiler's angular vertex slot. -/
theorem directSourceFinalRingVariableCode_ringCopy
    (symbols : List encoding.Γ) (atom : WrappedPeriodicPlanarSATVariable Variable)
    (vertex : RingVertex) :
    directSourceFinalRingVariableCode decider symbols (ringCopy atom vertex) =
      directSourceFinalInheritedRingCode decider symbols atom (directFinalCycleRingVertexSlot vertex).val := by
  cases vertex with
  | separator => rfl
  | port port => cases port <;> rfl

private theorem cycleRingSlot_val_eq_iff (first second : RingVertex) :
    (directFinalCycleRingVertexSlot first).val = (directFinalCycleRingVertexSlot second).val ↔
      first = second := by
  have injective : Function.Injective directFinalCycleRingVertexSlot := by native_decide
  exact ⟨fun equal => injective (Fin.ext equal), fun equal => congrArg (fun vertex => (directFinalCycleRingVertexSlot vertex).val) equal⟩

private theorem ringCopy_fst {Atom : Type*} (atom : Atom) (vertex : RingVertex) :
    (ringCopy atom vertex).1 = atom := by
  cases vertex <;> rfl

private theorem ringCopy_eq_iff {Atom : Type*} (first second : Atom)
    (firstVertex secondVertex : RingVertex) :
    ringCopy first firstVertex = ringCopy second secondVertex ↔
      first = second ∧ firstVertex = secondVertex := by
  constructor
  · intro equal
    have atomsEq := congrArg Prod.fst equal
    simp only [ringCopy_fst] at atomsEq
    subst second
    exact ⟨rfl, ringCopy_injective first equal⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Numeric equality is exactly equality of actual ring variables, across
all compass ports and the separator, for represented source atoms. -/
theorem directSourceFinalRingVariableCode_eq_iff_ringCopy
    (symbols : List encoding.Γ) (first second : WrappedPeriodicPlanarSATVariable Variable)
    (firstMember : first ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences)
    (secondMember : second ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences)
    (firstVertex secondVertex : RingVertex) :
    directSourceFinalRingVariableCode decider symbols (ringCopy first firstVertex) =
        directSourceFinalRingVariableCode decider symbols (ringCopy second secondVertex) ↔
      ringCopy first firstVertex = ringCopy second secondVertex := by
  rw [directSourceFinalRingVariableCode_ringCopy, directSourceFinalRingVariableCode_ringCopy,
    directSourceFinalInheritedRingCode_eq_iff decider symbols first second firstMember secondMember
      _ _ (directFinalCycleRingVertexSlot firstVertex).isLt (directFinalCycleRingVertexSlot secondVertex).isLt]
  simp only [Prod.mk.injEq, and_true, cycleRingSlot_val_eq_iff, ringCopy_eq_iff]

/-- A genuine bounded angular slot codes the compass copy it actually selects. -/
theorem directSourceFinalRingVariableCode_angularCopy
    (symbols : List encoding.Γ) (atom : WrappedPeriodicPlanarSATVariable Variable)
    (slot : Nat) (slotLt : slot < 8) :
    directSourceFinalRingVariableCode decider symbols (copy atom (angularPortOfIndex slot)) =
      directSourceFinalInheritedRingCode decider symbols atom slot := by
  change directSourceFinalRingVariableCode decider symbols (ringCopy atom (.port (angularPortOfIndex slot))) = _
  rw [directSourceFinalRingVariableCode_ringCopy]
  change directSourceFinalInheritedRingCode decider symbols atom (angularPortOfIndex slot).angularRank = _
  rw [angularRank_angularPortOfIndex slotLt]

end LeanTrominoes.PeriodicCNFStripReduction

end
