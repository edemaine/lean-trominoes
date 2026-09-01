/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeCompiler

/-! # Semantics of direct final canonical element degrees -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

@[simp] theorem directSourceFinalVariableElementDegreeBlock_length
    (pair : GroupedVariableFanSlot) :
    (directSourceFinalVariableElementDegreeBlock pair).length =
      match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
      | .fixedRed => 3
      | .fixedGreen | .fixedBlue => 1 := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [directSourceFinalVariableElementDegreeBlock, kindEq]

@[simp] theorem directSourceFinalClauseElementDegreeBlock_length
    (descriptor : FormulaShapeDirectionOrdering.Token) :
    (directSourceFinalClauseElementDegreeBlock descriptor).length =
      match descriptor with
      | .clause _ => 4
      | .variable => 0 := by
  cases descriptor with
  | «variable» => rfl
  | clause profile => cases profile <;> rfl

theorem directSourceFinalVariableElementDegreeBlock_valid
    (pair : GroupedVariableFanSlot)
    (degree : Nat)
    (member : degree ∈ directSourceFinalVariableElementDegreeBlock pair) :
    degree = 2 ∨ degree = 3 := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [directSourceFinalVariableElementDegreeBlock, kindEq] at member <;>
    simp [member]

theorem directSourceFinalClauseElementDegreeBlock_valid
    (descriptor : FormulaShapeDirectionOrdering.Token)
    (degree : Nat)
    (member : degree ∈ directSourceFinalClauseElementDegreeBlock descriptor) :
    degree = 2 ∨ degree = 3 := by
  cases descriptor with
  | «variable» => simp [directSourceFinalClauseElementDegreeBlock] at member
  | clause profile =>
      cases profile <;>
        simp [directSourceFinalClauseElementDegreeBlock] at member <;>
        omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The emitted column is definitionally three copies of the common
variable-prefix/clause-suffix degree pattern, matching RGB order. -/
theorem directSourceFinalCanonicalElementDegrees_eq_three_colors
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      directSourceFinalOneColorElementDegrees decider symbols ++
        directSourceFinalOneColorElementDegrees decider symbols ++
        directSourceFinalOneColorElementDegrees decider symbols := by
  unfold directSourceFinalCanonicalElementDegrees
    directSourceFinalGreenBlueElementDegrees
  simp [List.append_assoc]

private theorem directSourceFinalVariableElementDegrees_valid
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalVariableElementDegrees decider symbols,
      degree = 2 ∨ degree = 3 := by
  intro degree member
  unfold directSourceFinalVariableElementDegrees at member
  simp only [FiniteUnaryFieldBlockMap.values,
    List.mem_flatMap] at member
  obtain ⟨pair, _pairMember, localMember⟩ := member
  exact directSourceFinalVariableElementDegreeBlock_valid
    pair degree localMember

private theorem directSourceFinalClauseElementDegrees_valid
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalClauseElementDegrees decider symbols,
      degree = 2 ∨ degree = 3 := by
  intro degree member
  unfold directSourceFinalClauseElementDegrees at member
  simp only [FiniteUnaryFieldBlockMap.values,
    List.mem_flatMap] at member
  obtain ⟨descriptor, _descriptorMember, localMember⟩ := member
  exact directSourceFinalClauseElementDegreeBlock_valid
    descriptor degree localMember

private theorem directSourceFinalOneColorElementDegrees_valid
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalOneColorElementDegrees decider symbols,
      degree = 2 ∨ degree = 3 := by
  intro degree member
  unfold directSourceFinalOneColorElementDegrees at member
  rw [List.mem_append] at member
  rcases member with variableMember | clauseMember
  · exact directSourceFinalVariableElementDegrees_valid
      decider symbols degree variableMember
  · exact directSourceFinalClauseElementDegrees_valid
      decider symbols degree clauseMember

private theorem threeCopies_valid
    (values : List Nat)
    (valid : ∀ degree ∈ values, degree = 2 ∨ degree = 3) :
    ∀ degree ∈ values ++ values ++ values,
      degree = 2 ∨ degree = 3 := by
  intro degree member
  simp only [List.mem_append] at member
  rcases member with (first | second) | third
  · exact valid degree first
  · exact valid degree second
  · exact valid degree third

/-- Every compiled canonical element degree satisfies the exact promise
required by counted contraction. -/
theorem directSourceFinalCanonicalElementDegrees_valid
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalCanonicalElementDegrees decider symbols,
      degree = 2 ∨ degree = 3 := by
  rw [directSourceFinalCanonicalElementDegrees_eq_three_colors]
  exact threeCopies_valid
    (directSourceFinalOneColorElementDegrees decider symbols)
    (directSourceFinalOneColorElementDegrees_valid decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
