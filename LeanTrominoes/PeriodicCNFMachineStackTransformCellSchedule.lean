/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransformCellEmitter
import LeanTrominoes.PeriodicCNFMachineFixedConfigurationEmitterSpec

/-!
# Exact normalized schedule of stack-transform cells

Split the represented positions into the pushed prefix, the shifted equality
interior, and the source-out-of-range tail.  This identifies the three token
blocks emitted by the verified machines with the normalized
`stackTransformCell` operand at every represented position.
-/

noncomputable section

namespace LeanTrominoes

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformCellSchedule

open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Natural-index presentation of the normalized cell program.  Only indices
below `space` are later used. -/
def cellProgram (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space position : Nat) :
    TransitionProgram.Program :=
  if addedPosition : position < transform.added.length then
    BoundedMachineProgram.nextStackCellIs (tm := tm) stack position
      (some transform.added[position])
  else
    let source := position - transform.added.length + transform.discard
    if sourcePosition : source < space then
      BoundedMachineProgram.stackCellsEqual (tm := tm) stack source position
    else
      BoundedMachineProgram.nextStackCellIs (tm := tm) stack position none

@[simp]
theorem cellProgram_eq_stackTransformCell (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) {space position : Nat}
    (represented : position < space) :
    cellProgram (tm := tm) stack transform space position =
      BoundedMachineProgram.stackTransformCell (tm := tm) stack transform
        ⟨position, represented⟩ := by
  rfl

def cellTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.range space).flatMap fun position =>
    ofProgram (cellProgram (tm := tm) stack transform space position)

def normalizedCellTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.finRange space).flatMap fun position =>
    ofProgram
      (BoundedMachineProgram.stackTransformCell (tm := tm) stack transform
        position)

theorem normalizedCellTokens_eq_cellTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    normalizedCellTokens (tm := tm) stack transform space =
      cellTokens (tm := tm) stack transform space := by
  unfold normalizedCellTokens cellTokens
  calc
    (List.finRange space).flatMap (fun position =>
        ofProgram
          (BoundedMachineProgram.stackTransformCell (tm := tm) stack
            transform position)) =
        ((List.finRange space).map Fin.val).flatMap (fun position =>
          ofProgram (cellProgram (tm := tm) stack transform space position)) := by
      rw [List.flatMap_map]
      apply List.flatMap_congr
      intro position _
      rw [cellProgram_eq_stackTransformCell stack transform position.isLt]
    _ = _ := by
      rw [BoundedMachineOneHotEmitter.finRange_values]

theorem flatMap_range_if_lt {Target : Type} (total limit : Nat)
    (function : Nat → List Target) :
    (List.range total).flatMap
        (fun position => if position < limit then function position else []) =
      (List.range (min total limit)).flatMap function := by
  induction total with
  | zero => simp
  | succ total induction =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        induction]
      by_cases below : total < limit
      · have oldMin : min total limit = total := Nat.min_eq_left (by omega)
        have newMin : min (total + 1) limit = total + 1 :=
          Nat.min_eq_left (by omega)
        rw [if_pos below, oldMin, newMin, List.range_succ,
          List.flatMap_append, List.flatMap_singleton]
      · have reached : limit ≤ total := Nat.le_of_not_gt below
        rw [if_neg below, Nat.min_eq_right reached,
          Nat.min_eq_right (by omega)]
        simp

theorem range_split_min (start total : Nat) :
    List.range total =
      List.range (min start total) ++
        (List.range (total - start)).map fun offset => start + offset := by
  by_cases fits : start ≤ total
  · rw [Nat.min_eq_left fits,
      BoundedMachineFixedConfigurationEmitter.range_split fits]
  · have totalLe : total ≤ start := Nat.le_of_not_ge fits
    rw [Nat.min_eq_right totalLe]
    simp [Nat.sub_eq_zero_of_le totalLe]

def addedAt (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (position : Nat) : List Token :=
  if addedPosition : position < transform.added.length then
    ofProgram
      (BoundedMachineProgram.nextStackCellIs (tm := tm) stack position
        (some transform.added[position]))
  else []

theorem addedTokens_eq (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    BoundedMachineStackTransformPrefixEmitter.addedTokens (tm := tm) stack
        transform space =
      (List.range (min transform.added.length space)).flatMap
        (addedAt (tm := tm) stack transform) := by
  unfold BoundedMachineStackTransformPrefixEmitter.addedTokens
  calc
    (List.finRange transform.added.length).flatMap (fun position =>
        if position.val < space then
          ofProgram
            (BoundedMachineProgram.nextStackCellIs (tm := tm) stack
              position.val (some transform.added[position]))
        else []) =
      ((List.finRange transform.added.length).map Fin.val).flatMap
        (fun position =>
          if position < space then
            addedAt (tm := tm) stack transform position
          else []) := by
        rw [List.flatMap_map]
        apply List.flatMap_congr
        intro position _
        simp [addedAt, position.isLt]
    _ = (List.range transform.added.length).flatMap
        (fun position =>
          if position < space then
            addedAt (tm := tm) stack transform position
          else []) := by
        rw [BoundedMachineOneHotEmitter.finRange_values]
    _ = _ := flatMap_range_if_lt _ _ _

def equalityCount {stack : tm.K}
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : Nat :=
  space - BoundedMachineStackTransformCellEmitter.cutoff transform

def tailCount {stack : tm.K}
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : Nat :=
  (space - transform.added.length) - equalityCount transform space

def equalityRangeTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.range (equalityCount transform space)).flatMap fun position =>
    ofProgram
      (BoundedMachineProgram.stackCellsEqual (tm := tm) stack
        (position + transform.discard)
        (position + transform.added.length))

def tailRangeTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.range (tailCount transform space)).flatMap fun position =>
    ofProgram
      (BoundedMachineProgram.nextStackCellIs (tm := tm) stack
        (transform.added.length + equalityCount transform space + position)
        none)

theorem equalityTokens_eq (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    BoundedMachineStackTransformPrefixEmitter.equalityTokens (tm := tm) stack
        transform space =
      equalityRangeTokens (tm := tm) stack transform space := by
  rfl

theorem tailTokens_eq (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    BoundedMachineStackTransformCellEmitter.tailTokens (tm := tm) stack
        transform space =
      tailRangeTokens (tm := tm) stack transform space := by
  unfold BoundedMachineStackTransformCellEmitter.tailTokens tailRangeTokens
    tailCount equalityCount BoundedMachineStackTransformCellEmitter.tailProgram
  rw [BoundedMachineBivariateStack.positionRangeTokens_nextStackCellIs]

/-- The natural-index cell list splits exactly into the three emitted blocks. -/
theorem cellTokens_eq_parts (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    cellTokens (tm := tm) stack transform space =
      (List.range (min transform.added.length space)).flatMap
          (addedAt (tm := tm) stack transform) ++
        equalityRangeTokens (tm := tm) stack transform space ++
        tailRangeTokens (tm := tm) stack transform space := by
  let added := transform.added.length
  let cut := BoundedMachineStackTransformCellEmitter.cutoff transform
  let equal := space - cut
  have addedEq : added = transform.added.length := rfl
  have cutEq : cut =
      max transform.added.length transform.discard := rfl
  have equalEq : equal =
      space - max transform.added.length transform.discard := by
    rw [show equal = space - cut by rfl, cutEq]
  have equalGlobal : equal =
      space - BoundedMachineStackTransformCellEmitter.cutoff transform := rfl
  have addedLeCut : added ≤ cut := by
    unfold added cut BoundedMachineStackTransformCellEmitter.cutoff
      BoundedMachineStackTransformPrefixEmitter.cutoff
    omega
  have equalLeRemaining : equal ≤ space - added := by omega
  unfold cellTokens
  rw [range_split_min added space, List.flatMap_append, List.flatMap_map]
  have prefixEq :
      (List.range (min added space)).flatMap
          (fun position =>
            ofProgram (cellProgram (tm := tm) stack transform space position)) =
        (List.range (min transform.added.length space)).flatMap
          (addedAt (tm := tm) stack transform) := by
    apply List.flatMap_congr
    intro position member
    have belowMin := List.mem_range.mp member
    have belowAdded : position < transform.added.length := by
      change position < added
      omega
    simp [cellProgram, addedAt, belowAdded]
  rw [prefixEq, List.append_assoc]
  simp only [List.append_cancel_left_eq]
  change (List.range (space - added)).flatMap
      (fun offset =>
        ofProgram
          (cellProgram (tm := tm) stack transform space
            (added + offset))) = _
  rw [BoundedMachineFixedConfigurationEmitter.range_split equalLeRemaining,
    List.flatMap_append, List.flatMap_map]
  have interiorEq :
      (List.range equal).flatMap (fun position =>
          ofProgram
            (cellProgram (tm := tm) stack transform space
              (added + position))) =
        equalityRangeTokens (tm := tm) stack transform space := by
    unfold equalityRangeTokens equalityCount
    change _ = (List.range equal).flatMap _
    apply List.flatMap_congr
    intro position member
    have belowEqual := List.mem_range.mp member
    have belowEqual' : position <
        space - max transform.added.length transform.discard := by
      simpa [equalEq] using belowEqual
    have notAdded : ¬ added + position < transform.added.length := by
      change ¬ added + position < added
      omega
    have sourceBase :
        added + position - transform.added.length = position := by
      rw [addedEq]
      omega
    have sourceRepresented :
        added + position - transform.added.length + transform.discard <
          space := by
      rw [sourceBase]
      have discardLe : transform.discard ≤
          max transform.added.length transform.discard := Nat.le_max_right _ _
      omega
    unfold cellProgram
    rw [dif_neg notAdded, dif_pos sourceRepresented]
    have sourceEq :
        added + position - transform.added.length + transform.discard =
          position + transform.discard := by rw [sourceBase]
    have targetEq :
        added + position = position + transform.added.length := by
      rw [addedEq]
      omega
    rw [sourceEq, targetEq]
  rw [interiorEq]
  have tailEq :
      (List.range ((space - added) - equal)).flatMap (fun offset =>
          ofProgram
            (cellProgram (tm := tm) stack transform space
              (added + (equal + offset)))) =
        tailRangeTokens (tm := tm) stack transform space := by
    unfold tailRangeTokens tailCount equalityCount
    change _ = (List.range ((space - added) - equal)).flatMap _
    apply List.flatMap_congr
    intro position member
    have belowTail := List.mem_range.mp member
    have notAdded :
        ¬ added + (equal + position) < transform.added.length := by
      change ¬ added + (equal + position) < added
      omega
    have sourceBase :
        added + (equal + position) - transform.added.length =
          equal + position := by
      rw [addedEq]
      omega
    have sourceOutside :
        ¬ (added + (equal + position) - transform.added.length +
          transform.discard < space) := by
      by_cases order : transform.added.length ≤ transform.discard
      · have equalCase : equal = space - transform.discard := by
          rw [equalEq, max_eq_right order]
        rw [sourceBase, equalCase]
        omega
      · have reverse : transform.discard < transform.added.length :=
          Nat.lt_of_not_ge order
        have equalCase : equal = space - transform.added.length := by
          rw [equalEq, max_eq_left (Nat.le_of_lt reverse)]
        have noTail : (space - added) - equal = 0 := by
          rw [addedEq, equalCase]
          exact Nat.sub_self _
        omega
    unfold cellProgram
    rw [dif_neg notAdded, dif_neg sourceOutside]
    have positionEq : added + (equal + position) =
        transform.added.length +
          (space - BoundedMachineStackTransformCellEmitter.cutoff transform) +
          position := by
      rw [addedEq, equalGlobal]
      omega
    rw [positionEq]
  rw [tailEq]

/-- The verified emitter's three blocks are token-for-token the complete
normalized represented-cell schedule. -/
theorem emitted_eq_normalizedCellTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    BoundedMachineStackTransformCellEmitter.emitted (tm := tm) stack
        transform space =
      normalizedCellTokens (tm := tm) stack transform space := by
  unfold BoundedMachineStackTransformCellEmitter.emitted
    BoundedMachineStackTransformPrefixEmitter.emitted
  rw [addedTokens_eq, equalityTokens_eq, tailTokens_eq,
    normalizedCellTokens_eq_cellTokens, cellTokens_eq_parts]

end BoundedMachineStackTransformCellSchedule
end PeriodicCNF
end LeanTrominoes
