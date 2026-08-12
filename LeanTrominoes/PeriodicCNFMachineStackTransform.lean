import LeanTrominoes.PeriodicCNFMachineFields

/-!
# Normalized bounded-stack transformations

An atomic TM2 statement may push and pop several times before reaching a
`goto` or `halt`.  Such a sequence has a compact normal form: prepend a finite
list of known symbols, then drop a fixed number of cells from the original
stack.  This file defines that normal form and a transition expression whose
size is linear in the selected stack width.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Normal form for the effect of one atomic statement on a stack. -/
structure StackTransform (Symbol : Type*) where
  added : List Symbol
  discard : Nat
  deriving DecidableEq, Repr

namespace StackTransform

/-- Apply a normalized transform to an ordinary variable-length stack. -/
def apply {Symbol : Type*} (transform : StackTransform Symbol)
    (symbols : List Symbol) : List Symbol :=
  transform.added ++ symbols.drop transform.discard

/-- The unchanged stack transform. -/
def identity (Symbol : Type*) : StackTransform Symbol :=
  ⟨[], 0⟩

/-- Normalize one additional push. -/
def push {Symbol : Type*} (symbol : Symbol)
    (transform : StackTransform Symbol) : StackTransform Symbol :=
  ⟨symbol :: transform.added, transform.discard⟩

/-- Normalize one additional pop. -/
def pop {Symbol : Type*}
    (transform : StackTransform Symbol) : StackTransform Symbol :=
  match transform.added with
  | [] => ⟨[], transform.discard + 1⟩
  | _ :: remaining => ⟨remaining, transform.discard⟩

@[simp]
theorem identity_apply {Symbol : Type*} (symbols : List Symbol) :
    (identity Symbol).apply symbols = symbols := by
  simp [identity, apply]

@[simp]
theorem push_apply {Symbol : Type*} (symbol : Symbol)
    (transform : StackTransform Symbol) (symbols : List Symbol) :
    (transform.push symbol).apply symbols =
      symbol :: transform.apply symbols := by
  simp [push, apply]

private theorem drop_succ_eq_tail_drop {Symbol : Type*}
    (symbols : List Symbol) (discarded : Nat) :
    symbols.drop (discarded + 1) = (symbols.drop discarded).tail := by
  induction discarded generalizing symbols with
  | zero => cases symbols <;> rfl
  | succ discarded ih =>
      cases symbols with
      | nil => simp
      | cons head tail =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih tail

@[simp]
theorem pop_apply {Symbol : Type*} (transform : StackTransform Symbol)
    (symbols : List Symbol) :
    transform.pop.apply symbols = (transform.apply symbols).tail := by
  cases addedEq : transform.added with
  | nil =>
      cases transform with
      | mk added discarded =>
          simp only at addedEq
          subst added
          change symbols.drop (discarded + 1) =
            (symbols.drop discarded).tail
          exact drop_succ_eq_tail_drop symbols discarded
  | cons head tail =>
      cases transform with
      | mk added discarded =>
          simp only at addedEq
          subst added
          simp [pop, apply]

/-- Optional value of one fixed-width output cell under a normalized
transform.  Cells beyond the represented source width are empty. -/
def cellValue {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current : Fin width → Option Symbol) (position : Fin width) :
    Option Symbol :=
  if addedPosition : position.val < transform.added.length then
    some transform.added[position.val]
  else
    let source := position.val - transform.added.length + transform.discard
    if sourcePosition : source < width then
      current ⟨source, sourcePosition⟩
    else
      none

/-- The first source cell that would fall beyond the fixed output width. -/
def firstOmitted {Symbol : Type*} (width : Nat)
    (transform : StackTransform Symbol) : Nat :=
  width - transform.added.length + transform.discard

/-- A fixed-width source vector has enough room for the normalized output.
When the first omitted source cell is represented, it must already be empty;
suffix shape then makes every later source cell empty as well. -/
def FitsVector {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current : Fin width → Option Symbol) : Prop :=
  transform.added.length ≤ width ∧
    ∀ omittedExists : transform.firstOmitted width < width,
      current ⟨transform.firstOmitted width, omittedExists⟩ = none

/-- Semantic relation on two fixed-width optional stack vectors. -/
def RelatesVector {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current next : Fin width → Option Symbol) : Prop :=
  transform.FitsVector current ∧
    ∀ position, next position = transform.cellValue current position

theorem apply_getElem? {Symbol : Type*} (transform : StackTransform Symbol)
    (symbols : List Symbol) (index : Nat) :
    (transform.apply symbols)[index]? =
      if addedPosition : index < transform.added.length then
        some transform.added[index]
      else
        symbols[index - transform.added.length + transform.discard]? := by
  rw [apply]
  by_cases addedPosition : index < transform.added.length
  · rw [dif_pos addedPosition, List.getElem?_append_left addedPosition]
    simp
  · rw [dif_neg addedPosition,
      List.getElem?_append_right (Nat.not_lt.mp addedPosition),
      List.getElem?_drop]
    rw [Nat.add_comm]

/-- The vector-level cell formula is the optional-cell view of applying the
same transform to the reconstructed source list. -/
theorem cellValue_eq_apply_getElem? {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current : Fin width → Option Symbol)
    (shaped : BoundedMachineAtom.OptionVectorShaped current)
    (position : Fin width) :
    transform.cellValue current position =
      (transform.apply
        (BoundedMachineAtom.occupiedPrefix width current))[position.val]? := by
  rw [apply_getElem?]
  by_cases addedPosition : position.val < transform.added.length
  · rw [cellValue, dif_pos addedPosition, dif_pos addedPosition]
  · rw [cellValue, dif_neg addedPosition, dif_neg addedPosition]
    let source := position.val - transform.added.length + transform.discard
    by_cases sourcePosition : source < width
    · rw [dif_pos sourcePosition]
      exact (BoundedMachineAtom.occupiedPrefix_getElem?_eq current shaped
        ⟨source, sourcePosition⟩).symm
    · rw [dif_neg sourcePosition]
      apply Eq.symm
      apply List.getElem?_eq_none
      exact le_trans
        (BoundedMachineAtom.occupiedPrefix_length_le width current)
        (Nat.not_lt.mp sourcePosition)

/-- The explicit overflow check is equivalent to the transformed ordinary
stack fitting in the fixed width. -/
theorem fitsVector_iff_apply_length_le {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current : Fin width → Option Symbol)
    (shaped : BoundedMachineAtom.OptionVectorShaped current) :
    transform.FitsVector current ↔
      (transform.apply
        (BoundedMachineAtom.occupiedPrefix width current)).length ≤ width := by
  let symbols := BoundedMachineAtom.occupiedPrefix width current
  change transform.FitsVector current ↔
    (transform.apply symbols).length ≤ width
  have symbolsFit : symbols.length ≤ width :=
    BoundedMachineAtom.occupiedPrefix_length_le width current
  constructor
  · rintro ⟨addedFits, omittedEmpty⟩
    have symbolsBeforeOmitted :
        symbols.length ≤ transform.firstOmitted width := by
      by_cases omittedExists : transform.firstOmitted width < width
      · have recovered := BoundedMachineAtom.occupiedPrefix_getElem?_eq
          current shaped ⟨transform.firstOmitted width, omittedExists⟩
        rw [omittedEmpty omittedExists] at recovered
        exact List.getElem?_eq_none_iff.mp recovered
      · exact le_trans symbolsFit (Nat.not_lt.mp omittedExists)
    simp only [apply, List.length_append, List.length_drop]
    rw [firstOmitted] at symbolsBeforeOmitted
    omega
  · intro outputFits
    have addedFits : transform.added.length ≤ width := by
      simp only [apply, List.length_append, List.length_drop] at outputFits
      omega
    refine ⟨addedFits, ?_⟩
    intro omittedExists
    have symbolsBeforeOmitted :
        symbols.length ≤ transform.firstOmitted width := by
      simp only [apply, List.length_append, List.length_drop] at outputFits
      rw [firstOmitted]
      omega
    have omittedNone :
        symbols[transform.firstOmitted width]? = none :=
      List.getElem?_eq_none symbolsBeforeOmitted
    have recovered := BoundedMachineAtom.occupiedPrefix_getElem?_eq
      current shaped ⟨transform.firstOmitted width, omittedExists⟩
    rw [omittedNone] at recovered
    exact recovered.symm

/-- Vector relation and ordinary-list transformation coincide on suffix-shaped
vectors. -/
theorem relatesVector_iff_occupiedPrefix_eq {Symbol : Type*} {width : Nat}
    (transform : StackTransform Symbol)
    (current next : Fin width → Option Symbol)
    (currentShaped : BoundedMachineAtom.OptionVectorShaped current)
    (nextShaped : BoundedMachineAtom.OptionVectorShaped next) :
    transform.RelatesVector current next ↔
      BoundedMachineAtom.occupiedPrefix width next =
        transform.apply (BoundedMachineAtom.occupiedPrefix width current) := by
  let currentList := BoundedMachineAtom.occupiedPrefix width current
  let nextList := BoundedMachineAtom.occupiedPrefix width next
  have nextFits : nextList.length ≤ width :=
    BoundedMachineAtom.occupiedPrefix_length_le width next
  constructor
  · rintro ⟨fits, cells⟩
    have outputFits : (transform.apply currentList).length ≤ width :=
      (fitsVector_iff_apply_length_le transform current currentShaped).mp fits
    apply List.ext_getElem?
    intro index
    by_cases indexExists : index < width
    · let position : Fin width := ⟨index, indexExists⟩
      rw [BoundedMachineAtom.occupiedPrefix_getElem?_eq next nextShaped position,
        cells position,
        cellValue_eq_apply_getElem? transform current currentShaped position]
    · have widthLe := Nat.not_lt.mp indexExists
      rw [List.getElem?_eq_none (le_trans nextFits widthLe),
        List.getElem?_eq_none (le_trans outputFits widthLe)]
  · intro listsEqual
    have outputFits : (transform.apply currentList).length ≤ width := by
      rw [← listsEqual]
      exact nextFits
    refine ⟨(fitsVector_iff_apply_length_le
      transform current currentShaped).mpr outputFits, ?_⟩
    intro position
    have recovered := BoundedMachineAtom.occupiedPrefix_getElem?_eq
      next nextShaped position
    rw [listsEqual, ← cellValue_eq_apply_getElem?
      transform current currentShaped position] at recovered
    exact recovered.symm

end StackTransform

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

noncomputable local instance (stack : tm.K) : DecidableEq (tm.Γ stack) :=
  Classical.decEq _

/-- Expression for one output cell of a normalized stack transform. -/
def stackTransformCellExpression (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (position : Fin space) : TransitionExpr :=
  if addedPosition : position.val < transform.added.length then
    nextStackCellIs (tm := tm) (clockBits := clockBits) stack position
      (some transform.added[position.val])
  else
    let source := position.val - transform.added.length + transform.discard
    if sourcePosition : source < space then
      stackCellsEqual (tm := tm) (clockBits := clockBits) stack
        ⟨source, sourcePosition⟩ position
    else
      nextStackCellIs (tm := tm) (clockBits := clockBits) stack position none

/-- Reject an output prefix wider than the represented stack, and require the
first omitted represented source cell to be empty. -/
def stackTransformFitsExpression (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) : TransitionExpr :=
  if _addedFits : transform.added.length ≤ space then
    if omittedExists : transform.firstOmitted space < space then
      currentStackCellIs (tm := tm) (clockBits := clockBits) stack
        ⟨transform.firstOmitted space, omittedExists⟩ none
    else
      .constant true
  else
    .constant false

/-- Linear-size expression for a complete normalized stack transform. -/
def stackTransformExpression (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) : TransitionExpr :=
  .and
    (stackTransformFitsExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform)
    (TransitionExpr.all ((List.finRange space).map fun position =>
      stackTransformCellExpression (tm := tm) (clockBits := clockBits)
        stack transform position))

theorem stackTransformCellExpression_eval_iff_decode
    {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (position : Fin space) :
    (stackTransformCellExpression (tm := tm) (clockBits := clockBits)
      stack transform position).eval current next = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) next).stack stack position =
      transform.cellValue
        ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack) position := by
  rw [stackTransformCellExpression]
  by_cases addedPosition : position.val < transform.added.length
  · rw [dif_pos addedPosition]
    simp [StackTransform.cellValue, addedPosition,
      nextStackCellIs_eval_decode nextOneHot]
  · rw [dif_neg addedPosition]
    let source := position.val - transform.added.length + transform.discard
    by_cases sourcePosition : source < space
    · rw [dif_pos sourcePosition]
      rw [StackTransform.cellValue, dif_neg addedPosition,
        dif_pos sourcePosition]
      exact (stackCellsEqual_eval_iff_decode currentOneHot nextOneHot stack
        (⟨source, sourcePosition⟩ : Fin space) position).trans eq_comm
    · rw [dif_neg sourcePosition]
      simp [StackTransform.cellValue, addedPosition, source,
        sourcePosition, nextStackCellIs_eval_decode nextOneHot]

theorem stackTransformFitsExpression_eval_iff_decode
    {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    (stackTransformFitsExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).eval current next = true ↔
      transform.FitsVector
        ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack) := by
  rw [stackTransformFitsExpression, StackTransform.FitsVector]
  by_cases addedFits : transform.added.length ≤ space
  · rw [dif_pos addedFits]
    by_cases omittedExists : transform.firstOmitted space < space
    · rw [dif_pos omittedExists]
      simp [addedFits, omittedExists,
        currentStackCellIs_eval_decode currentOneHot]
    · rw [dif_neg omittedExists]
      simp [TransitionExpr.eval, addedFits, omittedExists]
  · rw [dif_neg addedFits]
    simp [TransitionExpr.eval, addedFits]

theorem stackTransformExpression_eval_iff_decode
    {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    (stackTransformExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).eval current next = true ↔
      transform.RelatesVector
        ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack)
        ((decode (tm := tm) (space := space)
          (clockBits := clockBits) next).stack stack) := by
  rw [stackTransformExpression, TransitionExpr.eval, Bool.and_eq_true,
    stackTransformFitsExpression_eval_iff_decode currentOneHot,
    TransitionExpr.all_eval, List.all_eq_true,
    StackTransform.RelatesVector]
  constructor
  · rintro ⟨fits, cells⟩
    refine ⟨fits, fun position => ?_⟩
    apply (stackTransformCellExpression_eval_iff_decode
      currentOneHot nextOneHot stack transform position).mp
    apply cells
    simp
  · rintro ⟨fits, cells⟩
    refine ⟨fits, ?_⟩
    intro expression expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (stackTransformCellExpression_eval_iff_decode
      currentOneHot nextOneHot stack transform position).mpr (cells position)

/-- On list-shaped decoded slices, the linear Boolean expression is exactly
the corresponding ordinary-list stack transformation. -/
theorem stackTransformExpression_eval_iff_toCfg
    {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) current).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) next).StackShaped)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    (stackTransformExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).eval current next = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) next).toCfg.stk stack =
      transform.apply ((decode (tm := tm) (space := space)
        (clockBits := clockBits) current).toCfg.stk stack) := by
  rw [stackTransformExpression_eval_iff_decode
    currentOneHot nextOneHot stack transform]
  simpa [BoundedMachineSlice.toCfg, BoundedMachineSlice.stackList] using
    StackTransform.relatesVector_iff_occupiedPrefix_eq transform
      ((decode (tm := tm) (space := space)
        (clockBits := clockBits) current).stack stack)
      ((decode (tm := tm) (space := space)
        (clockBits := clockBits) next).stack stack)
      (BoundedMachineSlice.stack_optionVectorShaped currentShaped stack)
      (BoundedMachineSlice.stack_optionVectorShaped nextShaped stack)

theorem stackTransformCellExpression_atomsBelow (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (position : Fin space) :
    (stackTransformCellExpression (tm := tm) (clockBits := clockBits)
      stack transform position).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  rw [stackTransformCellExpression]
  split <;> rename_i addedPosition
  · exact nextStackCellIs_atomsBelow stack position _
  · dsimp only
    split <;> rename_i sourcePosition
    · exact stackCellsEqual_atomsBelow stack _ position
    · exact nextStackCellIs_atomsBelow stack position none

theorem stackTransformFitsExpression_atomsBelow (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    (stackTransformFitsExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  rw [stackTransformFitsExpression]
  split <;> rename_i addedFits
  · split <;> rename_i omittedExists
    · exact currentStackCellIs_atomsBelow stack _ none
    · trivial
  · trivial

theorem stackTransformExpression_atomsBelow (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    (stackTransformExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  refine ⟨stackTransformFitsExpression_atomsBelow stack transform, ?_⟩
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackTransformCellExpression_atomsBelow stack transform position

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
