import LeanTrominoes.PeriodicCNFMachineConfiguration

/-!
# Semantic expressions for bounded machine fields

This file supplies the small expression vocabulary used by the TM2 step
compiler.  It can test a current or next label, control state, or stack cell,
and can require corresponding finite fields to agree.  On arbitrary one-hot
valuations these expressions are proved equivalent to equality of the decoded
semantic fields.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace TransitionExpr

/-- The ordered one-hot equality vector distinguishes every member of its
finite value list. -/
theorem eq_of_decideEq_map_eq {Value : Type*} [DecidableEq Value]
    {values : List Value} {first second : Value}
    (firstMem : first ∈ values)
    (bitsEq :
      values.map (fun value => decide (first = value)) =
        values.map (fun value => decide (second = value))) :
    first = second := by
  induction values with
  | nil => simp at firstMem
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at bitsEq
      by_cases firstHead : first = head
      · subst first
        have secondHead : second = head := by
          simpa using bitsEq.1
        exact secondHead.symm
      · apply ih
        · simpa [firstHead] using firstMem
        · exact bitsEq.2

theorem finiteDecideEq_map_injective {Value : Type*} [Fintype Value]
    [DecidableEq Value] (first second : Value) :
    (BoundedMachineAtom.finiteValues Value).map
        (fun value => decide (first = value)) =
      (BoundedMachineAtom.finiteValues Value).map
        (fun value => decide (second = value)) ↔
      first = second := by
  constructor
  · exact eq_of_decideEq_map_eq
      (BoundedMachineAtom.mem_finiteValues first)
  · rintro rfl
    rfl

end TransitionExpr

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

noncomputable local instance : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (stack : tm.K) : DecidableEq (tm.Γ stack) :=
  Classical.decEq _

/-- Test one label in the current slice. -/
def currentLabelIs (label : Option tm.Λ) : TransitionExpr :=
  .current (code (.label label : BoundedMachineAtom tm space clockBits))

/-- Test one label in the next slice. -/
def nextLabelIs (label : Option tm.Λ) : TransitionExpr :=
  .next (code (.label label : BoundedMachineAtom tm space clockBits))

/-- Test one finite control state in the current slice. -/
def currentControlIs (control : tm.σ) : TransitionExpr :=
  .current (code (.state control : BoundedMachineAtom tm space clockBits))

/-- Test one finite control state in the next slice. -/
def nextControlIs (control : tm.σ) : TransitionExpr :=
  .next (code (.state control : BoundedMachineAtom tm space clockBits))

/-- Test one optional stack symbol in the current slice. -/
def currentStackCellIs (stack : tm.K) (position : Fin space)
    (symbol : Option (tm.Γ stack)) : TransitionExpr :=
  .current (code (.stack ⟨stack, position, symbol⟩ :
    BoundedMachineAtom tm space clockBits))

/-- Test one optional stack symbol in the next slice. -/
def nextStackCellIs (stack : tm.K) (position : Fin space)
    (symbol : Option (tm.Γ stack)) : TransitionExpr :=
  .next (code (.stack ⟨stack, position, symbol⟩ :
    BoundedMachineAtom tm space clockBits))

/-- Preserve the optional label field across an edge. -/
def labelsEqual : TransitionExpr :=
  TransitionExpr.vectorsEqual
    (labelAtoms (tm := tm) (space := space) (clockBits := clockBits))
    (labelAtoms (tm := tm) (space := space) (clockBits := clockBits))

/-- Preserve the finite control field across an edge. -/
def controlsEqual : TransitionExpr :=
  TransitionExpr.vectorsEqual
    (stateAtoms (tm := tm) (space := space) (clockBits := clockBits))
    (stateAtoms (tm := tm) (space := space) (clockBits := clockBits))

/-- Require one current stack cell to equal one next stack cell on the same
typed stack. -/
def stackCellsEqual (stack : tm.K)
    (currentPosition nextPosition : Fin space) : TransitionExpr :=
  TransitionExpr.vectorsEqual
    (stackCellAtoms (tm := tm) (clockBits := clockBits)
      stack currentPosition)
    (stackCellAtoms (tm := tm) (clockBits := clockBits)
      stack nextPosition)

/-- Preserve every represented cell of one stack. -/
def stackEqual (stack : tm.K) : TransitionExpr :=
  TransitionExpr.all ((List.finRange space).map fun position =>
    stackCellsEqual (tm := tm) (clockBits := clockBits)
      stack position position)

/-- Preserve every represented cell of every stack. -/
def stacksEqual : TransitionExpr :=
  TransitionExpr.all ((finiteValues tm.K).map fun stack =>
    stackEqual (tm := tm) (space := space) (clockBits := clockBits) stack)

@[simp]
theorem currentLabelIs_eval_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (label : Option tm.Λ) :
    (currentLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).label = label) := by
  exact decode_label_bit currentOneHot label

@[simp]
theorem nextLabelIs_eval_decode {current next : Nat → Bool}
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (label : Option tm.Λ) :
    (nextLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) next).label = label) := by
  exact decode_label_bit nextOneHot label

@[simp]
theorem currentControlIs_eval_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (control : tm.σ) :
    (currentControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).control = control) := by
  exact decode_state_bit currentOneHot control

@[simp]
theorem nextControlIs_eval_decode {current next : Nat → Bool}
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (control : tm.σ) :
    (nextControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) next).control = control) := by
  exact decode_state_bit nextOneHot control

@[simp]
theorem currentStackCellIs_eval_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (stack : tm.K) (position : Fin space) (symbol : Option (tm.Γ stack)) :
    (currentStackCellIs (tm := tm) (clockBits := clockBits)
      stack position symbol).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack position = symbol) := by
  exact decode_stack_bit currentOneHot stack position symbol

@[simp]
theorem nextStackCellIs_eval_decode {current next : Nat → Bool}
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (stack : tm.K) (position : Fin space) (symbol : Option (tm.Γ stack)) :
    (nextStackCellIs (tm := tm) (clockBits := clockBits)
      stack position symbol).eval current next =
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) next).stack stack position = symbol) := by
  exact decode_stack_bit nextOneHot stack position symbol

private theorem labelAtoms_map_decode {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    (labelAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        valuation =
      (finiteValues (Option tm.Λ)).map fun label =>
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) valuation).label = label) := by
  simp [labelAtoms, List.map_map, Function.comp_def,
    decode_label_bit oneHot]

private theorem stateAtoms_map_decode {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    (stateAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        valuation =
      (finiteValues tm.σ).map fun control =>
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) valuation).control = control) := by
  simp [stateAtoms, List.map_map, Function.comp_def,
    decode_state_bit oneHot]

private theorem stackCellAtoms_map_decode {valuation : Nat → Bool}
    (oneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (stack : tm.K) (position : Fin space) :
    (stackCellAtoms (tm := tm) (clockBits := clockBits)
      stack position).map valuation =
      (finiteValues (Option (tm.Γ stack))).map fun symbol =>
        decide ((decode (tm := tm) (space := space)
          (clockBits := clockBits) valuation).stack stack position = symbol) := by
  simp [stackCellAtoms, List.map_map, Function.comp_def,
    decode_stack_bit oneHot]

@[simp]
theorem labelsEqual_eval_iff_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true) :
    (labelsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).eval current next = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) current).label =
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) next).label := by
  rw [labelsEqual, TransitionExpr.vectorsEqual_eval_iff,
    labelAtoms_map_decode currentOneHot, labelAtoms_map_decode nextOneHot]
  exact TransitionExpr.finiteDecideEq_map_injective _ _

@[simp]
theorem controlsEqual_eval_iff_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true) :
    (controlsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).eval current next = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) current).control =
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) next).control := by
  rw [controlsEqual, TransitionExpr.vectorsEqual_eval_iff,
    stateAtoms_map_decode currentOneHot, stateAtoms_map_decode nextOneHot]
  exact TransitionExpr.finiteDecideEq_map_injective _ _

@[simp]
theorem stackCellsEqual_eval_iff_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (stack : tm.K) (currentPosition nextPosition : Fin space) :
    (stackCellsEqual (tm := tm) (clockBits := clockBits)
      stack currentPosition nextPosition).eval current next = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) current).stack stack currentPosition =
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) next).stack stack nextPosition := by
  rw [stackCellsEqual, TransitionExpr.vectorsEqual_eval_iff,
    stackCellAtoms_map_decode currentOneHot,
    stackCellAtoms_map_decode nextOneHot]
  exact TransitionExpr.finiteDecideEq_map_injective _ _

@[simp]
theorem stackEqual_eval_iff_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true)
    (stack : tm.K) :
    (stackEqual (tm := tm) (space := space)
      (clockBits := clockBits) stack).eval current next = true ↔
      ∀ position,
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack position =
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) next).stack stack position := by
  rw [stackEqual, TransitionExpr.all_eval, List.all_eq_true]
  constructor
  · intro equal position
    apply (stackCellsEqual_eval_iff_decode currentOneHot nextOneHot
      stack position position).mp
    apply equal
    simp
  · intro equal expression expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (stackCellsEqual_eval_iff_decode currentOneHot nextOneHot
      stack position position).mpr (equal position)

@[simp]
theorem stacksEqual_eval_iff_decode {current next : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval current current = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval next next = true) :
    (stacksEqual (tm := tm) (space := space)
      (clockBits := clockBits)).eval current next = true ↔
      ∀ stack position,
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) current).stack stack position =
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) next).stack stack position := by
  rw [stacksEqual, TransitionExpr.all_eval, List.all_eq_true]
  constructor
  · intro equal stack position
    apply (stackEqual_eval_iff_decode currentOneHot nextOneHot stack).mp
    apply equal
    exact List.mem_map.mpr ⟨stack, mem_finiteValues stack, rfl⟩
  · intro equal expression expressionMem
    obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (stackEqual_eval_iff_decode currentOneHot nextOneHot stack).mpr
      (equal stack)

theorem currentLabelIs_atomsBelow (label : Option tm.Λ) :
    (currentLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem nextLabelIs_atomsBelow (label : Option tm.Λ) :
    (nextLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem currentControlIs_atomsBelow (control : tm.σ) :
    (currentControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem nextControlIs_atomsBelow (control : tm.σ) :
    (nextControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem currentStackCellIs_atomsBelow (stack : tm.K) (position : Fin space)
    (symbol : Option (tm.Γ stack)) :
    (currentStackCellIs (tm := tm) (clockBits := clockBits)
      stack position symbol).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem nextStackCellIs_atomsBelow (stack : tm.K) (position : Fin space)
    (symbol : Option (tm.Γ stack)) :
    (nextStackCellIs (tm := tm) (clockBits := clockBits)
      stack position symbol).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  code_lt_atomCount _

theorem labelsEqual_atomsBelow :
    (labelsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  TransitionExpr.vectorsEqual_atomsBelow labelAtoms_below labelAtoms_below

theorem controlsEqual_atomsBelow :
    (controlsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  TransitionExpr.vectorsEqual_atomsBelow stateAtoms_below stateAtoms_below

theorem stackCellsEqual_atomsBelow (stack : tm.K)
    (currentPosition nextPosition : Fin space) :
    (stackCellsEqual (tm := tm) (clockBits := clockBits)
      stack currentPosition nextPosition).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  TransitionExpr.vectorsEqual_atomsBelow
    (stackCellAtoms_below stack currentPosition)
    (stackCellAtoms_below stack nextPosition)

theorem stackEqual_atomsBelow (stack : tm.K) :
    (stackEqual (tm := tm) (space := space)
      (clockBits := clockBits) stack).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackCellsEqual_atomsBelow stack position position

theorem stacksEqual_atomsBelow :
    (stacksEqual (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackEqual_atomsBelow stack

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
