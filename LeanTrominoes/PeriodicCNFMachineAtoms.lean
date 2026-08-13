import LeanTrominoes.Complexity
import LeanTrominoes.PeriodicCNFTransitionExprVectors
import Mathlib.Data.Fintype.EquivFin

/-!
# Atoms for bounded machine configurations

A Boolean slice in the PSPACE-hardness construction contains a complete
bounded machine configuration and a reset clock.  This file defines the
finite, dependently typed vocabulary for those bits and gives it one
collision-free interval of natural-number atom names.  Later files can build
transition expressions using the field-specific atom vectors while starting
all Tseitin allocation at `atomCount`.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Source atoms in one bounded configuration slice.  Stack cells store an
`Option` symbol: `none` is the unused suffix marker, while `some symbol`
records an occupied cell. -/
inductive BoundedMachineAtom (tm : FinTM2) (space clockBits : Nat)
  | label (value : Option tm.Λ)
  | state (value : tm.σ)
  | stack (cell : Σ stack : tm.K,
      Fin space × Option (tm.Γ stack))
  | clock (position : Fin clockBits)

private def BoundedMachineAtom.sumEquiv (tm : FinTM2)
    (space clockBits : Nat) :
    BoundedMachineAtom tm space clockBits ≃
      Option tm.Λ ⊕ tm.σ ⊕
        ((Σ stack : tm.K, Fin space × Option (tm.Γ stack)) ⊕
          Fin clockBits) where
  toFun
    | @BoundedMachineAtom.label _ _ _ value => Sum.inl value
    | @BoundedMachineAtom.state _ _ _ value => Sum.inr (Sum.inl value)
    | @BoundedMachineAtom.stack _ _ _ cell =>
        Sum.inr (Sum.inr (Sum.inl cell))
    | @BoundedMachineAtom.clock _ _ _ position =>
        Sum.inr (Sum.inr (Sum.inr position))
  invFun
    | Sum.inl value => .label value
    | Sum.inr (Sum.inl value) => .state value
    | Sum.inr (Sum.inr (Sum.inl cell)) => .stack cell
    | Sum.inr (Sum.inr (Sum.inr position)) => .clock position
  left_inv atom := by cases atom <;> rfl
  right_inv value := by
    rcases value with value | value
    · rfl
    · rcases value with value | value
      · rfl
      · rcases value with value | value
        · obtain ⟨stack, position, symbol⟩ := value
          rfl
        · rfl

noncomputable instance boundedMachineAtomFintype
    (tm : FinTM2) (space clockBits : Nat)
    [∀ stack, Fintype (tm.Γ stack)] :
    Fintype (BoundedMachineAtom tm space clockBits) :=
  Fintype.ofEquiv
    (Option tm.Λ ⊕ tm.σ ⊕
      ((Σ stack : tm.K, Fin space × Option (tm.Γ stack)) ⊕
        Fin clockBits))
    (BoundedMachineAtom.sumEquiv tm space clockBits).symm

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Number of source atoms in one Boolean slice. -/
def atomCount : Nat :=
  Fintype.card (BoundedMachineAtom tm space clockBits)

/-- Cardinality formula underlying the finite source-atom allocation. -/
theorem atomCount_eq_card_sum :
    atomCount (tm := tm) (space := space) (clockBits := clockBits) =
      Fintype.card
        (Option tm.Λ ⊕ tm.σ ⊕
          ((Σ stack : tm.K, Fin space × Option (tm.Γ stack)) ⊕
            Fin clockBits)) := by
  unfold atomCount
  exact Fintype.card_congr (BoundedMachineAtom.sumEquiv tm space clockBits)

/-- Injectively name every typed source atom by a natural below `atomCount`. -/
def code (atom : BoundedMachineAtom tm space clockBits) : Nat :=
  (Fintype.equivFin (BoundedMachineAtom tm space clockBits) atom).val

@[simp]
theorem code_lt_atomCount
    (atom : BoundedMachineAtom tm space clockBits) :
    code atom < atomCount (tm := tm) (space := space)
      (clockBits := clockBits) :=
  (Fintype.equivFin (BoundedMachineAtom tm space clockBits) atom).isLt

theorem code_injective :
    Function.Injective
      (code (tm := tm) (space := space) (clockBits := clockBits)) := by
  intro first second equality
  apply (Fintype.equivFin
    (BoundedMachineAtom tm space clockBits)).injective
  apply Fin.ext
  exact equality

theorem code_eq_iff {first second :
    BoundedMachineAtom tm space clockBits} :
    code first = code second ↔ first = second :=
  code_injective.eq_iff

/-- A duplicate-free enumeration of any finite type. -/
def finiteValues (Value : Type*) [Fintype Value] : List Value := by
  classical
  exact Finset.univ.toList

@[simp]
theorem mem_finiteValues {Value : Type*} [Fintype Value]
    (value : Value) :
    value ∈ finiteValues Value := by
  classical
  simp [finiteValues]

theorem finiteValues_nodup (Value : Type*) [Fintype Value] :
    (finiteValues Value).Nodup := by
  classical
  exact Finset.nodup_toList _

@[simp]
theorem finiteValues_length (Value : Type*) [Fintype Value] :
    (finiteValues Value).length = Fintype.card Value := by
  classical
  simp [finiteValues]

/-- Atom vector for the optional control label.  `none` is the halted label. -/
def labelAtoms : List Nat :=
  (finiteValues (Option tm.Λ)).map fun value =>
    code (.label value : BoundedMachineAtom tm space clockBits)

/-- Atom vector for the finite internal control state. -/
def stateAtoms : List Nat :=
  (finiteValues tm.σ).map fun value =>
    code (.state value : BoundedMachineAtom tm space clockBits)

/-- Atom vector for all possible values of one bounded stack cell. -/
def stackCellAtoms (stack : tm.K) (position : Fin space) : List Nat :=
  (finiteValues (Option (tm.Γ stack))).map fun value =>
    code (.stack ⟨stack, position, value⟩ :
      BoundedMachineAtom tm space clockBits)

/-- Little-endian atom vector for the reset clock. -/
def clockAtoms : List Nat :=
  (List.finRange clockBits).map fun position =>
    code (.clock position : BoundedMachineAtom tm space clockBits)

@[simp]
theorem labelAtoms_length :
    (labelAtoms (tm := tm) (space := space)
      (clockBits := clockBits)).length = Fintype.card (Option tm.Λ) := by
  simp [labelAtoms]

@[simp]
theorem stateAtoms_length :
    (stateAtoms (tm := tm) (space := space)
      (clockBits := clockBits)).length = Fintype.card tm.σ := by
  simp [stateAtoms]

@[simp]
theorem stackCellAtoms_length (stack : tm.K) (position : Fin space) :
    (stackCellAtoms (tm := tm) (clockBits := clockBits)
      stack position).length = Fintype.card (Option (tm.Γ stack)) := by
  simp [stackCellAtoms]

@[simp]
theorem clockAtoms_length :
    (clockAtoms (tm := tm) (space := space)
      (clockBits := clockBits)).length = clockBits := by
  simp [clockAtoms]

theorem labelAtoms_below :
    TransitionExpr.AtomListBelow
      (labelAtoms (tm := tm) (space := space) (clockBits := clockBits))
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  intro atom atomMem
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp atomMem
  exact code_lt_atomCount _

theorem stateAtoms_below :
    TransitionExpr.AtomListBelow
      (stateAtoms (tm := tm) (space := space) (clockBits := clockBits))
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  intro atom atomMem
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp atomMem
  exact code_lt_atomCount _

theorem stackCellAtoms_below (stack : tm.K) (position : Fin space) :
    TransitionExpr.AtomListBelow
      (stackCellAtoms (tm := tm) (clockBits := clockBits) stack position)
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  intro atom atomMem
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp atomMem
  exact code_lt_atomCount _

theorem clockAtoms_below :
    TransitionExpr.AtomListBelow
      (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  intro atom atomMem
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp atomMem
  exact code_lt_atomCount _

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
