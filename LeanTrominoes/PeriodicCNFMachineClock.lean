import LeanTrominoes.PeriodicCNFMachineDecode
import Mathlib.Data.Nat.Bitwise

/-!
# Fixed-width reset clocks

The cyclic computation reduction stores its clock in a fixed little-endian
Boolean field.  This file connects the structural `BinarySuccessor` relation
to ordinary natural-number addition, including the no-overflow condition, and
identifies canonical machine clock atoms with the fixed-width bits of the
semantic clock.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

namespace TransitionExpr

/-- Interpret a little-endian Boolean list as a natural number. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | bit :: bits => bit.toNat + 2 * bitsValue bits

/-- The low `width` bits of a natural number, in little-endian order. -/
def fixedBits (width number : Nat) : List Bool :=
  (List.range width).map number.testBit

@[simp]
theorem fixedBits_length (width number : Nat) :
    (fixedBits width number).length = width := by
  simp [fixedBits]

@[simp]
theorem fixedBits_zero_width (number : Nat) :
    fixedBits 0 number = [] :=
  rfl

theorem fixedBits_succ_width (width number : Nat) :
    fixedBits (width + 1) number =
      number.testBit 0 :: fixedBits width (number / 2) := by
  simp [fixedBits, List.range_succ_eq_map, List.map_map,
    Function.comp_def, Nat.testBit_succ]

theorem bitsValue_lt_two_pow_length (bits : List Bool) :
    bitsValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitsValue]
  | cons bit bits ih =>
      cases bit <;> simp [bitsValue, pow_succ] at ih ⊢ <;> omega

theorem bitsValue_eq_zero_of_all_false {bits : List Bool}
    (allFalse : ∀ bit ∈ bits, bit = false) :
    bitsValue bits = 0 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [allFalse bit (by simp)]
      simp [bitsValue, ih (fun member memberMem =>
        allFalse member (by simp [memberMem]))]

theorem bitsValue_injective_of_length_eq {first second : List Bool}
    (lengthEq : first.length = second.length)
    (valueEq : bitsValue first = bitsValue second) :
    first = second := by
  induction first generalizing second with
  | nil =>
      have : second = [] := List.eq_nil_of_length_eq_zero
        (by simpa using lengthEq.symm)
      exact this.symm
  | cons first firsts ih =>
      cases second with
      | nil => simp at lengthEq
      | cons second seconds =>
          have tailLength : firsts.length = seconds.length := by
            simpa using lengthEq
          cases first <;> cases second <;>
            simp only [bitsValue, Bool.toNat_false, Bool.toNat_true] at valueEq
          · congr
            exact ih tailLength (by omega)
          · omega
          · omega
          · congr
            exact ih tailLength (by omega)

/-- Structural little-endian succession always adds one numerically. -/
theorem binarySuccessor_bitsValue {currentBits nextBits : List Bool}
    (successor : BinarySuccessor currentBits nextBits) :
    bitsValue nextBits = bitsValue currentBits + 1 := by
  induction currentBits generalizing nextBits with
  | nil =>
      cases nextBits <;> simp [BinarySuccessor] at successor
  | cons currentBit currentBits ih =>
      cases nextBits with
      | nil => simp [BinarySuccessor] at successor
      | cons nextBit nextBits =>
          cases currentBit with
          | false =>
              cases nextBit with
              | false => simp [BinarySuccessor] at successor
              | true =>
                  simp only [BinarySuccessor] at successor
                  subst nextBits
                  simp [bitsValue]
                  omega
          | true =>
              cases nextBit with
              | false =>
                  simp only [BinarySuccessor] at successor
                  have tailValue := ih successor
                  simp [bitsValue] at tailValue ⊢
                  omega
              | true => simp [BinarySuccessor] at successor

theorem binarySuccessor_length_eq {currentBits nextBits : List Bool}
    (successor : BinarySuccessor currentBits nextBits) :
    currentBits.length = nextBits.length := by
  induction currentBits generalizing nextBits with
  | nil =>
      cases nextBits <;> simp [BinarySuccessor] at successor
  | cons currentBit currentBits ih =>
      cases nextBits with
      | nil => simp [BinarySuccessor] at successor
      | cons nextBit nextBits =>
          cases currentBit with
          | false =>
              cases nextBit with
              | false => simp [BinarySuccessor] at successor
              | true =>
                  simp only [BinarySuccessor] at successor
                  simp [successor]
          | true =>
              cases nextBit with
              | false =>
                  simp only [BinarySuccessor] at successor
                  simp [ih successor]
              | true => simp [BinarySuccessor] at successor

/-- Equal-width Boolean vectors whose values differ by one satisfy the
structural no-overflow successor relation. -/
theorem binarySuccessor_of_bitsValue {currentBits nextBits : List Bool}
    (lengthEq : currentBits.length = nextBits.length)
    (valueEq : bitsValue nextBits = bitsValue currentBits + 1) :
    BinarySuccessor currentBits nextBits := by
  induction currentBits generalizing nextBits with
  | nil =>
      have nextNil : nextBits = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst nextBits
      simp [bitsValue] at valueEq
  | cons currentBit currentBits ih =>
      cases nextBits with
      | nil => simp at lengthEq
      | cons nextBit nextBits =>
          have tailLength : currentBits.length = nextBits.length := by
            simpa using lengthEq
          cases currentBit <;> cases nextBit
          · simp [bitsValue] at valueEq
            omega
          · simp only [BinarySuccessor]
            apply bitsValue_injective_of_length_eq tailLength
            simp [bitsValue] at valueEq
            omega
          · simp only [BinarySuccessor]
            apply ih tailLength
            simp [bitsValue] at valueEq
            omega
          · simp [bitsValue] at valueEq
            omega

theorem binarySuccessor_iff_bitsValue {currentBits nextBits : List Bool}
    (lengthEq : currentBits.length = nextBits.length) :
    BinarySuccessor currentBits nextBits ↔
      bitsValue nextBits = bitsValue currentBits + 1 := by
  exact ⟨binarySuccessor_bitsValue,
    binarySuccessor_of_bitsValue lengthEq⟩

/-- A natural below the fixed-width range is recovered from its low bits. -/
theorem bitsValue_fixedBits_of_lt {width number : Nat}
    (bounded : number < 2 ^ width) :
    bitsValue (fixedBits width number) = number := by
  induction width generalizing number with
  | zero =>
      simp at bounded
      subst number
      rfl
  | succ width ih =>
      rw [fixedBits_succ_width, bitsValue]
      have powerEq : 2 ^ (width + 1) = 2 * 2 ^ width := by
        rw [pow_succ]
        omega
      have dividedBound : number / 2 < 2 ^ width := by
        rw [powerEq] at bounded
        omega
      rw [ih dividedBound, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one number with remainder | remainder
      · simp [remainder]
        have division := Nat.mod_add_div number 2
        omega
      · simp [remainder]
        have division := Nat.mod_add_div number 2
        omega

/-- Re-encoding the numeric value of a Boolean vector at the same width
recovers the vector exactly. -/
theorem fixedBits_bitsValue (bits : List Bool) :
    fixedBits bits.length (bitsValue bits) = bits := by
  apply bitsValue_injective_of_length_eq
  · simp
  · rw [bitsValue_fixedBits_of_lt (bitsValue_lt_two_pow_length bits)]

/-- Fixed-width representations implement ordinary successor exactly when
the result still fits in the width. -/
theorem binarySuccessor_fixedBits {width number : Nat}
    (resultFits : number + 1 < 2 ^ width) :
    BinarySuccessor (fixedBits width number)
      (fixedBits width (number + 1)) := by
  apply binarySuccessor_of_bitsValue
  · simp
  · rw [bitsValue_fixedBits_of_lt (lt_trans (Nat.lt_succ_self number)
        resultFits), bitsValue_fixedBits_of_lt resultFits]

theorem binarySuccessor_fixedBits_iff {width current next : Nat}
    (currentFits : current < 2 ^ width)
    (nextFits : next < 2 ^ width) :
    BinarySuccessor (fixedBits width current) (fixedBits width next) ↔
      next = current + 1 := by
  rw [binarySuccessor_iff_bitsValue (by simp),
    bitsValue_fixedBits_of_lt currentFits,
    bitsValue_fixedBits_of_lt nextFits]

end TransitionExpr

namespace BoundedMachineAtom

open Turing
open PeriodicComputation

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

private theorem map_finRange_val (width : Nat) (function : Nat → Bool) :
    (List.finRange width).map (fun position => function position.val) =
      (List.range width).map function := by
  induction width generalizing function with
  | zero => rfl
  | succ width ih =>
      rw [List.finRange_succ, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Fin.val_zero]
      congr 1
      simpa [Function.comp_def] using
        ih (function := fun index => function (index + 1))

/-- Reading canonical clock atoms produces the fixed-width semantic clock
bits in little-endian order. -/
theorem clockAtoms_encode (state : ResetClockState tm.Cfg) :
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        (encode (space := space) (clockBits := clockBits) state) =
      TransitionExpr.fixedBits clockBits state.clock := by
  rw [clockAtoms, TransitionExpr.fixedBits, List.map_map]
  simp only [Function.comp_def, encode_clock]
  exact map_finRange_val clockBits state.clock.testBit

/-- Decoding canonical clock bits recovers every in-range semantic clock. -/
theorem bitsValue_clockAtoms_encode (state : ResetClockState tm.Cfg)
    (clockFits : state.clock < 2 ^ clockBits) :
    TransitionExpr.bitsValue
      ((clockAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        (encode (space := space) (clockBits := clockBits) state)) =
      state.clock := by
  rw [clockAtoms_encode]
  exact TransitionExpr.bitsValue_fixedBits_of_lt clockFits

/-- Clock expression for an ordinary non-reset edge. -/
def clockSuccessor : TransitionExpr :=
  TransitionExpr.binarySuccessor
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))

/-- Clock expression for an accepting edge, requiring every next-slice clock
bit to be zero. -/
def clockReset : TransitionExpr :=
  TransitionExpr.all
    ((clockAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
      fun atom => .not (.next atom))

theorem clockSuccessor_encode_iff
    (current next : ResetClockState tm.Cfg)
    (currentFits : current.clock < 2 ^ clockBits)
    (nextFits : next.clock < 2 ^ clockBits) :
    (clockSuccessor (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      next.clock = current.clock + 1 := by
  rw [clockSuccessor, TransitionExpr.binarySuccessor_eval_iff,
    clockAtoms_encode, clockAtoms_encode]
  exact TransitionExpr.binarySuccessor_fixedBits_iff currentFits nextFits

theorem clockReset_encode_iff (current next : ResetClockState tm.Cfg)
    (nextFits : next.clock < 2 ^ clockBits) :
    (clockReset (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      next.clock = 0 := by
  constructor
  · intro reset
    have allFalse : ∀ bit ∈
        (clockAtoms (tm := tm) (space := space)
          (clockBits := clockBits)).map
            (encode (space := space) (clockBits := clockBits) next),
        bit = false := by
      intro bit bitMem
      obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp bitMem
      have expressionTrue :
          (.not (.next atom) : TransitionExpr).eval
            (encode (space := space) (clockBits := clockBits) current)
            (encode (space := space) (clockBits := clockBits) next) = true := by
        have allTrue :
            ((clockAtoms (tm := tm) (space := space)
              (clockBits := clockBits)).map
              fun atom => (.not (.next atom) : TransitionExpr)).all
                (fun expression => expression.eval
                  (encode (space := space) (clockBits := clockBits) current)
                  (encode (space := space) (clockBits := clockBits) next)) = true := by
          simpa [clockReset] using reset
        apply List.all_eq_true.mp allTrue
        exact List.mem_map.mpr ⟨atom, atomMem, rfl⟩
      simpa [TransitionExpr.eval] using expressionTrue
    have zeroValue := TransitionExpr.bitsValue_eq_zero_of_all_false allFalse
    have decoded := bitsValue_clockAtoms_encode
      (space := space) (clockBits := clockBits) next nextFits
    omega
  · intro nextZero
    rw [clockReset, TransitionExpr.all_eval, List.all_eq_true]
    intro expression expressionMem
    obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp expressionMem
    obtain ⟨position, _, atomEq⟩ := List.mem_map.mp atomMem
    subst atom
    simp [TransitionExpr.eval, nextZero]

theorem clockSuccessor_atomsBelow :
    (clockSuccessor (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  TransitionExpr.binarySuccessor_atomsBelow
    clockAtoms_below clockAtoms_below

theorem clockReset_atomsBelow :
    (clockReset (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp expressionMem
  exact clockAtoms_below atom atomMem

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
