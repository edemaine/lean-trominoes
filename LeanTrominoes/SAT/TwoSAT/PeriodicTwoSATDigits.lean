/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCoverIndex

/-! # Arithmetic formulas for the explicit cover indices

These identities expose the quotient and remainder operations performed by
cover generation. In particular the equivalence inverses are base-M digits,
not arbitrary finite enumerations.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph
variable {n d M : ℕ} [NeZero M]

theorem coordinateIndex_value (z : CoverLattice d M) :
    (coordinateIndex d M z).val=∑ j : Fin d, (z j).val*M^j.val := by
  cases M with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ M => rfl

theorem coordinateIndex_digit (i : Fin (M^d)) (j : Fin d) :
    (((coordinateIndex d M).symm i) j).val=(i.val/M^j.val)%M := by
  cases M with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ M => rfl

theorem literalIndex_value (a : Signed (Fin n)) :
    (literalIndex n a).val=2*a.1.val+(if a.2 then 1 else 0) := by
  cases a with
  | mk a sign => cases sign <;> simp [literalIndex,finProdFinEquiv,finTwoEquiv,Nat.add_comm]

theorem coverIndex_value (a : Signed (Fin n)) (z : CoverLattice d M) :
    (coverIndex n d M (a,z)).val=(2*a.1.val+(if a.2 then 1 else 0))*M^d+
      ∑ j : Fin d, (z j).val*M^j.val := by
  simp only [coverIndex,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv_apply_val,
    Prod.map_fst,Prod.map_snd,literalIndex_value,coordinateIndex_value]
  ring

theorem shifted_digit (i : Fin (M^d)) (offset : Lattice d) (j : Fin d) :
    ((((coordinateIndex d M).symm i)+wrap M offset) j).val=
      ((((i.val/M^j.val%M : ℕ) : ℤ)+offset j)%M).toNat := by
  have cast := ZMod.val_intCast (n := M)
    (((((coordinateIndex d M).symm i) j).val : ℤ)+offset j)
  simp only [Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val] at cast
  have converted := congrArg Int.toNat cast
  simpa only [Int.toNat_natCast,coordinateIndex_digit,Pi.add_apply,wrap] using converted

def shiftedCoordinate (d M i : ℕ) (offset : Lattice d) : ℕ :=
  ∑ j : Fin d, ((((i/M^j.val%M : ℕ) : ℤ)+offset j)%M).toNat*M^j.val

theorem shiftedCoordinate_eq (i : Fin (M^d)) (offset : Lattice d) :
    shiftedCoordinate d M i.val offset=
      (coordinateIndex d M (((coordinateIndex d M).symm i)+wrap M offset)).val := by
  rw [coordinateIndex_value]
  simp only [shiftedCoordinate,shifted_digit]

theorem shiftedCoordinate_lt (i : Fin (M^d)) (offset : Lattice d) :
    shiftedCoordinate d M i.val offset<M^d := by
  rw [shiftedCoordinate_eq]
  exact Fin.is_lt _

theorem shifted_coverIndex (a : Signed (Fin n)) (i : Fin (M^d)) (offset : Lattice d) :
    (coverIndex n d M (a,((coordinateIndex d M).symm i)+wrap M offset)).val=
      (2*a.1.val+(if a.2 then 1 else 0))*M^d+shiftedCoordinate d M i.val offset := by
  rw [coverIndex_value]
  simp only [shiftedCoordinate,shifted_digit]

end LeanTrominoes.PeriodicTwoSAT
