/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripCompiler
import LeanTrominoes.Theorem55CompilerComputability

/-! # Primitive recursiveness of the strip compiler -/

namespace LeanTrominoes.Theorem55StripCompiler
open Computability

theorem period_primrec : Primrec Theorem55StripSource.period :=
  Primrec.nat_mul.comp (Primrec.nat_add.comp periodicStrip_width_primrec (Primrec.const 72))
    periodicStrip_period_primrec

theorem padding_membership_primrec :
    PrimrecRel (fun (n : Nat) (c : Cell) => c ∈ StripTrominoPadding.region n) := by
  have x : Primrec (fun a : Nat × Cell => a.2.1 % (a.1 : Int)) :=
    int_emodNat_primrec.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have y : Primrec (fun a : Nat × Cell => a.2.2) := Primrec.snd.comp Primrec.snd
  exact (((Primrec.eq.comp x (Primrec.const 14)).or
    (Primrec.eq.comp x (Primrec.const 15))).and
      ((int_le_primrec.comp (Primrec.const 4) y).and
        (int_le_primrec.comp y (Primrec.const 6)))).primrecRel

theorem preparedContains_primrec : Primrec₂ preparedContains := by
  have source : Primrec (fun a : PeriodicStrip × Cell => a.1.contains (Cell.add (0,-10) a.2)) :=
    periodicStrip_contains_primrec.comp Primrec.fst
      (cell_add_primrec.comp (Primrec.const (0,-10)) Primrec.snd)
  have padding : Primrec (fun a : PeriodicStrip × Cell =>
      decide (a.2 ∈ StripTrominoPadding.region (Theorem55StripSource.period a.1))) :=
    padding_membership_primrec.decide.comp (period_primrec.comp Primrec.fst) Primrec.snd
  exact Primrec.cond source (Primrec.const true) padding

theorem refinedContains_primrec : Primrec₂ refinedContains := by
  have source : Primrec (fun a : PeriodicStrip × Cell => preparedContains a.1 (PlusRefinement.parent a.2)) :=
    preparedContains_primrec.comp Primrec.fst (Theorem55Compiler.parent_primrec.comp Primrec.snd)
  have cross : Primrec (fun a : PeriodicStrip × Cell =>
      decide (PlusRefinement.subcell a.2 ∈ PlusRefinement.cross)) :=
    (constant_polyomino_membership_primrec PlusRefinement.cross).decide.comp
      (Theorem55Compiler.subcell_primrec.comp Primrec.snd)
  exact Primrec.and.comp source cross

theorem repack_primrec : Primrec₂ KeyedStripComplement.repack := by
  exact Primrec.ite Theorem55Compiler.horizontal_lock_membership_primrec
    (cell_add_primrec.comp Primrec.snd
      (Primrec.pair (int_negate_primrec.comp (int_ofNat_primrec.comp Primrec.fst)) (Primrec.const 0)))
    Primrec.snd

theorem tileCells_primrec : Primrec tileCells := by
  have size : Primrec (fun source : PeriodicStrip => 3 * Theorem55StripSource.period source) :=
    Primrec.nat_mul.comp (Primrec.const 3) period_primrec
  have keep : PrimrecRel (fun (c : Cell) (source : PeriodicStrip) => (!refinedContains source c) = true) := by
    apply (Primrec.eq.comp₂ refinedContains_primrec.swap (Primrec₂.const true)).not.of_eq
    intro c source
    change (¬ refinedContains source c = true) ↔ (!refinedContains source c) = true
    cases refinedContains source c <;> decide
  have filtered : Primrec (fun source : PeriodicStrip =>
      (Theorem55Compiler.squareList (3 * Theorem55StripSource.period source)).filter
        (fun c => !refinedContains source c)) := by
    apply (keep.listFilter.comp (Theorem55Compiler.squareList_primrec.comp size) Primrec.id).of_eq
    intro source
    simp only [Bool.decide_coe,id_eq]
  exact Primrec.list_map filtered (repack_primrec.comp₂ (size.comp₂ Primrec₂.left) Primrec₂.right)

theorem compile_primrec : Primrec compile :=
  Primrec.ite periodicStrip_isWellFormed_primrec
    (Primrec.pair (Primrec.nat_mul.comp (Primrec.const 3) period_primrec) tileCells_primrec)
    (Primrec.const (0,[]))

end LeanTrominoes.Theorem55StripCompiler
