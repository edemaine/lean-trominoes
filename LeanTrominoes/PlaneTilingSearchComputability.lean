/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlaneTilingFiniteSearch

/-! # Primitive-recursive finite search for two-tile plane tilings -/

namespace LeanTrominoes.PlaneTilingSearch

open Computability

def placementEquiv : Placement Bool ≃ Bool × SquareSymmetry × Cell where
  toFun p := (p.kind, p.symmetry, p.offset)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨k, s, c⟩; rfl

noncomputable instance : Primcodable (Placement Bool) :=
  Primcodable.ofEquiv _ placementEquiv

theorem placement_data_primrec : Primrec placementEquiv := Primrec.of_equiv

theorem placement_mk_primrec : Primrec placementEquiv.symm := Primrec.of_equiv_symm

theorem kind_primrec : Primrec (Placement.kind : Placement Bool → Bool) :=
  Primrec.fst.comp placement_data_primrec

theorem symmetry_primrec : Primrec (Placement.symmetry : Placement Bool → SquareSymmetry) :=
  Primrec.fst.comp (Primrec.snd.comp placement_data_primrec)

theorem offset_primrec : Primrec (Placement.offset : Placement Bool → Cell) :=
  Primrec.snd.comp (Primrec.snd.comp placement_data_primrec)

theorem tileList_primrec : Primrec₂ tileList := by
  apply (Primrec.cond Primrec.snd (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)).of_eq
  intro a
  cases a.2 <;> rfl

theorem candidates_primrec : Primrec₂ candidates := by
  have bySymmetry : Primrec₂ (fun (a : (Input × Cell) × Bool) (s : SquareSymmetry) =>
      (tileList a.1.1 a.2).map (fun q => (⟨a.2, s, Cell.sub a.1.2 (s.act q)⟩ : Placement Bool))) := by
    apply Primrec.list_map (tileList_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
    change Primrec (fun a : (((Input × Cell) × Bool) × SquareSymmetry) × Cell =>
      placementEquiv.symm (a.1.1.2, a.1.2, Cell.sub a.1.1.1.2 (a.1.2.act a.2)))
    exact placement_mk_primrec.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (cell_sub_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (squareSymmetry_act_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))))
  exact Primrec.list_flatMap (Primrec.const [false, true])
    (Primrec.list_flatMap (Primrec.const TrominoAssignment.squareSymmetryList) bySymmetry)

theorem pool_primrec : Primrec₂ pool :=
  Primrec.list_flatMap (TrominoAssignment.boxCellList_primrec.comp Primrec.snd)
    (candidates_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

theorem subsets_primrec {α : Type} [Primcodable α] : Primrec (@subsets α) := by
  have heads : Primrec (fun a : List α × (α × List (List α)) =>
      a.2.2.map (a.2.1 :: ·)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  apply (Primrec.list_foldr Primrec.id (Primrec.const [[]])
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) heads).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp at ih ⊢
    simp only [subsets, ih]

abbrev CoverInput := Input × Placement Bool × Cell

theorem covers_primrec : PrimrecPred (fun a : CoverInput => a.2.2 ∈ a.2.1.cells (tiles a.1)) := by
  have hit : PrimrecRel (fun (q : Cell) (a : CoverInput) =>
      Cell.add a.2.1.offset (a.2.1.symmetry.act q) = a.2.2) :=
    Primrec.eq.comp₂
      (cell_add_primrec.comp₂
        (offset_primrec.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right)))
        (squareSymmetry_act_primrec.comp₂
          (symmetry_primrec.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))) Primrec₂.left))
      (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
  apply (hit.exists_mem_list.comp
    (tileList_primrec.comp Primrec.fst (kind_primrec.comp (Primrec.fst.comp Primrec.snd))) Primrec.id).of_eq
  intro a
  simp only [Placement.mem_cells_iff, tiles, List.mem_toFinset, id_eq]

abbrev ChoiceInput := Input × Cell × List (Placement Bool)

set_option maxHeartbeats 1000000 in
theorem valid_cell_primrec : PrimrecPred (fun a : ChoiceInput =>
    ∃ p ∈ a.2.2, a.2.1 ∈ p.cells (tiles a.1) ∧
      ∀ q ∈ a.2.2, a.2.1 ∈ q.cells (tiles a.1) → q = p) := by
  have others : PrimrecRel (fun (q : Placement Bool) (a : Input × Cell × Placement Bool) =>
      a.2.1 ∈ q.cells (tiles a.1) → q = a.2.2) := by
    apply ((covers_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))).not.or
        (Primrec.eq.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).of_eq
    intro a
    tauto
  have chosen : PrimrecRel (fun (p : Placement Bool) (a : ChoiceInput) =>
      a.2.1 ∈ p.cells (tiles a.1) ∧
        ∀ q ∈ a.2.2, a.2.1 ∈ q.cells (tiles a.1) → q = p) := by
    have cover : PrimrecPred (fun a : Placement Bool × ChoiceInput =>
        a.2.2.1 ∈ a.1.cells (tiles a.2.1)) :=
      covers_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    have selected : Primrec (fun a : Placement Bool × ChoiceInput => a.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have context : Primrec (fun a : Placement Bool × ChoiceInput => (a.2.1, a.2.2.1, a.1)) :=
      Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
    have unique : PrimrecPred (fun a : Placement Bool × ChoiceInput =>
        ∀ q ∈ a.2.2.2, a.2.2.1 ∈ q.cells (tiles a.2.1) → q = a.1) := by
      exact (others.forall_mem_list.comp selected context).of_eq (fun _ => Iff.rfl)
    exact cover.and unique
  exact chosen.exists_mem_list.comp (Primrec.snd.comp Primrec.snd) Primrec.id

theorem valid_primrec : PrimrecPred (fun a : Input × Nat × List (Placement Bool) => Valid a.1 a.2.1 a.2.2) := by
  have cells : PrimrecRel (fun (c : Cell) (a : Input × Nat × List (Placement Bool)) =>
      ∃ p ∈ a.2.2, c ∈ p.cells (tiles a.1) ∧
        ∀ q ∈ a.2.2, c ∈ q.cells (tiles a.1) → q = p) :=
    valid_cell_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact cells.forall_mem_list.comp
    (TrominoAssignment.boxCellList_primrec.comp (Primrec.fst.comp Primrec.snd)) Primrec.id

theorem finiteSearch_primrec : PrimrecRel FiniteSearch := by
  have selected : PrimrecRel (fun (ps : List (Placement Bool)) (a : Input × Nat) => Valid a.1 a.2 ps) :=
    valid_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  exact selected.exists_mem_list.comp (subsets_primrec.comp pool_primrec) Primrec.id

theorem coRE : LeanWang.CoREPred (fun input => Tileable (tiles input) Set.univ) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteSearch input radius) finiteSearch_primrec.not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ r, ¬ FiniteSearch input r) ↔ ¬ Tileable (tiles input) Set.univ
    rw [tileable_iff]
    exact not_forall.symm)

end LeanTrominoes.PlaneTilingSearch
