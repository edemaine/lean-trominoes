/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIOrientationCompiler

/-! # Primitive recursiveness of the completion reduction -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks
open Gadget Gadget.PeriodicOrthogonalDrawing Computability TrominoAssignment LBricks

set_option maxHeartbeats 2000000

private theorem drawing_h_primrec : Primrec PeriodicOrthogonalDrawing.horizontalPeriodPred :=
  (Primrec.fst.comp (Primrec.of_equiv : Primrec PeriodicOrthogonalDrawing.equivData)).of_eq fun _ => rfl

private theorem drawing_v_primrec : Primrec PeriodicOrthogonalDrawing.verticalPeriodPred :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv : Primrec PeriodicOrthogonalDrawing.equivData))).of_eq fun _ => rfl

private theorem drawing_cells_primrec : Primrec PeriodicOrthogonalDrawing.cellTypes :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv : Primrec PeriodicOrthogonalDrawing.equivData))).of_eq fun _ => rfl

private theorem emodNat_primrec : Primrec₂ fun (a : Int) (n : Nat) => a % (n : Int) := by
  exact (int_subtract_primrec.comp₂ Primrec₂.left
    (int_multiply_primrec.comp₂ (int_edivNat_primrec.comp₂ Primrec₂.left Primrec₂.right)
      (int_ofNat_primrec.comp₂ Primrec₂.right))).of_eq fun a n => by
        change a - a / (n : Int) * (n : Int) = a % (n : Int)
        have h := Int.emod_add_ediv_mul a (n : Int)
        omega

private theorem residue_nat_primrec : Primrec₂ fun (a : Int) (n : Nat) => (residue a n).val := by
  unfold residue
  exact int_toNat_primrec.comp₂ (emodNat_primrec.comp₂ Primrec₂.left
    (Primrec.nat_add.comp₂ Primrec₂.right (Primrec₂.const 1)))

private theorem getAt_primrec : Primrec₂ PeriodicOrthogonalDrawing.getAt := by
  have h : Primrec fun p : PeriodicOrthogonalDrawing × Cell => p.1.horizontalPeriodPred + 1 :=
    Primrec.nat_add.comp (drawing_h_primrec.comp Primrec.fst) (Primrec.const 1)
  have x : Primrec fun p : PeriodicOrthogonalDrawing × Cell => (residue p.2.1 p.1.horizontalPeriodPred).val :=
    residue_nat_primrec.comp (Primrec.fst.comp Primrec.snd) (drawing_h_primrec.comp Primrec.fst)
  have y : Primrec fun p : PeriodicOrthogonalDrawing × Cell => (residue p.2.2 p.1.verticalPeriodPred).val :=
    residue_nat_primrec.comp (Primrec.snd.comp Primrec.snd) (drawing_v_primrec.comp Primrec.fst)
  exact ((Primrec.list_getD (.blank : OrthogonalCellType)).comp
    (drawing_cells_primrec.comp Primrec.fst) (Primrec.nat_add.comp (Primrec.nat_mul.comp y h) x)).of_eq fun _ => rfl

private theorem macroIndex_primrec : Primrec Circuit.macroIndex :=
  Primrec.pair (int_edivNat_primrec.comp Primrec.fst (Primrec.const 64))
    (int_edivNat_primrec.comp Primrec.snd (Primrec.const 64))

private def finiteLabel (t : OrthogonalCellType) (p : Fin 64 × Fin 64) : Fin 24 :=
  (circuitFor (kindOf t)).labelAt (p.1.val,p.2.val)

private theorem local_indices_primrec : Primrec fun c : Cell => (residue c.1 63,residue c.2 63) :=
  Primrec.pair (Primrec.fin_val_iff.mp (residue_nat_primrec.comp Primrec.fst (Primrec.const 63)))
    (Primrec.fin_val_iff.mp (residue_nat_primrec.comp Primrec.snd (Primrec.const 63)))

theorem drawing_macro_palette_primrec : Primrec₂ fun d c => Circuit.macroPalette (drawingKinds d) c := by
  have table : Primrec fun p : OrthogonalCellType × (Fin 64 × Fin 64) => finiteLabel p.1 p.2 := Primrec.dom_finite _
  exact (table.comp (Primrec.pair (getAt_primrec.comp Primrec.fst (macroIndex_primrec.comp Primrec.snd))
    (local_indices_primrec.comp Primrec.snd))).of_eq fun p => by
      simp only [finiteLabel,Circuit.macroPalette,drawingKinds,residue_val_int]
      rfl

private theorem square_origin_primrec : Primrec fun c => origin (brickOfSquare c) := by
  have diff := int_subtract_primrec.comp Primrec.snd Primrec.fst
  exact Primrec.pair
    (int_add_primrec.comp (int_multiply_primrec.comp (Primrec.const 36) Primrec.fst)
      (int_multiply_primrec.comp (Primrec.const 18) diff))
    (int_multiply_primrec.comp (Primrec.const 162) diff)

private theorem shift_primrec : Primrec₂ fun (p : Placement Unit) (c : Cell) => p.shift c := by
  have data : Primrec fun q : Placement Unit × Cell =>
      ((),q.1.symmetry,Cell.add q.2 q.1.offset) :=
    Primrec.pair (Primrec.const ()) (Primrec.pair (placement_symmetry_primrec.comp Primrec.fst)
      (cell_add_primrec.comp Primrec.snd (placement_offset_primrec.comp Primrec.fst)))
  exact ((Primrec.of_equiv_symm : Primrec placementUnitEquiv.symm).comp data).of_eq fun _ => rfl

private theorem drawing_width_primrec : Primrec fun d => (drawingDomain d).width := by
  simp only [drawingDomain_width]
  exact Primrec.nat_mul.comp (Primrec.const 64) (Primrec.nat_add.comp drawing_h_primrec (Primrec.const 1))

private theorem drawing_height_primrec : Primrec fun d => (drawingDomain d).height := by
  simp only [drawingDomain_height]
  exact Primrec.nat_mul.comp (Primrec.const 64) (Primrec.nat_add.comp drawing_v_primrec (Primrec.const 1))

private theorem drawing_sites_primrec : Primrec fun d => (drawingDomain d).sites := by
  have rows : Primrec₂ fun (d : PeriodicOrthogonalDrawing) (x : Nat) =>
      (List.range (drawingDomain d).height).map fun (y : Nat) => ((x : Int),(y : Int)) :=
    Primrec.list_map (Primrec.list_range.comp (drawing_height_primrec.comp Primrec.fst))
      (Primrec₂.pair.comp₂ (int_ofNat_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
        (int_ofNat_primrec.comp₂ Primrec₂.right))
  exact Primrec.list_flatMap (Primrec.list_range.comp drawing_width_primrec) rows

private theorem drawing_motif_primrec : Primrec fun d => (compileDrawing d).motif := by
  have blocks : Primrec₂ fun d c =>
      (motif (Circuit.macroPalette (drawingKinds d) c)).map fun p => p.shift (origin (brickOfSquare c)) :=
    Primrec.list_map ((Primrec.dom_finite motif).comp drawing_macro_palette_primrec)
      (shift_primrec.comp₂ Primrec₂.right (square_origin_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.left)))
  exact Primrec.list_flatMap drawing_sites_primrec blocks

/-- The exact semantic compiler is primitive recursive on finite presentations. -/
theorem compileDrawing_primrec : Primrec compileDrawing := by
  have p₁ : Primrec fun d => origin (brickOfSquare ((drawingDomain d).width,0)) :=
    square_origin_primrec.comp (Primrec.pair (int_ofNat_primrec.comp drawing_width_primrec) (Primrec.const 0))
  have p₂ : Primrec fun d => origin (brickOfSquare (0,(drawingDomain d).height)) :=
    square_origin_primrec.comp (Primrec.pair (Primrec.const 0) (int_ofNat_primrec.comp drawing_height_primrec))
  exact ((Primrec.of_equiv_symm : Primrec PeriodicTrominoPrefill.equivData.symm).comp
    (Primrec.pair drawing_motif_primrec (Primrec.pair p₁ p₂))).of_eq fun _ => rfl

theorem compileDrawing_computable : Computable compileDrawing := compileDrawing_primrec.to_comp

end LeanTrominoes.CompletionPattern.IBricks
