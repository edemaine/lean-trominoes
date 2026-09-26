/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripSourcePaletteCompiler

/-! # A dense cell table supplies a sparse-model interface for every drawing -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Gadget Gadget.PeriodicOrthogonalDrawing

def densePoints (d : PeriodicOrthogonalDrawing) : List Cell :=
  (gridSites d.horizontalPeriod d.verticalPeriod).map (fun p => ((p.1:Int),(p.2:Int)))

def denseEntries (d : PeriodicOrthogonalDrawing) : List DrawingEntry :=
  (densePoints d).map (fun p => (p,d.getAt p))

private theorem lookup_function {A B : Type} [BEq A] [LawfulBEq A]
    (items : List A) (f : A → B) (a : A) (member : a ∈ items) :
    (items.map (fun p => (p,f p))).lookup a = some (f a) := by
  induction items with
  | nil => simp at member
  | cons b rest ih =>
    by_cases same : a = b
    · subst a
      simp
    · have tail := (List.mem_cons.mp member).resolve_left same
      have unequal : (a == b) = false := beq_eq_false_iff_ne.mpr same
      simp [List.lookup_cons,unequal,ih tail]

theorem densePoints_bounds (d : PeriodicOrthogonalDrawing) (p : Cell) (hp : p ∈ densePoints d) :
    0 ≤ p.1 ∧ p.1 < d.horizontalPeriod ∧ 0 ≤ p.2 ∧ p.2 < d.verticalPeriod := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have bounds := gridSites_bounds hq
  dsimp only [Prod.fst,Prod.snd]
  exact ⟨by omega,by exact_mod_cast bounds.1,by omega,by exact_mod_cast bounds.2⟩

theorem mem_densePoints (d : PeriodicOrthogonalDrawing) (p : Cell)
    (bounds : 0 ≤ p.1 ∧ p.1 < d.horizontalPeriod ∧ 0 ≤ p.2 ∧ p.2 < d.verticalPeriod) :
    p ∈ densePoints d := by
  apply List.mem_map.mpr
  refine ⟨(p.1.toNat,p.2.toNat),?_,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨p.1.toNat,List.mem_range.mpr (by omega),?_⟩
    exact List.mem_map.mpr ⟨p.2.toNat,List.mem_range.mpr (by omega),rfl⟩
  · exact Prod.ext (Int.toNat_of_nonneg bounds.1) (Int.toNat_of_nonneg bounds.2.2.1)

theorem denseModel (d : PeriodicOrthogonalDrawing) : SparseModel d (denseEntries d) where
  bounds := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact densePoints_bounds d p hp
  consistent := by
    intro a ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    rfl
  lookup := by
    intro p bounds
    rw [denseEntries,lookup_function (densePoints d) d.getAt p (mem_densePoints d p bounds)]
    rfl

theorem getAt_nat (d : PeriodicOrthogonalDrawing) (x y : Nat)
    (hx : x < d.horizontalPeriod) (hy : y < d.verticalPeriod) :
    d.getAt ((x:Int),(y:Int)) = d.cellTypes.getD (y*d.horizontalPeriod+x) .blank := by
  have ex : (x:Int) % (d.horizontalPeriod:Int) = x := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  have ey : (y:Int) % (d.verticalPeriod:Int) = y := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hy)
  change d.cellTypes.getD (((y:Int) % (d.verticalPeriod:Int)).toNat*d.horizontalPeriod+
    ((x:Int) % (d.horizontalPeriod:Int)).toNat) .blank = _
  rw [ex,ey]
  simp

end LeanTrominoes.CompletionPattern.Runtime
end
