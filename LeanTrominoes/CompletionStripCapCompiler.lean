/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCappedCore
import LeanTrominoes.CompletionHorizontalPrefill

/-! # Finite motifs for the periodic cap bands -/
namespace LeanTrominoes.CompletionPattern.StripCaps

theorem cap_prescribed (t : Tromino) (top : Bool) :
    HorizontalPrefill.prescribed t (width t) (capMotif t top) = capPrefill t top := by
  ext f
  constructor
  · rintro ⟨p,hp,i,rfl⟩
    exact ⟨i,p.cells (fun _ => t.cells),Finset.mem_image.mpr
      ⟨p,List.mem_toFinset.mpr hp,rfl⟩,(Placement.shift_cells_image p t _).symm⟩
  · rintro ⟨i,g,hg,rfl⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    exact ⟨p,List.mem_toFinset.mp hp,i,(Placement.shift_cells_image p t _).symm⟩

def expandedCap (t : Tromino) (top : Bool) (period : Nat) : List (Placement Unit) :=
  HorizontalPrefill.expand (width t) (2*period) (capMotif t top)

theorem expandedCap_prescribed (t : Tromino) (top : Bool) (period : Nat) (hp : 0 < period) :
    HorizontalPrefill.prescribed t (2*width t*period) (expandedCap t top period) = capPrefill t top := by
  have eq : 2*width t*(period:Int) = width t*((2*period:Nat):Int) := by push_cast; ring
  rw [eq,expandedCap,HorizontalPrefill.prescribed_expand t _ _ (by omega),cap_prescribed]

end LeanTrominoes.CompletionPattern.StripCaps

namespace LeanTrominoes.Tromino

theorem completable_translate_iff (t : Tromino) (region : Set Cell) (prescribed : Set (Finset Cell)) (v : Cell) :
    t.Completable (Cell.add v '' region) ((fun f => f.image (Cell.add v)) '' prescribed) ↔
      t.Completable region prescribed := by
  constructor
  · intro h
    have back := h.translate (Cell.sub (0,0) v)
    simpa [Set.image_image,Function.comp_def,Cell.add,Cell.sub,Finset.image_image] using back
  · intro h
    exact h.translate v

end LeanTrominoes.Tromino
