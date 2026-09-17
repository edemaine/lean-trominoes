/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionTileField

/-! # Translation periods of the prescribed geometric footprints -/
namespace LeanTrominoes.CompletionPeriodic
open PeriodicTrominoPrefill
set_option maxHeartbeats 1000000

theorem prescribed_lattice_period (t : Tromino) (input : PeriodicTrominoPrefill) (i j : Int) :
    HasTranslationPeriod (input.prescribed t)
      (Cell.add (Cell.scale i input.period₁) (Cell.scale j input.period₂)) := by
  have forward (f : Finset Cell) (hf : f ∈ input.prescribed t) (i j : Int) :
      shift f (Cell.add (Cell.scale i input.period₁) (Cell.scale j input.period₂)) ∈ input.prescribed t := by
    obtain ⟨p,hp,k,l,rfl⟩ := hf
    refine ⟨p,hp,k+i,l+j,?_⟩
    simp only [shift,Finset.image_image]
    congr 1; funext c; ext <;> dsimp [Cell.add,Cell.scale] <;> ring
  intro f
  constructor
  · exact fun h => forward f h i j
  · intro h
    have hh := forward _ h (-i) (-j)
    rw [shift_shift] at hh
    have eq : Cell.add (Cell.add (Cell.scale i input.period₁) (Cell.scale j input.period₂))
        (Cell.add (Cell.scale (-i) input.period₁) (Cell.scale (-j) input.period₂)) = (0,0) := by
      ext <;> dsimp [Cell.add,Cell.scale] <;> ring
    simpa only [eq,shift_zero] using hh

theorem prescribed_square_period (t : Tromino) (input : PeriodicTrominoPrefill)
    (rank : (input.occupiedRegion t).IsFullRank) :
    ∃ n : Nat, HasSquarePeriod (input.prescribed t) (n+1) := by
  have independent : HasIndependentPeriods (input.prescribed t) :=
    ⟨input.period₁,input.period₂,rank,fun f i j => prescribed_lattice_period t input i j f⟩
  obtain ⟨N,hN,periodic⟩ := squarePeriod_of_independent independent
  cases N with
  | zero => omega
  | succ n => exact ⟨n,periodic⟩
end LeanTrominoes.CompletionPeriodic
