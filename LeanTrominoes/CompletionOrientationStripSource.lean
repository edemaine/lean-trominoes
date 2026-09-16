/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitStripCut
import LeanTrominoes.CompletionOrientationCompiler
import LeanTrominoes.GadgetStripBoundary

/-! # A finite-height source for the completion strip reduction -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks
open Gadget Gadget.PeriodicOrthogonalDrawing
set_option maxHeartbeats 2000000

theorem Circuit.source_shift (kinds : Cell → CircuitKind) (dy : Int) :
    Circuit.SourceHolds kinds → Circuit.SourceHolds (fun c => kinds (c.1,c.2+dy)) := by
  rintro ⟨v,seams,valid⟩
  refine ⟨fun c p => v (c.1,c.2+dy) p,?_,fun c => valid _⟩
  intro c p
  have eq : gridNeighbor (c.1,c.2+dy) p =
      ((gridNeighbor c p).1,(gridNeighbor c p).2+dy) := by
    rcases four_ports p with rfl | rfl | rfl | rfl <;>
      apply Prod.ext <;> simp [gridNeighbor] <;> omega
  simpa only [eq] using seams (c.1,c.2+dy) p

theorem Circuit.source_shift_iff (kinds : Cell → CircuitKind) (dy : Int) :
    Circuit.SourceHolds (fun c => kinds (c.1,c.2+dy)) ↔ Circuit.SourceHolds kinds := by
  constructor
  · intro h
    simpa using Circuit.source_shift (fun c => kinds (c.1,c.2+dy)) (-dy) h
  · exact Circuit.source_shift kinds dy

def stripKinds (d : PeriodicOrthogonalDrawing) (c : Cell) : CircuitKind :=
  Circuit.cutKinds d.verticalPeriod (drawingKinds d) (c.1,c.2-1)

theorem drawing_wrap_row (d : PeriodicOrthogonalDrawing) (c : Cell) :
    drawingKinds d (Circuit.wrapRow d.verticalPeriod c) = drawingKinds d c := by
  simp [drawingKinds,getAt,positionAt,residue,Circuit.wrapRow,verticalPeriod]

theorem stripKinds_correct (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed)
    (blank : d.HasBlankVerticalBoundary) :
    Circuit.SourceHolds (stripKinds d) ↔ d.HasOrientation := by
  have positive : (0:Int) < d.verticalPeriod := by simp [verticalPeriod]
  have outside (c : Cell) (hc : c.2 = -1 ∨ c.2 = d.verticalPeriod) :
      drawingKinds d c = .blank := by
    obtain ⟨x,y⟩ := c
    rcases hc with h | h <;> dsimp at h <;> subst y
    · simp [drawingKinds,(blank x).1,kindOf]
    · simp [drawingKinds,(blank x).2,kindOf]
  have inside (c : Cell) (hc : c.2 = 0 ∨ c.2 = (d.verticalPeriod:Int)-1) :
      drawingKinds d c = .blank := by
    have zero := drawing_wrap_row d (c.1,d.verticalPeriod)
    have last := drawing_wrap_row d (c.1,-1)
    have negMod : (-1)%(d.verticalPeriod:Int) = (d.verticalPeriod:Int)-1 := by
      have eq := Int.emod_eq_of_lt (show 0 ≤ (d.verticalPeriod:Int)-1 by omega)
        (show (d.verticalPeriod:Int)-1 < d.verticalPeriod by omega)
      simpa [Int.sub_emod] using eq
    simp only [Circuit.wrapRow,Int.emod_self,negMod] at zero last
    obtain ⟨x,y⟩ := c
    rcases hc with h | h <;> dsimp at h <;> subst y
    · exact zero.trans (outside _ (Or.inr rfl))
    · exact last.trans (outside _ (Or.inl rfl))
  change Circuit.SourceHolds (fun c => Circuit.cutKinds d.verticalPeriod (drawingKinds d) (c.1,c.2+(-1))) ↔ _
  rw [Circuit.source_shift_iff,Circuit.source_cut_iff _ positive _ (drawing_wrap_row d) outside inside,
    ← drawing_source_correct d wf]

theorem stripKinds_support (d : PeriodicOrthogonalDrawing) (c : Cell)
    (hc : c.2 < 1 ∨ (d.verticalPeriod:Int) < c.2) : stripKinds d c = .blank := by
  have outside : ¬ (0 ≤ c.2-1 ∧ c.2-1 < d.verticalPeriod) := by omega
  change (if 0 ≤ c.2-1 ∧ c.2-1 < d.verticalPeriod then _ else CircuitKind.blank) = _
  rw [if_neg outside]

theorem stripKinds_periodic (d : PeriodicOrthogonalDrawing) (c : Cell) (i : Int) :
    stripKinds d (c.1+i*d.horizontalPeriod,c.2) = stripKinds d c := by
  unfold stripKinds Circuit.cutKinds
  dsimp only
  split_ifs
  · exact congrArg kindOf (by simpa [horizontalPeriod] using getAt_repeat d (c.1,c.2-1) i 0)
  · rfl
end LeanTrominoes.CompletionPattern.LBricks
