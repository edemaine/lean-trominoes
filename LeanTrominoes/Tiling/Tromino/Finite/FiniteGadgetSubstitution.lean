/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FinitePeriodicTrominoBridge
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetReduction
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetExpandedMotifFiniteTokens

/-! # Finite Figure 11/12 substitution for drawings with a blank boundary

The final row and column contain no gadgets. Successive periodic copies are
therefore separated, so the finite motif has exactly the same orientation
behavior as the verified infinite gadget substitution.
-/
namespace LeanTrominoes.Gadget.PeriodicOrthogonalDrawing

/-- No gadget occupies the final row or column of the drawing domain. -/
def BlankBoundary (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∀ position : drawing.Position,
    position.1.val+1=drawing.horizontalPeriod ∨ position.2.val+1=drawing.verticalPeriod →
      drawing.get position=.blank

theorem expandedMotif_boundary_bounds (t : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (boundary : drawing.BlankBoundary) (cell : Cell) (member : cell∈drawing.expandedMotif t) :
    0≤cell.1 ∧ cell.1≤6*(drawing.horizontalPeriod:Int)-3 ∧
      0≤cell.2 ∧ cell.2≤6*(drawing.verticalPeriod:Int)-3 := by
  obtain ⟨x,hx,member⟩ := List.mem_flatMap.mp member
  obtain ⟨y,hy,member⟩ := List.mem_flatMap.mp member
  obtain ⟨pixel,hp,rfl⟩ := List.mem_map.mp member
  have bounds := GadgetExpandedMotifFiniteTokens.orthogonalCellPixel_bounds t (drawing.get (x,y)) pixel hp
  have notBoundary : ¬(x.val+1=drawing.horizontalPeriod ∨ y.val+1=drawing.verticalPeriod) := by
    intro edge
    have blank := boundary (x,y) edge
    rw [blank] at hp
    simp [orthogonalCellPixels] at hp
  have horizontal : x.val+1≠drawing.horizontalPeriod := fun edge => notBoundary (Or.inl edge)
  have vertical : y.val+1≠drawing.verticalPeriod := fun edge => notBoundary (Or.inr edge)
  have horizontalBound : (x.val:Int)≤(drawing.horizontalPeriod:Int)-2 := by
    have hx := x.isLt
    simp only [horizontalPeriod] at horizontal ⊢
    omega
  have verticalBound : (y.val:Int)≤(drawing.verticalPeriod:Int)-2 := by
    have hy := y.isLt
    simp only [verticalPeriod] at vertical ⊢
    omega
  simp only [Cell.add,blockOrigin]
  omega

/-- Cutting the finite motif out of the infinite periodic reduction is exact. -/
theorem finiteMotif_tileable_iff (t : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (boundary : drawing.BlankBoundary) :
    t.Tileable ((drawing.expandedMotif t).toFinset : Set Cell) ↔
      t.Tileable (drawing.periodicRegion t).carrier := by
  apply Tromino.FinitePeriodicBridge.finite_tileable_iff_periodic
  · dsimp [horizontalPeriod]; omega
  · dsimp [verticalPeriod]; omega
  · exact expandedMotif_boundary_bounds t drawing boundary

/-- The same checked local gadgets implement finite orientation instances. -/
theorem finiteSubstitution_correct (t : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
    (boundary : drawing.BlankBoundary) :
    drawing.HasOrientation ↔ t.Tileable ((drawing.expandedMotif t).toFinset : Set Cell) := by
  have behavior : OrientationBehaviorCorrect t := by
    cases t
    · exact iOrientationBehaviorCorrect
    · exact lOrientationBehaviorCorrect
  rw [finiteMotif_tileable_iff t drawing boundary]
  constructor
  · intro oriented
    exact (substitutionAssemblyCorrect t drawing).mp ((behavior drawing separated).mp oriented).2
  · intro tileable
    exact (behavior drawing separated).mpr
      ⟨wellFormed,(substitutionAssemblyCorrect t drawing).mpr tileable⟩

end LeanTrominoes.Gadget.PeriodicOrthogonalDrawing
