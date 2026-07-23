import LeanTrominoes.GadgetIPhaseLift
import LeanTrominoes.GadgetLPhaseLift

/-!
# Semantic Figure 11/12 reduction

This file composes the verified orientation behavior of both gadget libraries
with geometric block assembly.  Malformed or non-normalized source
presentations are mapped to a dependent-period presentation, which the target
decision predicate rejects by definition.
-/

namespace LeanTrominoes
namespace Gadget

/-- The normalized periodic trichromatic-orientation source predicate used by
the gadget reduction. -/
def NormalizedPeriodicOrientation
    (drawing : PeriodicOrthogonalDrawing) : Prop :=
  drawing.VerticesSeparated ∧ drawing.HasOrientation

/-- A canonical rejected target presentation for invalid source drawings. -/
def rejectedPeriodicRegion : PeriodicRegion where
  motif := []
  period₁ := (0, 0)
  period₂ := (0, 0)

theorem rejectedPeriodicRegion_not_fullRank :
    ¬rejectedPeriodicRegion.IsFullRank := by
  simp [PeriodicRegion.IsFullRank, PeriodicRegion.determinant,
    rejectedPeriodicRegion]

/-- Compile normalized well-formed drawings and send all other finite
presentations to a target no-instance. -/
def orientationReductionRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicRegion :=
  if drawing.IsWellFormed ∧ drawing.VerticesSeparated then
    drawing.periodicRegion tromino
  else
    rejectedPeriodicRegion

/-- The semantic reduction follows from orientation behavior plus exact
geometric assembly. -/
theorem orientationReductionRegion_correct
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    NormalizedPeriodicOrientation drawing ↔
      PeriodicTrominoTiling tromino
        (orientationReductionRegion tromino drawing) := by
  by_cases normalized :
      drawing.IsWellFormed ∧ drawing.VerticesSeparated
  · rw [orientationReductionRegion, if_pos normalized]
    constructor
    · rintro ⟨-, hasOrientation⟩
      have compatible :=
        (behavior drawing normalized.2).mp hasOrientation
      exact ⟨drawing.periodicRegion_fullRank tromino,
        (substitutionAssemblyCorrect tromino drawing).mp compatible.2⟩
    · rintro ⟨-, tileable⟩
      refine ⟨normalized.2, (behavior drawing normalized.2).mpr
        ⟨normalized.1, ?_⟩⟩
      exact (substitutionAssemblyCorrect tromino drawing).mpr tileable
  · rw [orientationReductionRegion, if_neg normalized]
    constructor
    · rintro ⟨separated, hasOrientation⟩
      exact (normalized ⟨hasOrientation.1, separated⟩).elim
    · rintro ⟨fullRank, -⟩
      exact (rejectedPeriodicRegion_not_fullRank fullRank).elim

/-- End-to-end correctness of the Figure 11 L-tromino reduction. -/
theorem lOrientationReductionRegion_correct
    (drawing : PeriodicOrthogonalDrawing) :
    NormalizedPeriodicOrientation drawing ↔
      PeriodicTrominoTiling .L
        (orientationReductionRegion .L drawing) :=
  orientationReductionRegion_correct .L lOrientationBehaviorCorrect drawing

/-- End-to-end correctness of the Figure 12 I-tromino reduction. -/
theorem iOrientationReductionRegion_correct
    (drawing : PeriodicOrthogonalDrawing) :
    NormalizedPeriodicOrientation drawing ↔
      PeriodicTrominoTiling .I
        (orientationReductionRegion .I drawing) :=
  orientationReductionRegion_correct .I iOrientationBehaviorCorrect drawing

end Gadget
end LeanTrominoes
