/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSegments
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebraSemantics

/-! # Exact semantics of affine descriptor-pair segments -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Affine consecutive-segment construction commutes exactly with point
evaluation. -/
theorem map_eval_segments
    (valuation : Side → Fin 11 → Nat) (affinePoints : List Point) :
    (segments affinePoints).map (Segment.eval valuation) =
      gridPolylineSegments (affinePoints.map (Point.eval valuation)) := by
  induction affinePoints using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons first second rest firstInduction restInduction =>
      simp [segments, gridPolylineSegments, Segment.eval,
        restInduction second]

/-- Affine segment evaluation is preserved exactly by canonical pair tagging. -/
theorem Segment.evalTokens_descriptorPairTokens
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    segment.evalTokens (descriptorPairTokens pair) =
      segment.evalPair pair := by
  have startEq :
      Point.eval (tokenFieldValue (descriptorPairTokens pair)) segment.start =
        Point.eval (pairFieldValue pair) segment.start :=
    Point.evalTokens_descriptorPairTokens segment.start pair
  have finishEq :
      Point.eval (tokenFieldValue (descriptorPairTokens pair)) segment.finish =
        Point.eval (pairFieldValue pair) segment.finish :=
    Point.evalTokens_descriptorPairTokens segment.finish pair
  unfold Segment.evalTokens Segment.evalPair Segment.eval
  rw [startEq, finishEq]

/-- Fixed period translation of an affine point evaluates to ordinary cell
translation by the evaluated period. -/
theorem Point.eval_translateByPeriod
    (valuation : Side → Fin 11 → Nat) (affinePoint : Point)
    (period : Expression) (translate : Cell) :
    (affinePoint.translateByPeriod period translate).eval valuation =
      Cell.add (affinePoint.eval valuation)
        (Cell.scale (period.eval valuation) translate) := by
  rcases translate with ⟨horizontal, vertical⟩
  simp [Point.translateByPeriod, Point.eval, point, Cell.add, Cell.scale]
  constructor <;> ring

/-- Fixed period translation of an affine segment evaluates to ordinary
segment translation by the evaluated period. -/
theorem Segment.eval_translateByPeriod
    (valuation : Side → Fin 11 → Nat) (segment : Segment)
    (period : Expression) (translate : Cell) :
    (segment.translateByPeriod period translate).eval valuation =
      (segment.eval valuation).translate
        (Cell.scale (period.eval valuation) translate) := by
  rcases segment with ⟨start, finish⟩
  simp [Segment.translateByPeriod, Segment.eval, GridSegment.translate,
    Point.eval_translateByPeriod, Cell.add, add_comm]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
