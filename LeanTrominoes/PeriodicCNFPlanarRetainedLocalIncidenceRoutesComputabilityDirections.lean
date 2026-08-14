/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityEncoding
import LeanTrominoes.EmbeddedCNFIncidenceDrawingAxisPlacement
import LeanTrominoes.AxisDirectionComputability

/-! # Primitive-recursive axis geometry for retained local routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace AxisDirection

theorem between_primrec : Primrec₂ AxisDirection.between := by
  change Primrec fun input : Cell × Cell =>
    AxisDirection.between input.1 input.2
  have firstX : Primrec fun input : Cell × Cell => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have firstY : Primrec fun input : Cell × Cell => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have secondX : Primrec fun input : Cell × Cell => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have secondY : Primrec fun input : Cell × Cell => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have sameX := Primrec.eq.comp firstX secondX
  have sameY := Primrec.eq.comp firstY secondY
  have east := Computability.int_lt_primrec.comp firstX secondX
  have west := Computability.int_lt_primrec.comp secondX firstX
  have north := Computability.int_lt_primrec.comp firstY secondY
  have south := Computability.int_lt_primrec.comp secondY firstY
  exact (Primrec.ite sameY
    (Primrec.ite east (Primrec.const .east)
      (Primrec.ite west (Primrec.const .west)
        (Primrec.const .invalid)))
    (Primrec.ite sameX
      (Primrec.ite north (Primrec.const .north)
        (Primrec.ite south (Primrec.const .south)
          (Primrec.const .invalid)))
      (Primrec.const .invalid))).of_eq fun input => by
        simp [AxisDirection.between]

private def intAbs (value : Int) : Int :=
  if 0 ≤ value then value else -value

private theorem intAbs_primrec : Primrec intAbs := by
  exact (Primrec.ite
    (Computability.int_le_primrec.comp
      (Primrec.const (0 : Int)) Primrec.id)
    Primrec.id Computability.int_negate_primrec).of_eq fun _ => rfl

private theorem intAbs_eq_abs (value : Int) :
    intAbs value = |value| := by
  by_cases nonnegative : 0 ≤ value
  · simp [intAbs, nonnegative, abs_of_nonneg]
  · have negative : value < 0 := lt_of_not_ge nonnegative
    simp [intAbs, nonnegative, abs_of_neg negative]

theorem axisSpan_primrec : Primrec₂ AxisDirection.axisSpan := by
  change Primrec fun input : Cell × Cell =>
    |input.2.1 - input.1.1| + |input.2.2 - input.1.2|
  have xDifference : Primrec fun input : Cell × Cell =>
      input.2.1 - input.1.1 :=
    Computability.int_subtract_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have yDifference : Primrec fun input : Cell × Cell =>
      input.2.2 - input.1.2 :=
    Computability.int_subtract_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Computability.int_add_primrec.comp
    (intAbs_primrec.comp xDifference)
    (intAbs_primrec.comp yDifference)).of_eq fun input => by
      rw [intAbs_eq_abs, intAbs_eq_abs]

theorem orientPoint_primrec : Primrec₂ AxisDirection.orientPoint := by
  change Primrec fun input : AxisDirection × Cell =>
    input.1.orientPoint input.2
  have east : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.east :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.east)
  have north : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.north :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.north)
  have west : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.west :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.west)
  have south : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.south :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.south)
  have northPoint : Primrec fun input : AxisDirection × Cell =>
      (-input.2.2, input.2.1) :=
    Primrec.pair
      (Computability.int_negate_primrec.comp
        (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  have westPoint : Primrec fun input : AxisDirection × Cell =>
      (-input.2.1, -input.2.2) :=
    Primrec.pair
      (Computability.int_negate_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (Computability.int_negate_primrec.comp
        (Primrec.snd.comp Primrec.snd))
  have southPoint : Primrec fun input : AxisDirection × Cell =>
      (input.2.2, -input.2.1) :=
    Primrec.pair (Primrec.snd.comp Primrec.snd)
      (Computability.int_negate_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.ite east Primrec.snd
    (Primrec.ite north northPoint
      (Primrec.ite west westPoint
        (Primrec.ite south southPoint Primrec.snd)))).of_eq
          fun input => by cases input.1 <;> rfl

theorem placePoint_primrec :
    Primrec fun input : (Cell × AxisDirection) × Cell =>
      input.1.2.placePoint input.1.1 input.2 := by
  exact (Computability.cell_add_primrec.comp
    (Primrec.fst.comp Primrec.fst)
    (orientPoint_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)).of_eq
        fun _ => rfl

end AxisDirection

end LeanTrominoes
