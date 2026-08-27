/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionTransform

/-! # Finite-state endpoint trimming for direction words -/

namespace LeanTrominoes
namespace Gadget
namespace DirectionTrim

/-- Four finite states suffice to count the first three discarded symbols. -/
inductive DropCount
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Fintype

namespace DropFirstThree

def transition : DropCount → AxisDirection →
    DropCount × List AxisDirection
  | .zero, _ => (.one, [])
  | .one, _ => (.two, [])
  | .two, _ => (.three, [])
  | .three, direction => (.three, [direction])

def finish (_ : DropCount) : List AxisDirection := []

def output (directions : List AxisDirection) : List AxisDirection :=
  FiniteStateTransducer.output .zero transition finish directions

@[simp]
theorem scan_three (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition .three directions =
      (.three, directions) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

theorem output_eq_drop (directions : List AxisDirection) :
    output directions = directions.drop 3 := by
  cases directions with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp [output, FiniteStateTransducer.output,
                FiniteStateTransducer.scan, transition, finish]

end DropFirstThree

namespace DropLastThree

/-- The last at most three symbols form a finite delayed-output buffer. -/
inductive Buffer
  | zero
  | one (first : AxisDirection)
  | two (first second : AxisDirection)
  | three (first second third : AxisDirection)
  deriving DecidableEq, Fintype

def transition : Buffer → AxisDirection → Buffer × List AxisDirection
  | .zero, direction => (.one direction, [])
  | .one first, direction => (.two first direction, [])
  | .two first second, direction =>
      (.three first second direction, [])
  | .three first second third, direction =>
      (.three second third direction, [first])

def finish (_ : Buffer) : List AxisDirection := []

def output (directions : List AxisDirection) : List AxisDirection :=
  FiniteStateTransducer.output .zero transition finish directions

/-- Once the three-symbol buffer is full, its output is the prefix ending
three symbols before the end of the remaining stream. -/
theorem scan_three_output
    (first second third : AxisDirection)
    (directions : List AxisDirection) :
    (FiniteStateTransducer.scan transition (.three first second third)
      directions).2 =
      (first :: second :: third :: directions).take directions.length := by
  induction directions generalizing first second third with
  | nil => rfl
  | cons direction directions induction =>
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction second third direction]
      simp

theorem output_eq_take (directions : List AxisDirection) :
    output directions = directions.take (directions.length - 3) := by
  cases directions with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp only [output, FiniteStateTransducer.output,
                FiniteStateTransducer.scan, transition, finish,
                List.nil_append, List.length_cons]
              rw [scan_three_output first second third rest]
              simp

end DropLastThree

/-- The two finite-state passes implementing the normalization trim. -/
def transducerOutput (directions : List AxisDirection) :
    List AxisDirection :=
  DropLastThree.output (DropFirstThree.output directions)

theorem transducerOutput_eq_trimThreeDirections
    (directions : List AxisDirection) :
    transducerOutput directions = trimThreeDirections directions := by
  rw [transducerOutput, DropFirstThree.output_eq_drop,
    DropLastThree.output_eq_take]
  unfold trimThreeDirections
  rw [List.length_drop, Nat.sub_sub]

end DirectionTrim
end Gadget
end LeanTrominoes
