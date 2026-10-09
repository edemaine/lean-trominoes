/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentPerturbationContacts

/-! # Perturbation bounds in translated periodic copies -/
namespace LeanTrominoes.GridSegment

theorem PointPerturbation.translate {factor : Int} {original output : Cell}
    (perturbed : PointPerturbation factor original output) (offset : Cell) :
    PointPerturbation factor (Cell.add offset original) (Cell.add (Cell.scale factor offset) output) := by
  have coordinate (old new shift : Int) : factor*shift+new-factor*(shift+old)=new-factor*old := by ring
  simpa only [PointPerturbation,Cell.add,Cell.scale,coordinate] using perturbed

theorem EndpointPerturbation.translate {factor : Int} {original output : GridSegment}
    (perturbed : EndpointPerturbation factor original output) (offset : Cell) :
    EndpointPerturbation factor (original.translate offset) (output.translate (Cell.scale factor offset)) :=
  ⟨perturbed.1.translate offset,perturbed.2.translate offset⟩

theorem direction_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).direction=segment.direction := by
  simp [direction,GridSegment.translate,Cell.add]

end LeanTrominoes.GridSegment
