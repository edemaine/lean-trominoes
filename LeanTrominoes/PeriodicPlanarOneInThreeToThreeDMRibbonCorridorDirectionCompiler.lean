/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorDirectionData
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Finite-state compilation of ribbon corridor directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM
namespace RibbonCorridorDirectionCompiler

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Remember the preceding source direction and emit the macrocell block once
the outgoing direction arrives. -/
def transition (color : Gadget.WireColor)
    (previous : Option AxisDirection)
    (current : AxisDirection) :
    Option AxisDirection × List AxisDirection :=
  (some current,
    match previous with
    | none => []
    | some incoming =>
        ribbonMacrocellDirectionBlock incoming current color)

def finish (_ : Option AxisDirection) :
    List AxisDirection :=
  []

/-- The machine-facing finite-state output. -/
def output (color : Gadget.WireColor)
    (directions : List AxisDirection) :
    List AxisDirection :=
  FiniteStateTransducer.output none (transition color) finish directions

private theorem scan_some_eq
    (color : Gadget.WireColor)
    (previous : AxisDirection)
    (directions : List AxisDirection) :
    (FiniteStateTransducer.scan
      (transition color) (some previous) directions).2 =
      ribbonCorridorDirectionWord color (previous :: directions) := by
  induction directions generalizing previous with
  | nil =>
      simp [FiniteStateTransducer.scan, ribbonCorridorDirectionWord]
  | cons current directions induction =>
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction current]
      rw [ribbonCorridorDirectionWord]

/-- The adjacent-pair finite-state scan emits exactly the semantic corridor
direction word. -/
theorem output_eq
    (color : Gadget.WireColor)
    (directions : List AxisDirection) :
    output color directions =
      ribbonCorridorDirectionWord color directions := by
  cases directions with
  | nil =>
      simp [output, FiniteStateTransducer.output,
        FiniteStateTransducer.scan, finish,
        ribbonCorridorDirectionWord]
  | cons first rest =>
      unfold output FiniteStateTransducer.output
      simp only [FiniteStateTransducer.scan, transition]
      rw [scan_some_eq color first rest]
      simp [finish]

/-- Adjacent-pair ribbon corridor expansion is polynomial-time. -/
noncomputable def computableInPolyTime
    (color : Gadget.WireColor) :
    TM2ComputableInPolyTime id id
      (ribbonCorridorDirectionWord color) := by
  let compiled := FiniteStateTransducer.computableInPolyTime
    (none : Option AxisDirection) (transition color) finish
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun directions => by
      simpa only [id_eq, output] using output_eq color directions)

end RibbonCorridorDirectionCompiler
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

end
