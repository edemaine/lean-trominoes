/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.GadgetDirectionTrimTransducers
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time endpoint trimming for direction words -/

noncomputable section

namespace LeanTrominoes
namespace Gadget
namespace DirectionTrim

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

noncomputable def dropFirstThreeComputableInPolyTime :
    TM2ComputableInPolyTime id id DropFirstThree.output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output .zero
      DropFirstThree.transition DropFirstThree.finish)
  exact FiniteStateTransducer.computableInPolyTime
    .zero DropFirstThree.transition DropFirstThree.finish

noncomputable def dropLastThreeComputableInPolyTime :
    TM2ComputableInPolyTime id id DropLastThree.output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output .zero
      DropLastThree.transition DropLastThree.finish)
  exact FiniteStateTransducer.computableInPolyTime
    .zero DropLastThree.transition DropLastThree.finish

noncomputable def transducerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id transducerOutput := by
  change TM2ComputableInPolyTime id id
    (fun input => DropLastThree.output (DropFirstThree.output input))
  exact TM2CompositionMachine.computableInPolyTime
    dropFirstThreeComputableInPolyTime
    dropLastThreeComputableInPolyTime

/-- Removing three directions from each end is a composition of two
linear-time finite-state transductions. -/
noncomputable def trimThreeDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id trimThreeDirections := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    transducerOutputComputableInPolyTime
    transducerOutput_eq_trimThreeDirections

end DirectionTrim
end Gadget
end LeanTrominoes

end
