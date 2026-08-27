/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetDirectionFixedWrapperCompiler
import LeanTrominoes.GadgetDirectionTrimCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionTransform
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time one-round direction normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM

open Computability Turing
open Gadget

local instance : Inhabited AxisDirection := ⟨.invalid⟩

noncomputable def repeatTwelveDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id repeatTwelveDirections := by
  change TM2ComputableInPolyTime id id
    (fun directions : List AxisDirection =>
      directions.flatMap fun direction => List.replicate 12 direction)
  exact FiniteBlockTransducer.computableInPolyTime
    (fun direction => List.replicate 12 direction)

/-- The physically composed output before identifying the fixed wrapper
with the mathematical normalization word. -/
def normalizationDirectionPhysicalOutput
    (sourceTemplate targetTemplate : List Cell)
    (oldDirections : List AxisDirection) : List AxisDirection :=
  DirectionFixedWrapper.output
    (routeStepDirections sourceTemplate)
    (routeStepDirections targetTemplate.reverse)
    (trimThreeDirections (repeatTwelveDirections oldDirections))

theorem normalizationDirectionPhysicalOutput_eq
    (sourceTemplate targetTemplate : List Cell)
    (oldDirections : List AxisDirection) :
    normalizationDirectionPhysicalOutput sourceTemplate targetTemplate
        oldDirections =
      normalizationDirectionWord sourceTemplate targetTemplate
        oldDirections := by
  rw [normalizationDirectionPhysicalOutput,
    DirectionFixedWrapper.output_eq]
  unfold normalizationDirectionWord
  rw [List.append_assoc]

noncomputable def normalizationDirectionPhysicalOutputComputableInPolyTime
    (sourceTemplate targetTemplate : List Cell) :
    TM2ComputableInPolyTime id id
      (normalizationDirectionPhysicalOutput
        sourceTemplate targetTemplate) := by
  let expanded := repeatTwelveDirectionsComputableInPolyTime
  let trimmed := TM2CompositionMachine.computableInPolyTime expanded
    DirectionTrim.trimThreeDirectionsComputableInPolyTime
  let wrapped := TM2CompositionMachine.computableInPolyTime trimmed
    (DirectionFixedWrapper.computableInPolyTime
      (routeStepDirections sourceTemplate)
      (routeStepDirections targetTemplate.reverse))
  change TM2ComputableInPolyTime id id
    (fun oldDirections =>
      DirectionFixedWrapper.output
        (routeStepDirections sourceTemplate)
        (routeStepDirections targetTemplate.reverse)
        (trimThreeDirections
          (repeatTwelveDirections oldDirections)))
  exact wrapped

/-- For fixed endpoint templates, a complete normalization round on the
finite direction alphabet is polynomial-time computable. -/
noncomputable def normalizationDirectionWordComputableInPolyTime
    (sourceTemplate targetTemplate : List Cell) :
    TM2ComputableInPolyTime id id
      (normalizationDirectionWord sourceTemplate targetTemplate) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (normalizationDirectionPhysicalOutputComputableInPolyTime
      sourceTemplate targetTemplate)
    (normalizationDirectionPhysicalOutput_eq
      sourceTemplate targetTemplate)

end PeriodicThreeDM
end LeanTrominoes

end
