/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReversedTemplateComputability

/-!
# Primitive-recursive normalized target suffixes
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open PeriodicOrthocrossing
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def normalizationTargetSuffix
    (input : (Cell × List Cell) × List Cell) : List Cell :=
  joinAtEndpoint (trimmedMagnifiedRoute input.2)
    (reversedNormalizationTemplateAt input.1)

theorem normalizationTargetSuffix_primrec :
    Primrec normalizationTargetSuffix := by
  exact (joinAtEndpoint_primrec.comp
    (trimmedMagnifiedRoute_primrec.comp Primrec.snd)
    (reversedNormalizationTemplateAt_primrec.comp Primrec.fst)).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
