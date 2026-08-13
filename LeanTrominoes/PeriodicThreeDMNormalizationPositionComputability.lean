/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationPosition0Computability

/-!
# Computability of the three affine vertex-position rounds
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationPosition1_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      normalizationPosition1 input.1 input.2 :=
  (normalizeVertexPosition_primrec.comp
    normalizationPosition0_primrec).of_eq fun _ => rfl

theorem normalizationPosition2_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      normalizationPosition2 input.1 input.2 :=
  (normalizeVertexPosition_primrec.comp
    (normalizeVertexPosition_primrec.comp
      normalizationPosition0_primrec)).of_eq fun _ => rfl

theorem finalNormalizationPosition_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      finalNormalizationPosition input.1 input.2 :=
  (normalizeVertexPosition_primrec.comp
    (normalizeVertexPosition_primrec.comp
      (normalizeVertexPosition_primrec.comp
        normalizationPosition0_primrec))).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
