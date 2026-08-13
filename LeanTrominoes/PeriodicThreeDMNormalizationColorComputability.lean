/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationColorSelectionComputability

/-!
# Computability of normalized periodic 3DM endpoint colors

The endpoint fan determines which wire color occupies each old side of a
retained vertex.  This module combines triple lookup with the finite selector.
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

theorem endpointColorAtSide_primrec :
    Primrec fun input : AtSide =>
      endpointColorAtSide input.1.1 input.1.2 input.2 := by
  have problemAndVertex : Primrec (fun input : AtSide =>
      (input.1.1.problem, input.1.2)) :=
    Primrec.pair
      (Input.problem_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have triple : Primrec (fun input : AtSide =>
      input.1.1.problem.endpointTripleAt input.1.2) := by
    exact (endpointTripleAt_primrec.comp problemAndVertex).of_eq
      fun _ => rfl
  exact (Primrec.option_casesOn triple (Primrec.const .red)
    endpointColorFromTriple_primrec.to₂).of_eq fun input => by
      unfold endpointColorAtSide endpointColorFromTriple
      cases input.1.1.problem.endpointTripleAt input.1.2 <;> rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
