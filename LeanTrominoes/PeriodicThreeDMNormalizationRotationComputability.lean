/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCanonicalColoringComputability

/-!
# Computability of normalized port rotations

Compute the zero, one, or two clockwise local replacements that put a
trichromatic vertex's red endpoint at its north port.
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

/-- Finite lookup version of `portOfColor`, avoiding an encoding of a
function value in the compiler proof. -/
theorem portOfColorValues_primrec :
    Primrec fun input :
      (WireColor × WireColor × WireColor) × WireColor =>
      portOfColor
        (fun port => match port with
          | .west => input.1.1
          | .north => input.1.2.1
          | .east => input.1.2.2)
        input.2 :=
  Primrec.dom_finite _

/-- Whether a compiler vertex is a triple vertex. -/
def vertexIsTriple : PeriodicThreeDMVertex → Bool
  | .triple _ => true
  | .element _ _ => false

theorem vertexIsTriple_primrec : Primrec vertexIsTriple := by
  exact (Primrec.sumCasesOn PeriodicThreeDMVertex.equivData_primrec
    (Primrec.const true).to₂
    (Primrec.const false).to₂).of_eq fun vertex => by
      cases vertex <;> rfl

/-- Rotation selection after all geometric endpoint data has been compressed
to finite control data. -/
def rotationCountFromData
    (input : Bool × Option EndpointTripleData) : PortRotationCount :=
  if input.1 then
    rotationsToNorth
      (portOfColor (fun port => canonicalColorFromData (input.2, port)) .red)
  else .zero

theorem rotationCountFromData_primrec :
    Primrec rotationCountFromData :=
  Primrec.dom_finite _

theorem rotationCountFromData_at
    (input : Input × PeriodicThreeDMVertex) :
    rotationCountFromData
        (vertexIsTriple input.2, endpointTripleDataAt input) =
      rotationCountAt input.1 input.2 := by
  rcases input with ⟨compilerInput, vertex⟩
  cases vertex with
  | element color atom =>
      rfl
  | triple index =>
      simp only [rotationCountFromData, vertexIsTriple, if_true,
        rotationCountAt]
      congr 2
      funext port
      exact canonicalColorFromData_endpointTripleDataAt
        (compilerInput, .triple index) port

theorem rotationCountAt_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      rotationCountAt input.1 input.2 := by
  have isTriple : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      vertexIsTriple input.2) :=
    vertexIsTriple_primrec.comp Primrec.snd
  have data : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      endpointTripleDataAt input) :=
    endpointTripleDataAt_primrec
  exact (rotationCountFromData_primrec.comp
    (Primrec.pair isTriple data)).of_eq rotationCountFromData_at

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
