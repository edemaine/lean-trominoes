/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteIncidenceColumns

/-! # Polynomial-time incidence and inward counts at each finite vertex -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget Turing EncodedUnaryColumn

def ownerValues (s : WitnessInput) : List Nat :=
  (List.range (2*s.1.2.length)).map fun index => (incidenceAt s.1 index).1

def selectedOwners (s : WitnessInput) : List Nat :=
  ((List.range (2*s.1.2.length)).filter (inward s.2)).map fun index => (incidenceAt s.1 index).1

def colorOwners (color : WireColor) (s : WitnessInput) : List Nat :=
  ((List.range (2*s.1.2.length)).filter fun index =>
    decide (FlatEncoding.colorField (incidenceAt s.1 index).2.2=FlatEncoding.colorField color)).map
      fun index => (incidenceAt s.1 index).1

def selectedOwnersCompiler : TM2ComputableInPolyTime encode UnaryFieldEncoderMachine.unaryFields selectedOwners := by
  let physical := filter (keep := fun s index => decide ((inward s.2 index).toNat=1))
    ownerCompiler (bits inwardCompiler)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  change ((List.range (2*s.1.2.length)).filter (fun index => decide ((inward s.2 index).toNat=1))).map
    (fun index => (incidenceAt s.1 index).1) = selectedOwners s
  unfold selectedOwners
  apply congrArg (List.map (fun index => (incidenceAt s.1 index).1))
  apply List.filter_congr
  intro index _
  cases inward s.2 index <;> rfl

def colorOwnersCompiler (color : WireColor) : TM2ComputableInPolyTime encode UnaryFieldEncoderMachine.unaryFields
    (colorOwners color) := by
  let equal := equalIndicator colorCompiler (constant colorCompiler (FlatEncoding.colorField color))
  let physical := filter ownerCompiler (bits equal)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  change ((List.range (2*s.1.2.length)).filter (fun index => decide
    ((decide (FlatEncoding.colorField (incidenceAt s.1 index).2.2=FlatEncoding.colorField color)).toNat=1))).map
      (fun index => (incidenceAt s.1 index).1) = colorOwners color s
  unfold colorOwners
  apply congrArg (List.map (fun index => (incidenceAt s.1 index).1))
  apply List.filter_congr
  intro index _
  by_cases same : FlatEncoding.colorField (incidenceAt s.1 index).2.2=FlatEncoding.colorField color <;> simp [same]

def degreeCountCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (ownerValues s).count vertex) :=
  countsOfValues (values := ownerValues) verticesCompiler ownerCompiler
    (fun s => by simpa using (show (List.range s.1.1.length).Nodup from List.nodup_range))

def inwardCountCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (selectedOwners s).count vertex) :=
  countsOfValues verticesCompiler selectedOwnersCompiler
    (fun s => by simpa using (show (List.range s.1.1.length).Nodup from List.nodup_range))

def colorCountCompiler (color : WireColor) : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (colorOwners color s).count vertex) :=
  countsOfValues verticesCompiler (colorOwnersCompiler color)
    (fun s => by simpa using (show (List.range s.1.1.length).Nodup from List.nodup_range))

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
end
