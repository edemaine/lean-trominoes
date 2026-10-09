/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteCountColumns

/-! # Polynomial-time Boolean checks for finite graph orientation -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget Turing EncodedUnaryColumn

private theorem and_nat (first second : Bool) :
    first.toNat*second.toNat=(first && second).toNat := by cases first <;> cases second <;> rfl

private theorem or_nat (first second : Bool) :
    1-(decide (first.toNat+second.toNat=0)).toNat=(first || second).toNat := by
  cases first <;> cases second <;> rfl

private def andColumn {rows : WitnessInput → List Nat} {first second : WitnessInput → Nat → Bool}
    (a : Compiler encode rows (fun s row => (first s row).toNat))
    (b : Compiler encode rows (fun s row => (second s row).toNat)) :
    Compiler encode rows (fun s row => (first s row && second s row).toNat) :=
  TM2ComputableInPolyTime.of_eq (multiply a b)
    (fun _ => List.map_congr_left (fun _ _ => and_nat _ _))

private def orColumn {rows : WitnessInput → List Nat} {first second : WitnessInput → Nat → Bool}
    (a : Compiler encode rows (fun s row => (first s row).toNat))
    (b : Compiler encode rows (fun s row => (second s row).toNat)) :
    Compiler encode rows (fun s row => (first s row || second s row).toNat) :=
  TM2ComputableInPolyTime.of_eq (sub (constant a 1) (zeroIndicator (add a b)))
    (fun _ => List.map_congr_left (fun _ _ => or_nat _ _))

private def chooseColumn {rows : WitnessInput → List Nat} {kind first second : WitnessInput → Nat → Bool}
    (k : Compiler encode rows (fun s row => (kind s row).toNat))
    (a : Compiler encode rows (fun s row => (first s row).toNat))
    (b : Compiler encode rows (fun s row => (second s row).toNat)) :
    Compiler encode rows (fun s row => (if kind s row then first s row else second s row).toNat) := by
  let physical := add (multiply k a) (multiply (sub (constant k 1) k) b)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  dsimp only
  cases kind s row <;> cases first s row <;> cases second s row <;> rfl

def colorCheck (s : WitnessInput) (vertex : Nat) : Bool :=
  if s.1.1.getD vertex false then
    decide ((colorOwners .red s).count vertex=1) &&
    decide ((colorOwners .green s).count vertex=1) &&
    decide ((colorOwners .blue s).count vertex=1)
  else
    decide ((colorOwners .red s).count vertex=3) ||
    decide ((colorOwners .green s).count vertex=3) ||
    decide ((colorOwners .blue s).count vertex=3)

def inwardCheck (s : WitnessInput) (vertex : Nat) : Bool :=
  if s.1.1.getD vertex false then
    decide ((selectedOwners s).count vertex=0) || decide ((selectedOwners s).count vertex=3)
  else decide ((selectedOwners s).count vertex=1)

def vertexCheck (s : WitnessInput) (vertex : Nat) : Bool :=
  decide ((ownerValues s).count vertex=3) && colorCheck s vertex && inwardCheck s vertex

def colorCheckCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (colorCheck s vertex).toNat) := by
  let red := colorCountCompiler WireColor.red
  let green := colorCountCompiler WireColor.green
  let blue := colorCountCompiler WireColor.blue
  let tri := andColumn (andColumn (equalIndicator red (constant red 1))
    (equalIndicator green (constant green 1))) (equalIndicator blue (constant blue 1))
  let mono := orColumn (orColumn (equalIndicator red (constant red 3))
    (equalIndicator green (constant green 3))) (equalIndicator blue (constant blue 3))
  exact chooseColumn vertexKindCompiler tri mono

def inwardCheckCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (inwardCheck s vertex).toNat) := by
  let count := inwardCountCompiler
  exact chooseColumn vertexKindCompiler
    (orColumn (equalIndicator count (constant count 0)) (equalIndicator count (constant count 3)))
    (equalIndicator count (constant count 1))

def vertexCheckCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (vertexCheck s vertex).toNat) :=
  andColumn (andColumn (equalIndicator degreeCountCompiler (constant degreeCountCompiler 3))
    colorCheckCompiler) inwardCheckCompiler

def endpointCheckCompiler : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => (decide ((incidenceAt s.1 index).1<s.1.1.length)).toNat) :=
  lessIndicator ownerCompiler (broadcast ownerCompiler vertexCountCompiler)

def offsetCheckCompiler (field : Fin 5) : Compiler encode
    (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => (decide ((FlatEncoding.edgeFields
      (s.1.2.getD (index/2) (⟨0,0,(0,0)⟩,.red))).getD field.val 0=0)).toNat) :=
  zeroIndicator (incidenceFieldCompiler field)

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
end
