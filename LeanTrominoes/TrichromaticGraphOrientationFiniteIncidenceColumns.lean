/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteColumns
import LeanTrominoes.TrichromaticGraphOrientationFieldReads
import LeanTrominoes.TrichromaticGraphOrientationIncidenceIndices
import LeanTrominoes.EncodedUnaryColumnSerialization

/-! # Incidence owners, colors, and witness directions compiled from native fields -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget Turing EncodedUnaryColumn
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def recordFieldCompiler {Row : Type} {rows : WitnessInput → List Row}
    {index : WitnessInput → Row → Nat} {field : WitnessInput → Row → Fin 5}
    (indices : Compiler encode rows index) (fieldNumbers : Compiler encode rows (fun s row => (field s row).val))
    (bounded : ∀ s row, row ∈ rows s → index s row < s.1.2.length) :
    Compiler encode rows (fun s row => (FlatEncoding.edgeFields
      (s.1.2.getD (index s row) (⟨0,0,(0,0)⟩,.red))).getD (field s row).val 0) := by
  let addresses := add (add (constant indices 2) (broadcast indices vertexCountCompiler))
    (add (scale indices 5) fieldNumbers)
  apply TM2ComputableInPolyTime.of_eq (lookupValues addresses fieldsCompiler)
  intro s
  apply List.map_congr_left
  intro row member
  have bound := bounded s row member
  have read := FlatEncoding.recordField_getD s.1 (index s row) (field s row) bound
  simpa only [List.getD_eq_getElem _ _ bound,Nat.mul_comm,Nat.add_assoc] using read

def vertexKindCompiler : Compiler encode (fun s : WitnessInput => List.range s.1.1.length)
    (fun s vertex => (s.1.1.getD vertex false).toNat) := by
  let addresses := add (constant verticesCompiler 2) verticesCompiler
  apply TM2ComputableInPolyTime.of_eq (lookupValues addresses fieldsCompiler)
  intro s
  apply List.map_congr_left
  intro vertex member
  exact FlatEncoding.vertexKind_getD s.1 vertex (List.mem_range.mp member)

def incidenceFieldCompiler (field : Fin 5) :
    Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
      (fun s index => (FlatEncoding.edgeFields
        (s.1.2.getD (index/2) (⟨0,0,(0,0)⟩,.red))).getD field.val 0) :=
  recordFieldCompiler (field := fun _ _ => field) (halve incidencesCompiler)
    (constant incidencesCompiler field.val) (fun s index member => by
      have bound := List.mem_range.mp member
      omega)

def ownerCompiler : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => (incidenceAt s.1 index).1) := by
  let fields : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
      (fun _ index => (⟨index%2,by omega⟩ : Fin 5).val) :=
    residue incidencesCompiler 2 (by decide) (fun residue => residue.val)
  let physical := recordFieldCompiler (field := fun _ index => ⟨index%2,by omega⟩)
    (halve incidencesCompiler) fields (fun s index member => by
      have bound := List.mem_range.mp member
      omega)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro index _
  by_cases source : index%2=0
  · simp [incidenceAt,FlatEncoding.edgeFields,source]
  · have target : index%2=1 := by omega
    simp [incidenceAt,FlatEncoding.edgeFields,target]

def colorCompiler : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => FlatEncoding.colorField (incidenceAt s.1 index).2.2) := by
  apply TM2ComputableInPolyTime.of_eq (incidenceFieldCompiler 4)
  intro s
  apply List.map_congr_left
  intro index _
  dsimp only
  unfold incidenceAt
  dsimp only
  split <;> simp [FlatEncoding.edgeFields]

def inward (bits : List Bool) (index : Nat) : Bool :=
  if index%2=0 then !(bits.getD (index/2) false) else bits.getD (index/2) false

def inwardCompiler : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => (inward s.2 index).toNat) := by
  let bit := lookupValues (halve incidencesCompiler) bitsCompiler
  let parity := residue incidencesCompiler 2 (by decide) (fun residue => residue.val)
  let negativeBit := sub (constant bit 1) bit
  let negativeParity := sub (constant parity 1) parity
  let physical := add (multiply parity bit) (multiply negativeParity negativeBit)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro index _
  dsimp only
  have bitValue : (s.2.map Bool.toNat).getD (index/2) 0 = (s.2.getD (index/2) false).toNat := by
    simpa using List.getD_map (l := s.2) (n := index/2) (d := false) Bool.toNat
  rw [bitValue]
  by_cases source : index%2=0
  · cases value : s.2[index/2]?.getD false <;> simp [inward,source,value,List.getD_eq_getElem?_getD]
  · have target : index%2=1 := by omega
    cases value : s.2[index/2]?.getD false <;> simp [inward,target,value,List.getD_eq_getElem?_getD]

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
end
