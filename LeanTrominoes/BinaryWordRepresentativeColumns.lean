/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupSemantics
import LeanTrominoes.EncodedUnaryColumnCompiler

/-! # Compiled datum columns at distinct injective binary-word names -/
namespace LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup

theorem selectedValues_injective_keys {Index : Type} [DecidableEq Index]
    (rows : List Index) (key : Index → List Bool) (value : Index → Nat)
    (injective : Function.Injective key) :
    selectedValues ⟨rows.map key⟩ (rows.map value)=rows.dedup.map value := by
  classical
  let datum (word : List Bool) := if h : ∃ i, key i=word then value h.choose else 0
  have atKey (i : Index) : datum (key i)=value i := by
    simp only [datum,dif_pos (show ∃ j, key j=key i from ⟨i,rfl⟩)]
    congr 1
    exact injective (Exists.choose_spec (show ∃ j, key j=key i from ⟨i,rfl⟩))
  have mapped : rows.map value=(rows.map key).map datum := by
    simp only [List.map_map]
    exact List.map_congr_left (fun i _ => (atKey i).symm)
  rw [mapped,selectedValues_map_eq_dedup_map,List.dedup_map_of_injective injective,List.map_map]
  exact List.map_congr_left (fun i _ => atKey i)

end LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup

noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol] [DecidableEq Index]
  {encodeInput : Input → List Symbol} {rows : Input → List Index}
  {key : Input → Index → List Bool} {value : Input → Index → Nat}

def binaryNamedDedup
    (names : TM2ComputableInPolyTime encodeInput DelimitedBinaryWords.encode
      (fun s => ⟨(rows s).map (key s)⟩))
    (values : Compiler encodeInput rows value)
    (injective : ∀ s, Function.Injective (key s)) :
    Compiler encodeInput (fun s => (rows s).dedup) value := by
  let computed := DelimitedBinaryWordRepresentativeValueLookup.selectedValuesComputableInPolyTime
    encodeInput (fun s => ⟨(rows s).map (key s)⟩) (fun s => (rows s).map (value s))
    (fun _ => by simp) names values
  exact computed.of_eq (fun s =>
    DelimitedBinaryWordRepresentativeValueLookup.selectedValues_injective_keys
      (rows s) (key s) (value s) (injective s))

end LeanTrominoes.EncodedUnaryColumn
