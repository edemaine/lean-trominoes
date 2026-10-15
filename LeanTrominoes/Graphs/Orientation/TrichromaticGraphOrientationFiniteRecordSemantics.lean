/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteCountSemantics

/-! # Endpoint bounds and zero offsets in the incidence enumeration -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget

theorem endpoint_checks_iff (graph : Input) :
    (∀ index < 2*graph.2.length, (incidenceAt graph index).1<graph.1.length) ↔
      ∀ record ∈ graph.2, record.1.source<graph.1.length ∧ record.1.target<graph.1.length := by
  constructor
  · intro checked record member
    obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
    have source := checked (2*index) (by omega)
    have target := checked (2*index+1) (by omega)
    have even : (2*index)%2=0 := by omega
    have odd : (2*index+1)%2=1 := by omega
    have leftHalf : (2*index)/2=index := by omega
    have rightHalf : (2*index+1)/2=index := by omega
    simp only [incidenceAt,even,odd,leftHalf,rightHalf,if_true,
      List.getD_eq_getElem _ _ bound] at source target
    exact ⟨source,target⟩
  · intro checked index bound
    have halfBound : index/2<graph.2.length := by omega
    have member := List.getElem_mem halfBound
    have h := checked _ member
    simp only [incidenceAt,List.getD_eq_getElem _ _ halfBound]
    split
    · exact h.1
    · exact h.2

theorem int_encode_zero_iff (value : Int) : Encodable.encode value=0 ↔ value=0 := by
  change Encodable.encode value=Encodable.encode (0:Int) ↔ value=0
  exact Encodable.encode_injective.eq_iff

def offsetCheck (s : WitnessInput) (index : Nat) : Bool :=
  let record := s.1.2.getD (index/2) (⟨0,0,(0,0)⟩,.red)
  decide ((FlatEncoding.edgeFields record).getD 2 0=0) &&
    decide ((FlatEncoding.edgeFields record).getD 3 0=0)

theorem offsetCheck_eq_true (s : WitnessInput) (index : Nat) :
    offsetCheck s index=true ↔ (s.1.2.getD (index/2) (⟨0,0,(0,0)⟩,.red)).1.offset=(0,0) := by
  simp [offsetCheck,FlatEncoding.edgeFields,int_encode_zero_iff,Prod.ext_iff]

theorem offset_checks_iff (s : WitnessInput) :
    (∀ index < 2*s.1.2.length, offsetCheck s index=true) ↔ ZeroOffsets s.1 := by
  simp only [offsetCheck_eq_true]
  constructor
  · intro checked record member
    obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
    have h := checked (2*index) (by omega)
    have half : (2*index)/2=index := by omega
    simpa only [half,List.getD_eq_getElem _ _ bound] using h
  · intro zero index bound
    have halfBound : index/2<s.1.2.length := by omega
    rw [List.getD_eq_getElem _ _ halfBound]
    exact zero _ (List.getElem_mem halfBound)

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
