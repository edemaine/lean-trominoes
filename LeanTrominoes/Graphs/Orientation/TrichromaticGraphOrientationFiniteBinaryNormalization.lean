/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFinite
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.Computation.Encoding.Binary.BinaryFieldBoundedDecoder

/-! # Polynomially bounded normalization of binary finite graph records -/
namespace LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
open Gadget

def bound (graph : Input) : Nat := (FlatEncoding.fields graph).length+4
def capped (limit value : Nat) : Nat := if value<limit then value else 0
def cappedInt (limit : Nat) (value : Int) : Int := if Encodable.encode value<limit then value else 0
def normalize (graph : Input) : Input :=
  (graph.1,graph.2.map fun record =>
    (⟨capped (bound graph) record.1.source,capped (bound graph) record.1.target,
      (cappedInt (bound graph) record.1.offset.1,cappedInt (bound graph) record.1.offset.2)⟩,record.2))

theorem bound_counts (graph : Input) :
    graph.1.length<bound graph ∧ graph.2.length<bound graph ∧ 3<bound graph := by
  unfold bound
  rw [FlatEncoding.fields_length]
  omega

theorem cappedInt_encode (limit : Nat) (value : Int) :
    Encodable.encode (cappedInt limit value)=capped limit (Encodable.encode value) := by
  unfold cappedInt capped
  split <;> rfl

theorem fields_normalize (graph : Input) :
    FlatEncoding.fields (normalize graph)=(FlatEncoding.fields graph).map (capped (bound graph)) := by
  have counts := bound_counts graph
  have kind (bit : Bool) : capped (bound graph) bit.toNat=bit.toNat := by
    cases bit <;> simp [capped,show 0<bound graph from by omega,show 1<bound graph from by omega]
  have color (color : WireColor) : capped (bound graph) (FlatEncoding.colorField color)=FlatEncoding.colorField color := by
    cases color <;> simp [FlatEncoding.colorField,capped,show 0<bound graph from by omega,
      show 1<bound graph from by omega,show 2<bound graph from by omega]
  simp only [FlatEncoding.fields,normalize,List.length_map,List.map_cons,List.map_append,
    List.map_map,List.map_flatMap,List.flatMap_map]
  simp only [capped,if_pos counts.1,if_pos counts.2.1]
  congr 3
  · apply List.map_congr_left
    intro bit _
    exact (kind bit).symm
  · apply List.flatMap_congr
    intro record _
    simp only [FlatEncoding.edgeFields,List.map_cons,List.map_nil,cappedInt_encode,color]
    rfl

theorem normalize_eq_of_bounded (graph : Input) (small : ∀ value ∈ FlatEncoding.fields graph, value<bound graph) :
    normalize graph=graph := by
  have fieldsEq : FlatEncoding.fields (normalize graph)=FlatEncoding.fields graph := by
    rw [fields_normalize]
    conv_rhs => rw [← List.map_id (FlatEncoding.fields graph)]
    exact List.map_congr_left (fun value member => by simp [capped,small value member])
  have decoded := congrArg FlatEncoding.decodeFields fieldsEq
  simpa only [FlatEncoding.decodeFields_fields,Option.some.injEq] using decoded

theorem finiteProblem_fields_bounded (graph : Input) (accepted : FiniteProblem graph) :
    ∀ value ∈ FlatEncoding.fields graph, value<bound graph := by
  have counts := bound_counts graph
  intro value member
  simp only [FlatEncoding.fields,List.mem_cons,List.mem_append] at member
  rcases member with rfl | rfl | kind | edgeFieldsMember
  · exact counts.1
  · exact counts.2.1
  · obtain ⟨bit,_,rfl⟩ := List.mem_map.mp kind
    cases bit <;> simp <;> omega
  · obtain ⟨record,recordMember,valueMember⟩ := List.mem_flatMap.mp edgeFieldsMember
    have endpoints := accepted.1.1 record recordMember
    have zero := accepted.2.1 record recordMember
    simp only [FlatEncoding.edgeFields,zero,List.mem_cons,List.not_mem_nil,or_false] at valueMember
    rcases valueMember with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · change 0<bound graph; omega
    · change 0<bound graph; omega
    · cases record.2 <;> simp [FlatEncoding.colorField] <;> omega

theorem capped_eq_decoder (limit value : Nat) : capped limit value=BinaryFieldBoundedDecoder.cap limit value-1 := by
  by_cases small : value<limit <;> simp [capped,BinaryFieldBoundedDecoder.cap,small]

end LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
