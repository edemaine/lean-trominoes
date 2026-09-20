/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Extracting the target atom numbers of occurrence-split route records -/
namespace LeanTrominoes.PeriodicCNF.RouteTargetCompiler
open UnaryProgramTokens UnaryFieldEncoderMachine PeriodicOrthocrossing

abbrev Control := Fin 12

def transition (position : Control) : Token → Control × List Symbol
  | .clauseMarker => (0,[])
  | .atomUnit => (position,if position=4 then [.unit] else [])
  | .atomEnd => (position+1,if position=4 then [.delimiter] else [])
  | _ => (position,[])

def finish (_ : Control) : List Symbol := []
def output (tokens : List Token) : List Symbol :=
  FiniteStateTransducer.output 0 transition finish tokens

private theorem scan_units (position : Control) (n : Nat) :
    FiniteStateTransducer.scan transition position (List.replicate n .atomUnit) =
      (position,if position=4 then List.replicate n .unit else []) := by
  induction n with
  | zero => simp [FiniteStateTransducer.scan]
  | succ n ih =>
    by_cases h : position=4
    · subst position
      simp [List.replicate_succ,FiniteStateTransducer.scan,transition,ih]
    · simp [List.replicate_succ,FiniteStateTransducer.scan,transition,h,ih]

private theorem scan_field (position : Control) (n : Nat) :
    FiniteStateTransducer.scan transition position (CountedUnaryFieldTokens.field n) =
      (position+1,if position=4 then unaryField n else []) := by
  unfold CountedUnaryFieldTokens.field atomTokens
  rw [FiniteStateTransducer.scan_append,scan_units]
  by_cases h : position=4 <;>
    simp [FiniteStateTransducer.scan,transition,h,unaryField]

private theorem scan_fields_cons (position : Control) (n : Nat) (ns : List Nat) :
    FiniteStateTransducer.scan transition position (CountedUnaryFieldTokens.fields (n::ns)) =
      let rest := FiniteStateTransducer.scan transition (position+1) (CountedUnaryFieldTokens.fields ns)
      (rest.1,(if position=4 then unaryField n else [])++rest.2) := by
  rw [CountedUnaryFieldTokens.fields,List.flatMap_cons,FiniteStateTransducer.scan_append,scan_field]
  rfl

private theorem scan_record (position : Control) (d : RouteDescriptor) :
    FiniteStateTransducer.scan transition position
      (CountedUnaryFieldTokens.countedFieldBlock d.unaryFields) =
      (11,unaryField d.targetVertexIndex) := by
  simp only [CountedUnaryFieldTokens.countedFieldBlock,FiniteStateTransducer.scan,transition,
    RouteDescriptor.unaryFields,signedUnaryFields,List.cons_append,List.nil_append]
  simp only [scan_fields_cons]
  simp [CountedUnaryFieldTokens.fields,FiniteStateTransducer.scan]

private theorem scan_records (position : Control) (ds : List RouteDescriptor) :
    (FiniteStateTransducer.scan transition position (routeDescriptorTokens ds)).2 =
      unaryFields (ds.map RouteDescriptor.targetVertexIndex) := by
  induction ds generalizing position with
  | nil => rfl
  | cons d ds ih =>
    change (FiniteStateTransducer.scan transition position
      (CountedUnaryFieldTokens.countedFieldBlock d.unaryFields ++ routeDescriptorTokens ds)).2 = _
    rw [FiniteStateTransducer.scan_append,scan_record]
    simp only [List.map_cons,unaryFields,List.flatMap_cons]
    exact congrArg (unaryField d.targetVertexIndex ++ ·) (ih 11)

theorem output_descriptors (ds : List RouteDescriptor) :
    output (routeDescriptorTokens ds) = unaryFields (ds.map RouteDescriptor.targetVertexIndex) := by
  simpa [output,FiniteStateTransducer.output,finish] using scan_records 0 ds

noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime 0 transition finish

end LeanTrominoes.PeriodicCNF.RouteTargetCompiler
