/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BinaryWordBlocks
import LeanTrominoes.BinaryWordSetChecks
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.FiniteAlphabetPolyTime

/-! # A polynomial-time exact-cover verifier backend

The input explicitly supplies candidate footprints, cell names, prefilled
footprints, and selection bits. Whole footprints are selected before their
cell names are unpacked. Completion permits protruding cells; finite-region
tiling additionally requires every selected cell to belong to the region.

The certificate concerns this complete request encoding. Producing the
candidate table from geometric coordinates is a separate machine obligation.
-/
namespace LeanTrominoes.FiniteExactCoverVerifier
open Turing
abbrev Word := List Bool
abbrev Block := List Word
abbrev Words := DelimitedBinaryWords.Input
local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ := ⟨DelimitedBinaryWords.Token.wordStart⟩

structure Request where
  region : Block
  candidates : List Block
  required : List Block
  bits : List Bool
  deriving DecidableEq

inductive Token
  | region (token : DelimitedBinaryWords.Token)
  | candidate (token : DelimitedBinaryWords.Token)
  | required (token : DelimitedBinaryWords.Token)
  | bit (value : Bool)
  deriving DecidableEq, Fintype, Inhabited

def Request.encode (request : Request) : List Token :=
  (DelimitedBinaryWords.encode ⟨request.region⟩).map .region ++
  (DelimitedBinaryWords.encode ⟨request.candidates.map BinaryWordBlocks.pack⟩).map .candidate ++
  (DelimitedBinaryWords.encode ⟨request.required.map BinaryWordBlocks.pack⟩).map .required ++
  request.bits.map .bit

def Request.selected (request : Request) : List Block :=
  DelimitedBinaryWordBooleanFilter.selected request.bits request.candidates

def Request.selectedCells (request : Request) : Words := ⟨request.selected.flatten⟩
def Request.selectedBlocks (request : Request) : Words := ⟨request.selected.map BinaryWordBlocks.pack⟩
def Request.regionWords (request : Request) : Words := ⟨request.region⟩
def Request.requiredWords (request : Request) : Words := ⟨request.required.map BinaryWordBlocks.pack⟩
def Request.candidateWords (request : Request) : Words := ⟨request.candidates.map BinaryWordBlocks.pack⟩

def check (strict : Bool) (request : Request) : Bool :=
  BinaryWordSetChecks.nodupCheck request.selectedCells &&
  BinaryWordSetChecks.subsetCheck (request.regionWords,request.selectedCells) &&
  BinaryWordSetChecks.subsetCheck (request.requiredWords,request.selectedBlocks) &&
  (if strict then BinaryWordSetChecks.subsetCheck (request.selectedCells,request.regionWords) else true)

theorem check_correct (strict : Bool) (request : Request) :
    check strict request=true ↔
      request.selected.flatten.Nodup ∧
      (∀ word∈request.region, word∈request.selected.flatten) ∧
      (∀ block∈request.required, BinaryWordBlocks.pack block∈request.selected.map BinaryWordBlocks.pack) ∧
      (strict=true → ∀ word∈request.selected.flatten, word∈request.region) := by
  cases strict <;> simp [check,BinaryWordSetChecks.nodupCheck_correct,
    BinaryWordSetChecks.subsetCheck_correct,Request.selectedCells,Request.selectedBlocks,
    Request.regionWords,Request.requiredWords,and_assoc]

def wordProjection (role : Fin 3) : Token → List DelimitedBinaryWords.Token
  | .region token => if role=0 then [token] else []
  | .candidate token => if role=1 then [token] else []
  | .required token => if role=2 then [token] else []
  | .bit _ => []

def bitProjection : Token → List Bool
  | .bit bit => [bit]
  | _ => []

theorem projection_encode (role : Fin 3) (request : Request) :
    request.encode.flatMap (wordProjection role)=
      if role=0 then DelimitedBinaryWords.encode request.regionWords
      else if role=1 then DelimitedBinaryWords.encode request.candidateWords
      else DelimitedBinaryWords.encode request.requiredWords := by
  have map_region (tokens : List DelimitedBinaryWords.Token) :
      (tokens.map Token.region).flatMap (wordProjection role)=
        if role=0 then tokens else [] := by
    induction tokens with
    | nil => simp
    | cons token tokens ih => by_cases active : role=0 <;> simp_all [wordProjection]
  have map_candidate (tokens : List DelimitedBinaryWords.Token) :
      (tokens.map Token.candidate).flatMap (wordProjection role)=
        if role=1 then tokens else [] := by
    induction tokens with
    | nil => simp
    | cons token tokens ih => by_cases active : role=1 <;> simp_all [wordProjection]
  have map_required (tokens : List DelimitedBinaryWords.Token) :
      (tokens.map Token.required).flatMap (wordProjection role)=
        if role=2 then tokens else [] := by
    induction tokens with
    | nil => simp
    | cons token tokens ih => by_cases active : role=2 <;> simp_all [wordProjection]
  have map_bits : (request.bits.map Token.bit).flatMap (wordProjection role)=[] := by
    simp [List.flatMap_map,wordProjection]
  simp only [Request.encode,List.flatMap_append,map_region,map_candidate,map_required,map_bits]
  fin_cases role <;> simp [Request.regionWords,Request.candidateWords,Request.requiredWords]

theorem bits_encode (request : Request) : request.encode.flatMap bitProjection=request.bits := by
  have erase (constructor : DelimitedBinaryWords.Token → Token)
      (kind : constructor=Token.region ∨ constructor=Token.candidate ∨ constructor=Token.required)
      (tokens : List DelimitedBinaryWords.Token) :
      (tokens.map constructor).flatMap bitProjection=[] := by
    rcases kind with rfl|rfl|rfl <;> simp [List.flatMap_map,bitProjection]
  have bits (values : List Bool) : (values.map Token.bit).flatMap bitProjection=values := by
    induction values <;> simp_all [bitProjection]
  simp [Request.encode,List.flatMap_append,erase _ (Or.inl rfl),
    erase _ (Or.inr (Or.inl rfl)),erase _ (Or.inr (Or.inr rfl)),bits]

noncomputable def projectedComputableInPolyTime (role : Fin 3) :
    TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode
      (fun request => if role=0 then request.regionWords else
        if role=1 then request.candidateWords else request.requiredWords) := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare Request.encode
    (FiniteBlockTransducer.computableInPolyTime (wordProjection role))
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical
    (fun request => by
      change request.encode.flatMap (wordProjection role)=_
      rw [projection_encode]
      split_ifs <;> rfl)

noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime Request.encode id Request.bits := by
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare Request.encode
    (FiniteBlockTransducer.computableInPolyTime bitProjection)
    (fun _ => rfl) (fun _ => rfl)
  exact physical.of_eq bits_encode

theorem selected_map {Value Target : Type} (function : Value → Target)
    (bits : List Bool) (values : List Value) :
    DelimitedBinaryWordBooleanFilter.selected bits (values.map function)=
      (DelimitedBinaryWordBooleanFilter.selected bits values).map function := by
  induction bits generalizing values with
  | nil => rfl
  | cons bit bits ih =>
    cases values with
    | nil => rfl
    | cons value values => cases bit <;> simp [DelimitedBinaryWordBooleanFilter.selected,ih]

noncomputable def selectedBlocksComputableInPolyTime :
    TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode Request.selectedBlocks := by
  let candidates : TM2ComputableInPolyTime Request.encode
      DelimitedBinaryWords.finEncoding.encode Request.candidateWords :=
    (projectedComputableInPolyTime 1).of_eq (fun _ => by simp)
  let filtered := DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime
    Request.encode Request.bits Request.candidateWords bitsComputableInPolyTime candidates
  exact filtered.of_eq (fun request => by
    simp [DelimitedBinaryWordBooleanFilter.selectedWords,Request.candidateWords,
      Request.selectedBlocks,Request.selected,selected_map])

noncomputable def selectedCellsComputableInPolyTime :
    TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode Request.selectedCells := by
  let prepared : TM2ComputableInPolyTime Request.encode
      (fun blocks : List Block => DelimitedBinaryWords.encode ⟨blocks.map BinaryWordBlocks.pack⟩)
      Request.selected := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    selectedBlocksComputableInPolyTime (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime prepared BinaryWordBlocks.flattenComputableInPolyTime
  exact composed.of_eq (fun _ => rfl)

/-- Combine two scalar Boolean verifiers on the same input. -/
noncomputable def andComputableInPolyTime
    {Input InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol) (first second : Input → Bool)
    (firstCompiler : TM2ComputableInPolyTime encodeInput (fun bit : Bool => [bit]) first)
    (secondCompiler : TM2ComputableInPolyTime encodeInput (fun bit : Bool => [bit]) second) :
    TM2ComputableInPolyTime encodeInput (fun bit : Bool => [bit])
      (fun input => first input && second input) := by
  let forked := TM2ForkMachine.computableInPolyTime firstCompiler secondCompiler
  let erase : SeparatedProductEncoding.Token Bool Bool → List Bool
    | .left bit | .right bit => [bit]
    | .separator => []
  let encoder := SeparatedProductEncoding.encode (fun bit : Bool => [bit]) (fun bit : Bool => [bit])
  let projector := TM2PolyTimeInputEncodingTransport.of_prepare encoder
    (FiniteBlockTransducer.computableInPolyTime erase) (fun _ => rfl) (fun _ => rfl)
  let flattened := TM2CompositionMachine.computableInPolyTime forked projector
  let reduced := TM2CompositionMachine.computableInPolyTime flattened BinaryWordRowChecks.allComputableInPolyTime
  exact reduced.of_eq (fun input => by simp [encoder,SeparatedProductEncoding.encode,erase])

noncomputable def subsetCompiled (first second : Request → Words)
    (firstCompiler : TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode first)
    (secondCompiler : TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode second) :
    TM2ComputableInPolyTime Request.encode (fun bit : Bool => [bit])
      (fun request => BinaryWordSetChecks.subsetCheck (first request,second request)) :=
  TM2CompositionMachine.computableInPolyTime
    (TM2ForkMachine.computableInPolyTime firstCompiler secondCompiler)
    BinaryWordSetChecks.subsetComputableInPolyTime

noncomputable def computableInPolyTime (strict : Bool) :
    TM2ComputableInPolyTime Request.encode (fun bit : Bool => [bit]) (check strict) := by
  let region : TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode Request.regionWords :=
    (projectedComputableInPolyTime 0).of_eq (fun _ => by simp)
  let required : TM2ComputableInPolyTime Request.encode DelimitedBinaryWords.finEncoding.encode Request.requiredWords :=
    (projectedComputableInPolyTime 2).of_eq (fun _ => by simp)
  let disjoint := TM2CompositionMachine.computableInPolyTime selectedCellsComputableInPolyTime
    BinaryWordSetChecks.nodupComputableInPolyTime
  let covered := subsetCompiled Request.regionWords Request.selectedCells region selectedCellsComputableInPolyTime
  let retained := subsetCompiled Request.requiredWords Request.selectedBlocks required selectedBlocksComputableInPolyTime
  let first := andComputableInPolyTime Request.encode _ _ disjoint covered
  let completion := andComputableInPolyTime Request.encode _ _ first retained
  cases strict with
  | false => exact completion.of_eq (fun _ => by simp [check])
  | true =>
    let inside := subsetCompiled Request.selectedCells Request.regionWords selectedCellsComputableInPolyTime region
    let tiling := andComputableInPolyTime Request.encode _ _ completion inside
    exact tiling.of_eq (fun _ => by simp [check])

noncomputable def finiteAlphabetComputableInPolyTime (strict : Bool) :
    Complexity.FiniteAlphabetComputableInPolyTime Request.encode
      (fun bit : Bool => [bit]) (check strict) :=
  Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (computableInPolyTime strict)

end LeanTrominoes.FiniteExactCoverVerifier
