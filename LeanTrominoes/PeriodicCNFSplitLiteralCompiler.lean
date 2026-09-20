/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSplitLiteralPrinter
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time assembly of aligned literal profiles and atom numbers -/
noncomputable section
namespace LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
open Turing UnaryFieldEncoderMachine FiniteAlphabetDelimitedBlockJoin

def atomToken : Symbol → List InputToken
  | .unit => [.value (.inr .unit)]
  | .delimiter => [.blockEnd]

def atomTokens (symbols : List Symbol) : List InputToken := symbols.flatMap atomToken

theorem atomTokens_field (n : Nat) : atomTokens (unaryField n) = atomBlock n := by
  unfold atomTokens unaryField atomBlock
  simp [List.flatMap_append,atomToken,List.flatMap_replicate,List.replicate_append_replicate]

theorem atomTokens_fields (ns : List Nat) :
    atomTokens (unaryFields ns) = ns.flatMap atomBlock := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    rw [unaryFields_cons]
    change atomTokens (unaryField n ++ unaryFields ns) = _
    simp only [atomTokens,List.flatMap_append] at *
    rw [show (unaryField n).flatMap atomToken=atomBlock n from atomTokens_field n,ih]
    rfl

theorem joined_records (pairs : List (Metadata × Nat)) :
    joined (pairs.flatMap fun p => prefixBlock p.1) (pairs.flatMap fun p => atomBlock p.2) =
      pairs.flatMap fun p => record p.1 p.2 := by
  have h := joined_pairedBlocks (pairs.map fun p =>
    ([(Sum.inl p.1 : Payload)],List.replicate p.2 (Sum.inr Symbol.unit : Payload)))
  simpa [blocks,block,prefixBlock,atomBlock,record,List.map_replicate,List.flatMap_map,
    List.map_map,Function.comp_def,List.map_cons,List.map_nil] using h

theorem joined_zip (ms : List Metadata) (ns : List Nat) (aligned : ms.length=ns.length) :
    output (joined (ms.flatMap prefixBlock) (ns.flatMap atomBlock)) =
      (ms.zip ns).flatMap fun p => literalBlock p.1 p.2 := by
  have hm : (ms.zip ns).map Prod.fst=ms := List.map_fst_zip (by omega)
  have hn : (ms.zip ns).map Prod.snd=ns := List.map_snd_zip (by omega)
  have h := joined_records (ms.zip ns)
  have a : (ms.zip ns).flatMap (fun p => prefixBlock p.1)=ms.flatMap prefixBlock := by
    rw [← List.flatMap_map,hm]
  have b : (ms.zip ns).flatMap (fun p => atomBlock p.2)=ns.flatMap atomBlock := by
    rw [← List.flatMap_map,hn]
  rw [a,b] at h
  rw [h,output_records]

noncomputable def assembleComputableInPolyTime
    {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (encode : Source → List InputSymbol)
    (metadata : Source → List Metadata) (atoms : Source → List Nat)
    (aligned : ∀ source, (metadata source).length=(atoms source).length)
    (metaCompiler : TM2ComputableInPolyTime encode id metadata)
    (atomCompiler : TM2ComputableInPolyTime encode unaryFields atoms) :
    TM2ComputableInPolyTime encode id
      (fun source => ((metadata source).zip (atoms source)).flatMap fun p => literalBlock p.1 p.2) := by
  let prefixes := TM2CompositionMachine.computableInPolyTime metaCompiler
    (FiniteBlockTransducer.computableInPolyTime prefixBlock)
  let physicalAtoms := TM2CompositionMachine.computableInPolyTime atomCompiler
    (TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
      (FiniteBlockTransducer.computableInPolyTime atomToken) (fun _ => rfl) (fun _ => rfl))
  have suffixes : TM2ComputableInPolyTime encode id (fun s => (atoms s).flatMap atomBlock) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physicalAtoms
      (fun s => atomTokens_fields (atoms s))
  let paired := joinedComputableInPolyTimeOf encode
    (fun s => (metadata s).flatMap prefixBlock) (fun s => (atoms s).flatMap atomBlock)
    prefixes suffixes
  let printed := TM2CompositionMachine.computableInPolyTime paired computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq printed
    (fun s => joined_zip (metadata s) (atoms s) (aligned s))

end LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
end
