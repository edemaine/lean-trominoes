/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Printing occurrence copies from finite profiles and unary atom numbers -/
namespace LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
open UnaryProgramClauseProfile UnaryProgramTokens

abbrev Metadata := Option (Fin 4) × LiteralProfile
abbrev Payload := Metadata ⊕ UnaryFieldEncoderMachine.Symbol
abbrev InputToken := FiniteAlphabetDelimitedBlockJoin.Token Payload

def initial : Metadata := (none,⟨false,false⟩)
def header (m : Metadata) : List Token :=
  match m.1 with
  | none => []
  | some n => .clauseMarker :: CountedUnaryFieldTokens.field n.val

def suffix (m : Metadata) : List Token :=
  CountedUnaryFieldTokens.fields [if m.2.nextSlice then 2 else 0,0,m.2.value.toNat]

def literalBlock (m : Metadata) (atom : Nat) : List Token :=
  header m ++ CountedUnaryFieldTokens.field atom ++ suffix m

def transition (m : Metadata) : InputToken → Metadata × List Token
  | .value (.inl next) => (next,header next)
  | .value (.inr .unit) => (m,[.atomUnit])
  | .value (.inr .delimiter) => (m,[])
  | .blockEnd => (initial,.atomEnd :: suffix m)

def finish (_ : Metadata) : List Token := []
def output (input : List InputToken) : List Token :=
  FiniteStateTransducer.output initial transition finish input

def prefixBlock (m : Metadata) : List InputToken := [.value (.inl m),.blockEnd]
def atomBlock (atom : Nat) : List InputToken :=
  List.replicate atom (.value (.inr .unit)) ++ [.blockEnd]
def record (m : Metadata) (atom : Nat) : List InputToken :=
  .value (.inl m) :: atomBlock atom

private theorem scan_units (m : Metadata) (n : Nat) :
    FiniteStateTransducer.scan transition m (List.replicate n (.value (.inr .unit))) =
      (m,List.replicate n .atomUnit) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,FiniteStateTransducer.scan,transition,ih]

theorem scan_record (m state : Metadata) (atom : Nat) :
    FiniteStateTransducer.scan transition state (record m atom) =
      (initial,literalBlock m atom) := by
  simp only [record,FiniteStateTransducer.scan,transition,atomBlock]
  rw [FiniteStateTransducer.scan_append,scan_units]
  simp [FiniteStateTransducer.scan,transition,literalBlock,CountedUnaryFieldTokens.field,
    atomTokens,List.append_assoc]

theorem output_records (pairs : List (Metadata × Nat)) :
    output (pairs.flatMap fun p => record p.1 p.2) =
      pairs.flatMap (fun p => literalBlock p.1 p.2) := by
  have scan (state : Metadata) :
      (FiniteStateTransducer.scan transition state (pairs.flatMap fun p => record p.1 p.2)).2 =
        pairs.flatMap (fun p => literalBlock p.1 p.2) := by
    induction pairs generalizing state with
    | nil => rfl
    | cons p pairs ih =>
      rw [List.flatMap_cons,FiniteStateTransducer.scan_append,scan_record]
      simpa only [List.flatMap_cons] using congrArg (literalBlock p.1 p.2 ++ ·) (ih initial)
  simpa [output,FiniteStateTransducer.output,finish] using scan initial

noncomputable def computableInPolyTime : Turing.TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end LeanTrominoes.PeriodicCNF.SplitLiteralPrinter
