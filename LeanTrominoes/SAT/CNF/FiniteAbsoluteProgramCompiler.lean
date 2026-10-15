/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteAbsoluteProgram
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnPairCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryOptionalBlocksCompiler

/-! # Polynomial-time absolute-time program serialization

Finite instruction metadata and computed time/atom columns suffice to emit
exact native postorder fields. Optional payloads retain their row boundaries,
so constants, wires, and Boolean operators remain in the original order.
-/
noncomputable section
namespace LeanTrominoes.FiniteCNF.AbsoluteProgramCompiler
open Computability Turing PeriodicCNF UnaryColumn
open UnaryFieldEncoderMachine (unaryField unaryFields)

def instructionCode : TransitionInstruction → Nat
  | .constant false => 0
  | .constant true => 1
  | .wire ⟨.current,_⟩ => 2
  | .wire ⟨.next,_⟩ => 3
  | .negate => 4
  | .conjoin => 5
  | .disjoin => 6

def instructionAtom : TransitionInstruction → Nat
  | .wire wire => wire.atom
  | _ => 0

def nextBit : TransitionInstruction → Nat
  | .wire ⟨.next,_⟩ => 1
  | _ => 0

def isConstant : TransitionInstruction → Bool
  | .constant _ => true
  | _ => false

def isWire : TransitionInstruction → Bool
  | .wire _ => true
  | _ => false

def constantBit : TransitionInstruction → Nat
  | .constant true => 1
  | _ => 0

def opcode : TransitionInstruction → Nat
  | .constant _ => 0
  | .wire _ => 1
  | .negate => 2
  | .conjoin => 3
  | .disjoin => 4

private theorem finiteMetadata (instruction : TransitionInstruction) :
    instructionCode instruction < 7 := by
  cases instruction with
  | constant b => cases b <;> decide
  | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> simp [instructionCode]
  | negate | conjoin | disjoin => decide

variable {Source Row : Type} [Fintype Source] [Inhabited Source]
  {rows : List Source → List Row} {instruction : List Source → Row → TransitionInstruction}
  {time : List Source → Row → Nat}

/-- Finite metadata tables are implemented by an actual unary residue machine. -/
def metadata (codes : Compiler rows (fun s row => instructionCode (instruction s row)))
    (field : TransitionInstruction → Nat) (table : Fin 7 → Nat)
    (correct : ∀ inst, table ⟨instructionCode inst,finiteMetadata inst⟩=field inst) :
    Compiler rows (fun s row => field (instruction s row)) := by
  let physical := residue codes 7 (by decide) table
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  simpa only [Nat.mod_eq_of_lt (finiteMetadata (instruction s row))] using correct (instruction s row)

/-- Serialize the exact program body after fixing every wire's absolute time. -/
def computableInPolyTime
    (codes : Compiler rows (fun s row => instructionCode (instruction s row)))
    (atoms : Compiler rows (fun s row => instructionAtom (instruction s row)))
    (times : Compiler rows time) :
    TM2ComputableInPolyTime id unaryFields (fun s => (rows s).flatMap fun row =>
      (absoluteInstruction (time s row) (instruction s row)).fields) := by
  let operation := metadata codes opcode (fun code =>
      if code.val < 2 then 0 else if code.val < 4 then 1 else code.val-2) (by
    intro inst
    cases inst with
    | constant b => cases b <;> rfl
    | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> rfl
    | negate | conjoin | disjoin => rfl)
  let constants := metadata codes (fun inst => (isConstant inst).toNat)
      (fun code => if code.val < 2 then 1 else 0) (by
    intro inst
    cases inst with
    | constant b => cases b <;> rfl
    | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> rfl
    | negate | conjoin | disjoin => rfl)
  let wires := metadata codes (fun inst => (isWire inst).toNat)
      (fun code => if code.val=2 ∨ code.val=3 then 1 else 0) (by
    intro inst
    cases inst with
    | constant b => cases b <;> rfl
    | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> rfl
    | negate | conjoin | disjoin => rfl)
  let values := metadata codes constantBit (fun code => if code.val=1 then 1 else 0) (by
    intro inst
    cases inst with
    | constant b => cases b <;> rfl
    | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> rfl
    | negate | conjoin | disjoin => rfl)
  let nexts := metadata codes nextBit (fun code => if code.val=3 then 1 else 0) (by
    intro inst
    cases inst with
    | constant b => cases b <;> rfl
    | wire wire => rcases wire with ⟨slice,atom⟩; cases slice <;> rfl
    | negate | conjoin | disjoin => rfl)
  let constantFlags : TM2ComputableInPolyTime id id
      (fun s => (rows s).map fun row => isConstant (instruction s row)) :=
    TM2ComputableInPolyTime.of_eq (bits constants) (by
      intro s; apply List.map_congr_left; intro row _
      cases isConstant (instruction s row) <;> rfl)
  let wireFlags : TM2ComputableInPolyTime id id
      (fun s => (rows s).map fun row => isWire (instruction s row)) :=
    TM2ComputableInPolyTime.of_eq (bits wires) (by
      intro s; apply List.map_congr_left; intro row _
      cases isWire (instruction s row) <;> rfl)
  let absoluteAtoms := pair (add times nexts) atoms
  let literalValues := UnaryOptionalBlocks.compiler constantFlags (blocks values)
  let wireSlices := UnaryOptionalBlocks.compiler wireFlags (blocks (constant codes 0))
  let wireAtoms := UnaryOptionalBlocks.compiler wireFlags (blocks absoluteAtoms)
  let physical := finishBlocks (appendBlocks (blocks operation)
    (appendBlocks literalValues (appendBlocks wireSlices wireAtoms)))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  change (rows s).flatMap _=unaryFields ((rows s).flatMap _)
  induction rows s with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.flatMap_cons,UnaryFieldEncoderMachine.unaryFields_append,ih]
    congr 1
    cases instruction s row with
    | constant b => cases b <;> rfl
    | wire wire =>
        rcases wire with ⟨slice,atom⟩
        cases slice <;> simp [opcode,isConstant,isWire,constantBit,nextBit,instructionAtom,
          absoluteInstruction,absoluteWire,TransitionInstruction.fields,unaryFields,unaryField]
    | negate | conjoin | disjoin => rfl

end LeanTrominoes.FiniteCNF.AbsoluteProgramCompiler
