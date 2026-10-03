/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryProgramFieldTokenizer
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Uniform absolute-time token emission, including empty source alphabets -/
noncomputable section
namespace LeanTrominoes.FiniteCNF.AbsoluteTokenCompiler
open Computability Turing PeriodicCNF UnaryColumn UnaryProgramTokens
open UnaryFieldEncoderMachine (unaryFields)
variable {Source : Type} [Fintype Source]
  {program : List Source → TransitionProgram.Program} {time : List Source → Nat}

private def singleFields [Inhabited Source]
    (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s)))
    (clock : ScalarCompiler time) :
    TM2ComputableInPolyTime id unaryFields (fun s => transitionProgramFields
      ((program s).map (absoluteInstruction (time s)))) := by
  let codes := ProgramColumns.codes emitter
  let atoms := ProgramColumns.atoms emitter
  let times := broadcast codes clock
  let physical := AbsoluteProgramCompiler.computableInPolyTime codes atoms times
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp [transitionProgramFields,List.flatMap_map])

def single
    (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s)))
    (clock : ScalarCompiler time) :
    TM2ComputableInPolyTime id id (fun s => ofProgram
      ((program s).map (absoluteInstruction (time s)))) := by
  classical
  refine if nonempty : Nonempty Source then ?_ else ?_
  · letI : Inhabited Source := ⟨Classical.choice nonempty⟩
    exact UnaryProgramFieldTokenizer.ofFields (singleFields emitter clock)
  · letI : IsEmpty Source := not_nonempty_iff.mp nonempty
    let physical : TM2ComputableInPolyTime (id : List Source → List Source) id (fun _ => ofProgram ((program []).map (absoluteInstruction (time [])))) := TM2ConstantValueCompiler.computableInPolyTime id id
      (ofProgram ((program []).map (absoluteInstruction (time []))))
    exact TM2ComputableInPolyTime.of_eq physical (fun s => by
      have eq : s=[] := by cases s with | nil => rfl | cons symbol _ => exact isEmptyElim symbol
      subst s; rfl)

def repeated {count : List Source → Nat}
    (emitter : TM2ComputableInPolyTime id id (fun s => ofProgram (program s)))
    (bound : ScalarCompiler count) :
    TM2ComputableInPolyTime id id (fun s => ofProgram
      ((List.range (count s)).flatMap fun time => (program s).map (absoluteInstruction time))) := by
  classical
  refine if nonempty : Nonempty Source then ?_ else ?_
  · letI : Inhabited Source := ⟨Classical.choice nonempty⟩
    let fields := ProgramColumns.repeated emitter bound
    let joined : TM2ComputableInPolyTime id unaryFields (fun s => transitionProgramFields ((List.range (count s)).flatMap fun time => (program s).map (absoluteInstruction time))) := TM2ComputableInPolyTime.of_eq fields (fun s => by
      simp [transitionProgramFields,List.flatMap_assoc])
    exact UnaryProgramFieldTokenizer.ofFields joined
  · letI : IsEmpty Source := not_nonempty_iff.mp nonempty
    let physical : TM2ComputableInPolyTime (id : List Source → List Source) id (fun _ => ofProgram ((List.range (count [])).flatMap fun time => (program []).map (absoluteInstruction time))) := TM2ConstantValueCompiler.computableInPolyTime id id
      (ofProgram ((List.range (count [])).flatMap fun time => (program []).map (absoluteInstruction time)))
    exact TM2ComputableInPolyTime.of_eq physical (fun s => by
      have eq : s=[] := by cases s with | nil => rfl | cons symbol _ => exact isEmptyElim symbol
      subst s; rfl)

end LeanTrominoes.FiniteCNF.AbsoluteTokenCompiler
