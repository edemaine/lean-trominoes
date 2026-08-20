/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionProgramLiteralCount
import LeanTrominoes.PeriodicCNFUnaryProgramTokens

/-! # Unary orthocrossing-grid units from transition-program tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace StripGridUnitTokens

open UnaryProgramTokens

def constantWeight : Nat := 16 * (1 + 5 * 1)
def wireWeight : Nat := 16 * (2 + 5 * 4)
def negateWeight : Nat := 16 * (2 + 5 * 4)
def binaryWeight : Nat := 16 * (3 + 5 * 7)

theorem constantWeight_eq : constantWeight = 16 * (1 + 5 * 1) := rfl
theorem wireWeight_eq : wireWeight = 16 * (2 + 5 * 4) := rfl
theorem negateWeight_eq : negateWeight = 16 * (2 + 5 * 4) := rfl
theorem binaryWeight_eq : binaryWeight = 16 * (3 + 5 * 7) := rfl

/-- Fixed block emitted by one request token.  Instruction tags carry their
exact clause-plus-five-literal contribution; the unique fresh-field terminator
carries the forced-root contribution and the generic grid margin. -/
def block : UnaryProgramTokens.Token → List Unit
  | .clauseMarker => []
  | .constant _ => List.replicate constantWeight ()
  | .wireStart _ => List.replicate wireWeight ()
  | .atomUnit => []
  | .atomEnd => []
  | .freshUnit => []
  | .freshEnd => List.replicate (16 * 7) ()
  | .negate => List.replicate negateWeight ()
  | .conjoin => List.replicate binaryWeight ()
  | .disjoin => List.replicate binaryWeight ()

def gridUnits (tokens : List UnaryProgramTokens.Token) : List Unit :=
  tokens.flatMap block

@[simp] theorem gridUnits_append (first second : List Token) :
    gridUnits (first ++ second) = gridUnits first ++ gridUnits second := by
  simp [gridUnits]

theorem gridUnits_replicate_of_block_nil (token : Token)
    (empty : block token = []) (count : Nat) :
    gridUnits (List.replicate count token) = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change block token ++
        gridUnits (List.replicate count token) = []
      rw [empty, induction]
      rfl

theorem gridUnits_singleton_constant (value : Bool) :
    gridUnits [.constant value] = List.replicate constantWeight () := by
  change List.replicate constantWeight () ++ [] = _
  rw [List.append_nil]

theorem gridUnits_singleton_wireStart (nextSlice : Bool) :
    gridUnits [.wireStart nextSlice] = List.replicate wireWeight () := by
  change List.replicate wireWeight () ++ [] = _
  rw [List.append_nil]

theorem gridUnits_singleton_atomEnd :
    gridUnits [.atomEnd] = [] := by
  change [] ++ [] = []
  rfl

theorem gridUnits_singleton_negate :
    gridUnits [.negate] = List.replicate negateWeight () := by
  change List.replicate negateWeight () ++ [] = _
  rw [List.append_nil]

theorem gridUnits_singleton_conjoin :
    gridUnits [.conjoin] = List.replicate binaryWeight () := by
  change List.replicate binaryWeight () ++ [] = _
  rw [List.append_nil]

theorem gridUnits_singleton_disjoin :
    gridUnits [.disjoin] = List.replicate binaryWeight () := by
  change List.replicate binaryWeight () ++ [] = _
  rw [List.append_nil]

@[simp] theorem gridUnits_clauseTokens (count : Nat) :
    gridUnits (clauseTokens count) = [] := by
  unfold clauseTokens
  exact gridUnits_replicate_of_block_nil .clauseMarker rfl count

@[simp] theorem gridUnits_atomTokens (atom : Nat) :
    gridUnits (atomTokens atom) = [] := by
  unfold atomTokens
  exact gridUnits_replicate_of_block_nil .atomUnit rfl atom

@[simp] theorem gridUnits_instructionTokens
    (instruction : TransitionInstruction) :
    gridUnits (instructionTokens instruction) =
      List.replicate
        (16 * (instruction.clauseCount +
          5 * instruction.literalCount)) () := by
  cases instruction with
  | constant value =>
      unfold instructionTokens
      rw [gridUnits_append, gridUnits_clauseTokens,
        List.nil_append, gridUnits_singleton_constant]
      change List.replicate constantWeight () =
        List.replicate (16 * (1 + 5 * 1)) ()
      exact congrArg (fun count => List.replicate count ())
        constantWeight_eq
  | wire input =>
      rcases input with ⟨slice, atom⟩
      cases slice <;>
        unfold instructionTokens <;>
        simp only [gridUnits_append, gridUnits_clauseTokens,
          gridUnits_atomTokens, gridUnits_singleton_wireStart,
          gridUnits_singleton_atomEnd, List.nil_append,
          List.append_nil] <;>
        change List.replicate wireWeight () =
          List.replicate (16 * (2 + 5 * 4)) () <;>
        exact congrArg (fun count => List.replicate count ())
          wireWeight_eq
  | negate =>
      unfold instructionTokens
      rw [gridUnits_append, gridUnits_clauseTokens,
        List.nil_append, gridUnits_singleton_negate]
      change List.replicate negateWeight () =
        List.replicate (16 * (2 + 5 * 4)) ()
      exact congrArg (fun count => List.replicate count ())
        negateWeight_eq
  | conjoin =>
      unfold instructionTokens
      rw [gridUnits_append, gridUnits_clauseTokens,
        List.nil_append, gridUnits_singleton_conjoin]
      change List.replicate binaryWeight () =
        List.replicate (16 * (3 + 5 * 7)) ()
      exact congrArg (fun count => List.replicate count ())
        binaryWeight_eq
  | disjoin =>
      unfold instructionTokens
      rw [gridUnits_append, gridUnits_clauseTokens,
        List.nil_append, gridUnits_singleton_disjoin]
      change List.replicate binaryWeight () =
        List.replicate (16 * (3 + 5 * 7)) ()
      exact congrArg (fun count => List.replicate count ())
        binaryWeight_eq

@[simp] theorem gridUnits_ofProgram (program : TransitionProgram.Program) :
    gridUnits (ofProgram program) =
      List.replicate
        (16 * (TransitionProgram.clauseCount program +
          5 * TransitionProgram.literalCount program)) () := by
  induction program with
  | nil => rfl
  | cons instruction program induction =>
      rw [show ofProgram (instruction :: program) =
          instructionTokens instruction ++ ofProgram program by rfl,
        gridUnits_append, gridUnits_instructionTokens, induction,
        ← List.replicate_add]
      congr 1
      simp only [TransitionProgram.clauseCount,
        TransitionProgram.literalCount, List.map_cons, List.sum_cons]
      omega

@[simp] theorem gridUnits_freshTokens (fresh : Nat) :
    gridUnits (freshTokens fresh) = List.replicate (16 * 7) () := by
  unfold freshTokens
  rw [gridUnits_append]
  rw [gridUnits_replicate_of_block_nil .freshUnit rfl]
  rfl

/-- The request token stream expands to exactly the generic orthocrossing
scale `16 * (clauses + 5 * literals + 7)`. -/
@[simp] theorem gridUnits_requestSource (fresh : Nat)
    (program : TransitionProgram.Program) :
    gridUnits (requestSource fresh program) =
      List.replicate
        (16 * (TransitionProgram.clauseCount program +
          5 * TransitionProgram.literalCount program + 7)) () := by
  unfold requestSource
  rw [gridUnits_append, gridUnits_freshTokens]
  rw [show gridUnits (.clauseMarker :: ofProgram program) =
      gridUnits (ofProgram program) by rfl,
    gridUnits_ofProgram, ← List.replicate_add]
  congr 1
  omega

end StripGridUnitTokens
end PeriodicCNF
end LeanTrominoes
