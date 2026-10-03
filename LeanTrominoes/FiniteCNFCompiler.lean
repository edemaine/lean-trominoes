/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAbsoluteExpression
import LeanTrominoes.FiniteCNFWidth
import LeanTrominoes.PeriodicCNFTransitionEvaluatorTime
import LeanTrominoes.FiniteAlphabetPolyTime

/-! # A native quadratic-time compiler for ordinary finite CNF

All input wires refer to one ordinary Boolean assignment. The verified native
structural compiler then emits zero-offset clauses, which encode ordinary
finite formulas without any periodic satisfiability requirement.
-/
namespace LeanTrominoes.FiniteCNFCompiler
open Turing PeriodicCNF

def erase (formula : PeriodicCNF Nat) : FiniteCNF.Formula Nat :=
  formula.clauses.map fun clause => clause.map fun literal => (literal.atom,literal.value)

@[simp] theorem erase_periodize (formula : FiniteCNF.Formula Nat) :
    erase (FiniteCNF.periodize formula)=formula := by
  simp [erase,FiniteCNF.periodize,List.map_map,Function.comp_def]

def ZeroOffsets (clauses : List (PeriodicClause Nat)) : Prop :=
  ∀ clause∈clauses, ∀ literal∈clause, literal.offset=(0,0)

theorem periodize_erase (formula : PeriodicCNF Nat) (zero : ZeroOffsets formula.clauses) :
    FiniteCNF.periodize (erase formula)=formula := by
  cases formula with
  | mk clauses =>
    simp only [FiniteCNF.periodize,erase,List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id clauses]
    apply List.map_congr_left
    intro clause member
    simp only [Function.comp_def,List.map_map,id_eq]
    conv_rhs => rw [← List.map_id clause]
    apply List.map_congr_left
    intro literal hl
    cases literal with
    | mk atom offset value =>
      simpa using congrArg (fun offset => (⟨atom,offset,value⟩ : PeriodicLiteral Nat)) (zero clause member _ hl).symm

theorem compiled_zeroOffsets (expression : TransitionExpr) (fresh : Nat) :
    ZeroOffsets (compileTransitionExpr expression.atCurrent fresh).clauses := by
  induction expression generalizing fresh with
  | constant b => simp [ZeroOffsets,TransitionExpr.atCurrent,compileTransitionExpr,constantClauses,gateOutput,TransitionWire.literal]
  | wire w => simp [ZeroOffsets,TransitionExpr.atCurrent,compileTransitionExpr,equalityClauses,gateOutput,TransitionWire.literal]
  | not e ih =>
    simp only [TransitionExpr.atCurrent,compileTransitionExpr]
    intro clause member literal hl
    rcases List.mem_append.mp member with old|gate
    · exact ih fresh clause old literal hl
    · simp only [notClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl <;> simp_all [gateOutput,TransitionWire.literal] <;> aesop
  | and e f ih1 ih2 =>
    simp only [TransitionExpr.atCurrent,compileTransitionExpr]
    intro clause member literal hl
    rcases List.mem_append.mp member with old|gate
    · rcases List.mem_append.mp old with left|right
      · exact ih1 fresh clause left literal hl
      · exact ih2 _ clause right literal hl
    · simp only [andClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl|rfl <;> simp_all [gateOutput,TransitionWire.literal] <;> aesop
  | or e f ih1 ih2 =>
    simp only [TransitionExpr.atCurrent,compileTransitionExpr]
    intro clause member literal hl
    rcases List.mem_append.mp member with old|gate
    · rcases List.mem_append.mp old with left|right
      · exact ih1 fresh clause left literal hl
      · exact ih2 _ clause right literal hl
    · simp only [orClauses,List.mem_cons,List.not_mem_nil,or_false] at gate
      rcases gate with rfl|rfl|rfl <;> simp_all [gateOutput,TransitionWire.literal] <;> aesop

theorem required_zeroOffsets (expression : TransitionExpr) (fresh : Nat) :
    ZeroOffsets (requireTransitionExpr expression.atCurrent fresh).clauses := by
  intro clause member literal hl
  rcases List.mem_append.mp member with old|root
  · exact compiled_zeroOffsets expression fresh clause old literal hl
  · simp_all [constantClauses,gateOutput,TransitionWire.literal]

theorem erase_satisfies_iff (formula : PeriodicCNF Nat) (zero : ZeroOffsets formula.clauses)
    (assignment : Nat → Bool) (next : Nat → Bool) :
    FiniteCNF.Satisfies (erase formula) assignment ↔ formula.Transition assignment next := by
  constructor
  · intro h clause member
    obtain ⟨mapped,hm,truth⟩ := h _ (List.mem_map.mpr ⟨clause,member,rfl⟩)
    obtain ⟨literal,hl,rfl⟩ := List.mem_map.mp hm
    exact ⟨literal,hl,by simpa [PeriodicLiteral.HoldsBetween,zero clause member literal hl] using truth⟩
  · intro h clause member
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
    obtain ⟨literal,hl,truth⟩ := h original ho
    exact ⟨(literal.atom,literal.value),List.mem_map.mpr ⟨literal,hl,rfl⟩,
      by simpa [PeriodicLiteral.HoldsBetween,zero original ho literal hl] using truth⟩

def fields (formula : FiniteCNF.Formula Nat) : List Nat :=
  PeriodicCNFFlatEncoding.formulaFields (FiniteCNF.periodize formula)

def decodeFields (fields : List Nat) : Option (FiniteCNF.Formula Nat) :=
  (PeriodicCNFFlatEncoding.decodeFormulaFields fields).map erase

@[simp] theorem decodeFields_fields (formula : FiniteCNF.Formula Nat) :
    decodeFields (fields formula)=some formula := by simp [decodeFields,fields]

def finEncoding : _root_.Computability.FinEncoding (FiniteCNF.Formula Nat) :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decodeFields decodeFields_fields

structure Request where
  expression : TransitionExpr
  fresh : Nat
  sourceBound : expression.AtomsBelow fresh

def Request.native (request : Request) : TransitionEvaluatorMachine.TransitionCompilerRequest :=
  ⟨request.expression.atCurrent,request.fresh,TransitionExpr.atCurrent_atomsBelow request.sourceBound⟩

def Request.encode (request : Request) : List PartrecToTM2.Γ' := request.native.encode

def Request.compile (request : Request) : FiniteCNF.Formula Nat :=
  erase (requireTransitionExpr request.expression.atCurrent request.fresh)

theorem Request.correct (request : Request) :
    FiniteCNF.Satisfiable request.compile ↔
      ∃ assignment : Nat → Bool, request.expression.eval assignment assignment=true := by
  constructor
  · rintro ⟨assignment,truth⟩
    refine ⟨assignment,?_⟩
    have transition := (erase_satisfies_iff _ (required_zeroOffsets _ _) assignment assignment).mp truth
    simpa only [TransitionExpr.atCurrent_eval] using requireTransitionExpr_transition_sound _ _ transition
  · rintro ⟨assignment,truth⟩
    obtain ⟨realized,_,transition⟩ := requireTransitionExpr_transition_complete request.expression.atCurrent request.fresh
      (TransitionExpr.atCurrent_atomsBelow request.sourceBound)
      (by simpa only [TransitionExpr.atCurrent_eval] using truth)
    exact ⟨realized,(erase_satisfies_iff _ (required_zeroOffsets _ _) realized assignment).mpr transition⟩

theorem Request.width (request : Request) : FiniteCNF.WidthAtMost 3 request.compile := by
  intro clause member
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
  simpa using FiniteCNF.required_width request.expression.atCurrent request.fresh original ho

/-- This is the physical native structural compiler, presented at its finite
formula codomain. Its running time is at most 400*(input length+1)^2. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime Request.encode finEncoding.encode Request.compile := by
  let physical := TransitionEvaluatorMachine.computableInPolyTime
  refine
    { tm := physical.tm
      inputAlphabet := physical.inputAlphabet
      outputAlphabet := physical.outputAlphabet
      time := physical.time
      outputsFun := ?_ }
  intro request
  have encoded : finEncoding.encode request.compile=PartrecToTM2.trList request.native.compile := by
    change PeriodicCNFFlatEncoding.encodeNatFields
      (PeriodicCNFFlatEncoding.formulaFields
        (FiniteCNF.periodize (erase (requireTransitionExpr request.expression.atCurrent request.fresh))))=
      PartrecToTM2.trList (requireTransitionExprFields request.expression.atCurrent request.fresh)
    rw [periodize_erase _ (required_zeroOffsets _ _),requireTransitionExprFields_eq_formulaFields]
    exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _
  convert physical.outputsFun request.native using 1 <;> try rfl
  rw [encoded]
  rfl

noncomputable def finiteAlphabetComputableInPolyTime :
    Complexity.FiniteAlphabetComputableInPolyTime Request.encode finEncoding.encode Request.compile :=
  Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime computableInPolyTime

theorem compiler_time (length : Nat) : computableInPolyTime.time.eval length=400*(length+1)^2 :=
  TransitionEvaluatorMachine.transitionTimePolynomial_eval length

end LeanTrominoes.FiniteCNFCompiler
