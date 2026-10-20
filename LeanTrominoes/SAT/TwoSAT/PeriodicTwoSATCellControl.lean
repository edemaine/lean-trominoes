/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawControl

/-! # Word checks for the complete original-input table expression -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM

structure Context {d : ℕ} (base : ℕ) (raw : Raw.LocalInput d) (sourceBase : ℕ)
    (env : Fin 17 → ℤ) (memory : ℕ → ℤ) : Prop where
  source : Raw.SourceAt raw.val sourceBase memory
  sourceValue : env 5=sourceBase
  clauseCount : env 7=raw.val.2.length
  parameters : ∀ i, i≠0 → (env i).natAbs≤base
  recordSize : Raw.recordSize d≤base
  variableBound : raw.val.1+1≤base

variable {d base sourceBase : ℕ} {raw : Raw.LocalInput d} {env : Fin 17 → ℤ} {memory : ℕ → ℤ}
variable (ctx : Context base raw sourceBase env memory)

abbrev Context.Good (_ctx : Context base raw sourceBase env memory) (e : Expression) : Prop := Controlled base env memory (Raw.words raw.val) e

include ctx

theorem Context.minimum : 5≤base := by have h := ctx.recordSize; dsimp [Raw.recordSize] at h; omega

macro "two_sat_control_arithmetic" params:term : tactic =>
  `(tactic| repeat' first
    | assumption
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact ($params) _ (by decide)
    | apply Controlled.constant; norm_num <;> omega)

theorem Context.recordGood (clause : Expression) (clauseGood : ctx.Good clause) (j : ℕ) (inside : j<5) :
    ctx.Good (record d clause (constant j)) :=
  Raw.record_controlled raw.val sourceBase env memory ctx.source ctx.sourceValue ctx.clauseCount
    ctx.parameters ctx.recordSize (by have := ctx.minimum; omega) ctx.variableBound clause clauseGood j inside

theorem Context.differenceGood (clause : Expression) (clauseGood : ctx.Good clause) (j : Fin d) :
    ctx.Good (sub (record d clause (constant (5+d+j.val))) (record d clause (constant (5+j.val)))) :=
  Raw.difference_controlled raw sourceBase env memory ctx.source ctx.sourceValue ctx.clauseCount
    ctx.parameters ctx.recordSize (by have := ctx.minimum; omega) clause clauseGood j

theorem Context.reverseDifferenceGood (clause : Expression) (clauseGood : ctx.Good clause) (j : Fin d) :
    ctx.Good (sub (record d clause (constant (5+j.val))) (record d clause (constant (5+d+j.val)))) :=
  Raw.reverse_difference_controlled raw sourceBase env memory ctx.source ctx.sourceValue ctx.clauseCount
    ctx.parameters ctx.recordSize (by have := ctx.minimum; omega) clause clauseGood j

theorem Context.powerGood (j : ℕ) : ctx.Good (power j) := by
  have minimum := ctx.minimum
  induction j with
  | zero => simp only [power]; two_sat_control_arithmetic ctx.parameters
  | succ j ih => simp only [power]; two_sat_control_arithmetic ctx.parameters

theorem Context.directionGood (e : Expression) (good : ctx.Good e) : ctx.Good (direction e) := by
  have minimum := ctx.minimum
  simp only [direction,mod,constant]
  two_sat_control_arithmetic ctx.parameters

theorem Context.rowGood (e : Expression) (good : ctx.Good e) : ctx.Good (row e) := by
  have minimum := ctx.minimum
  simp only [row,mod,div,two,mul,constant,clauses,coordinates,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.clauseIndexGood (e : Expression) (good : ctx.Good e) : ctx.Good (clauseIndex e) := by
  have minimum := ctx.minimum
  simp only [clauseIndex,div,mod,two,mul,constant,clauses,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.sourceLiteralGood (e : Expression) (good : ctx.Good e) : ctx.Good (sourceLiteral d e) := by
  have minimum := ctx.minimum
  have clause := ctx.clauseIndexGood e good
  have sign := ctx.directionGood e good
  have a := ctx.recordGood (clauseIndex e) clause 1 (by decide)
  have b := ctx.recordGood (clauseIndex e) clause 2 (by decide)
  have c := ctx.recordGood (clauseIndex e) clause 3 (by decide)
  have f := ctx.recordGood (clauseIndex e) clause 4 (by decide)
  simp only [sourceLiteral,add,mul,two,complement,sub,constant]
  two_sat_control_arithmetic ctx.parameters

theorem Context.targetLiteralGood (e : Expression) (good : ctx.Good e) : ctx.Good (targetLiteral d e) := by
  have minimum := ctx.minimum
  have clause := ctx.clauseIndexGood e good
  have sign := ctx.directionGood e good
  have a := ctx.recordGood (clauseIndex e) clause 1 (by decide)
  have b := ctx.recordGood (clauseIndex e) clause 2 (by decide)
  have c := ctx.recordGood (clauseIndex e) clause 3 (by decide)
  have f := ctx.recordGood (clauseIndex e) clause 4 (by decide)
  simp only [targetLiteral,add,mul,two,constant]
  two_sat_control_arithmetic ctx.parameters

theorem Context.displacementGood (e : Expression) (good : ctx.Good e) (j : Fin d) :
    ctx.Good (displacement d e j) := by
  have minimum := ctx.minimum
  have clause := ctx.clauseIndexGood e good
  have sign := ctx.directionGood e good
  have forward := ctx.differenceGood (clauseIndex e) clause j
  have backward := ctx.reverseDifferenceGood (clauseIndex e) clause j
  simp only [displacement,add,mul,complement,sub,constant]
  two_sat_control_arithmetic ctx.parameters

theorem Context.shiftedGood (e : Expression) (good : ctx.Good e) : ctx.Good (shifted d e) := by
  have minimum := ctx.minimum
  unfold shifted
  generalize List.finRange d=items
  induction items with
  | nil => simp only [List.foldr_nil,constant]; two_sat_control_arithmetic ctx.parameters
  | cons j items ih =>
    have coordinate := ctx.rowGood e good
    have powerGood := ctx.powerGood j.val
    have delta := ctx.displacementGood e good j
    simp only [List.foldr_cons,add,mul,mod,div,period,input]
    two_sat_control_arithmetic ctx.parameters

theorem Context.sourceVertexGood (e : Expression) (good : ctx.Good e) : ctx.Good (sourceVertex d e) := by
  have minimum := ctx.minimum
  have clause := ctx.clauseIndexGood e good
  have flagGood := ctx.recordGood (clauseIndex e) clause 0 (by decide)
  have literal := ctx.sourceLiteralGood e good
  have coordinate := ctx.rowGood e good
  simp only [sourceVertex,flag,add,mul,constant,coordinates,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.targetVertexGood (e : Expression) (good : ctx.Good e) : ctx.Good (targetVertex d e) := by
  have minimum := ctx.minimum
  have clause := ctx.clauseIndexGood e good
  have flagGood := ctx.recordGood (clauseIndex e) clause 0 (by decide)
  have literal := ctx.targetLiteralGood e good
  have coordinate := ctx.shiftedGood e good
  simp only [targetVertex,flag,add,mul,constant,coordinates,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.selectGood (a b yes no : Expression) (aGood : ctx.Good a) (bGood : ctx.Good b)
    (yesGood : ctx.Good yes) (noGood : ctx.Good no) : ctx.Good (select a b yes no) := by
  have minimum := ctx.minimum
  simp only [select,Expr.selectLt,Expr.indicator,increment,add,outputLength,input,constant]
  two_sat_control_arithmetic ctx.parameters

theorem Context.sourceFactGood (block : Expression) (good : ctx.Good block) : ctx.Good (sourceFact block) := by
  have minimum := ctx.minimum
  have sign := ctx.directionGood block good
  simp only [sourceFact,increment,add,mul,two,div,complement,sub,constant,vertices,coordinates,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.oppositeTargetGood (block : Expression) (good : ctx.Good block) : ctx.Good (oppositeTarget block) := by
  have minimum := ctx.minimum
  have sign := ctx.directionGood block good
  simp only [oppositeTarget,increment,add,mul,two,div,constant,vertices,coordinates,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.unaryHeadGood (i : Expression) (good : ctx.Good i) : ctx.Good (unaryHead d i) := by
  have minimum := ctx.minimum
  have edgeGood : ctx.Good (mod i edges) := by
    simp only [mod,edges,input]
    two_sat_control_arithmetic ctx.parameters
  have vertex := ctx.targetVertexGood (mod i edges) edgeGood
  simp only [unaryHead,increment,add,mul,div,constant,vertices,edges,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.unaryAtomGood (i : Expression) (good : ctx.Good i) : ctx.Good (unaryAtom d i) := by
  have minimum := ctx.minimum
  have edgeGood : ctx.Good (mod i edges) := by
    simp only [mod,edges,input]
    two_sat_control_arithmetic ctx.parameters
  have vertex := ctx.sourceVertexGood (mod i edges) edgeGood
  simp only [unaryAtom,increment,add,mul,div,constant,vertices,edges,input]
  two_sat_control_arithmetic ctx.parameters

theorem Context.headCellGood (i : Expression) (good : ctx.Good i) : ctx.Good (headCell d i) := by
  have minimum := ctx.minimum
  have unaryIndex : ctx.Good (mask (sub i (three numVars))) := by
    simp only [mask,sub,three,mul,constant,numVars,outputLength,input]
    two_sat_control_arithmetic ctx.parameters
  have markerIndex : ctx.Good (sub i (add (three numVars) (mul (two numVars) edges))) := by
    simp only [sub,add,three,two,mul,constant,numVars,edges,input]
    two_sat_control_arithmetic ctx.parameters
  have fact := ctx.sourceFactGood i good
  have unary := ctx.unaryHeadGood (mask (sub i (three numVars))) unaryIndex
  have marked := ctx.recordGood _ markerIndex 0 (by decide)
  simp only [headCell]
  repeat' first
    | assumption
    | apply Context.selectGood ctx
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact ctx.parameters _ (by decide)
    | apply Controlled.constant; norm_num <;> omega

theorem Context.atomCellGood (i : Expression) (good : ctx.Good i) : ctx.Good (atomCell d i) := by
  have minimum := ctx.minimum
  have unaryIndex : ctx.Good (mask (sub i (two numVars))) := by
    simp only [mask,sub,two,mul,constant,numVars,outputLength,input]
    two_sat_control_arithmetic ctx.parameters
  have opposite := ctx.oppositeTargetGood i good
  have unary := ctx.unaryAtomGood _ unaryIndex
  simp only [atomCell]
  repeat' first
    | assumption
    | apply Context.selectGood ctx
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact ctx.parameters _ (by decide)
    | apply Controlled.constant; norm_num <;> omega

theorem Context.ruleCellGood (i : Expression) (good : ctx.Good i) : ctx.Good (ruleCell i) := by
  have minimum := ctx.minimum
  simp only [ruleCell,add,two,three,mul,div,mask,sub,constant,numVars,outputLength,input]
  repeat' first
    | assumption
    | apply Context.selectGood ctx
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact ctx.parameters _ (by decide)
    | apply Controlled.constant; norm_num <;> omega

theorem Context.cellGood : ctx.Good (cell d) := by
  have minimum := ctx.minimum
  have headIndex : ctx.Good (mask (sub position (constant 4))) := by
    simp only [mask,sub,constant,position,outputLength,input]
    two_sat_control_arithmetic ctx.parameters
  have atomIndex : ctx.Good (mask (sub position (add (constant 4) rules))) := by
    simp only [mask,sub,add,constant,position,outputLength,rules,input]
    two_sat_control_arithmetic ctx.parameters
  have ruleIndex : ctx.Good (mask (sub position (add (add (constant 4) rules) occurrences))) := by
    simp only [mask,sub,add,constant,position,outputLength,rules,occurrences,input]
    two_sat_control_arithmetic ctx.parameters
  have heads := ctx.headCellGood _ headIndex
  have atomValues := ctx.atomCellGood _ atomIndex
  have ruleValues := ctx.ruleCellGood _ ruleIndex
  simp only [cell]
  repeat' first
    | assumption
    | apply Context.selectGood ctx
    | apply Controlled.arithmetic
    | apply Controlled.inputValue; exact ctx.parameters _ (by decide)
    | apply Controlled.constant; norm_num <;> omega

/-- All arithmetic, signed local differences, and memory loads in one generated
cell fit a single polynomial budget. Original raw coordinate words are checked
through `InputFits`, independently of their magnitudes. -/
theorem Context.cellBounded : Bounded (cell d) (base^(2*(cell d).nodes)) env memory (Raw.words raw.val) :=
  ctx.cellGood.budget (by have := ctx.minimum; omega)

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
