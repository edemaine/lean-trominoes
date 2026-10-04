/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicCNFRequireTransitionExprZeroAnchors
import LeanTrominoes.PeriodicCNFTransitionExprNonempty

/-! # A source interface shared by finite and periodic tableau printers

The geometry compiler consumes a bounded transition expression, its fresh
variable boundary, and an actual machine emitting its counted unary program.
Its implementation need not depend on how that expression was generated.
-/
noncomputable section
namespace LeanTrominoes.PeriodicCNF
open _root_.Computability Turing

structure ProgramSource {Input : Type} (encoding : _root_.Computability.FinEncoding Input)
    (language : Input → Prop) where
  request : List encoding.Γ → TransitionEvaluatorMachine.TransitionCompilerRequest
  formulaOfSymbols : List encoding.Γ → PeriodicCNF Nat
  formula_eq : ∀ symbols,formulaOfSymbols symbols=requireTransitionExpr
    (request symbols).expression (request symbols).fresh
  sourceTokens : List encoding.Γ → List UnaryProgramTokens.Token
  sourceTokens_eq_requestSource : ∀ symbols,sourceTokens symbols=UnaryProgramTokens.requestSource
    (request symbols).fresh (request symbols).expression.program
  sourceTokensComputableInPolyTime : TM2ComputableInPolyTime id id sourceTokens
  directSourceFormulaComputableInPolyTime : TM2ComputableInPolyTime id
    PeriodicCNFFlatEncoding.finEncoding.encode formulaOfSymbols
  correct : ∀ input,language input ↔ LocalPeriodicCNF1DSAT (formulaOfSymbols (encoding.encode input))

namespace ProgramSource
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}

def program (source : ProgramSource encoding language) (symbols : List encoding.Γ) :=
  (source.request symbols).expression.program

def fresh (source : ProgramSource encoding language) (symbols : List encoding.Γ) :=
  (source.request symbols).fresh

def sourceCompilerRequest (source : ProgramSource encoding language) := source.request

@[simp] theorem sourceCompilerRequest_program (source : ProgramSource encoding language) (symbols : List encoding.Γ) :
    (source.sourceCompilerRequest symbols).expression.program=source.program symbols := rfl
@[simp] theorem sourceCompilerRequest_fresh (source : ProgramSource encoding language) (symbols : List encoding.Γ) :
    (source.sourceCompilerRequest symbols).fresh=source.fresh symbols := rfl

def formula (source : ProgramSource encoding language) (input : Input) : PeriodicCNF Nat :=
  source.formulaOfSymbols (encoding.encode input)

@[simp] theorem formulaOfSymbols_encode (source : ProgramSource encoding language) (input : Input) :
    source.formulaOfSymbols (encoding.encode input)=source.formula input := rfl

theorem mem_iff_localPeriodicCNF1DSAT (source : ProgramSource encoding language) (input : Input) :
    language input ↔ LocalPeriodicCNF1DSAT (source.formula input) := source.correct input

/-- The established PSPACE printer supplies this interface without changing
its formula or its physical output word. -/
def ofDecider (decider : Complexity.DeciderInPolySpace encoding language) : ProgramSource encoding language := by
  letI (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
  refine ⟨PolySpaceNativeCompiler.sourceCompilerRequest decider,
    PolySpaceCompiler.formulaOfSymbols decider,?_,PolySpaceRequestEmitter.sourceTokens decider,?_,
    PolySpaceRequestEmitter.sourceTokensComputableInPolyTime decider,
    PolySpaceHardness.directSourceFormulaComputableInPolyTime decider,?_⟩
  · intro symbols
    rw [PolySpaceNativeCompiler.sourceCompilerRequest_expression,
      PolySpaceNativeCompiler.sourceCompilerRequest_fresh]
    rfl
  · intro symbols
    rw [PolySpaceRequestEmitter.sourceTokens_eq_requestSource,
      PolySpaceProgramSpec.sourceCompilerRequest_program,
      PolySpaceProgramSpec.sourceCompilerRequest_fresh]
  · intro input
    rw [PolySpaceCompiler.formulaOfSymbols_encode]
    exact PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

instance : Coe (Complexity.DeciderInPolySpace encoding language) (ProgramSource encoding language) :=
  ⟨ofDecider⟩
end ProgramSource
end LeanTrominoes.PeriodicCNF
