/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceRequestEmitter

/-!
# Polynomial-time packaging of periodic-CNF PSPACE hardness

This file isolates the only remaining machine-level obligation in the 1D
periodic-CNF hardness proof: generating the bounded compact transition request
from evaluator-native source fields.  Given that certificate, the verified
finite source encoder, request evaluator, sequential-composition machine, and
semantic reduction assemble the complete polynomial-time many-one reduction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace PolySpaceHardness

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Exact outstanding frontend contract: on native natural fields, generate
the bounded compact request consumed by the structural formula evaluator. -/
abbrev NativeRequestGenerator :=
  TM2ComputableInPolyTime PartrecToTM2.trList
    TransitionEvaluatorMachine.TransitionCompilerRequest.encode
    (PolySpaceNativeCompiler.nativeCompilerRequest decider)

/-- Compose arbitrary finite-alphabet field encoding with the native request
generator. -/
def sourceRequestComputableInPolyTime
    (generator : NativeRequestGenerator decider) :
    TM2ComputableInPolyTime id
      TransitionEvaluatorMachine.TransitionCompilerRequest.encode
      (fun symbols : List encoding.Γ =>
        PolySpaceNativeCompiler.nativeCompilerRequest decider
          (FiniteEncodingNativeFields.fields symbols)) :=
  TM2CompositionMachine.computableInPolyTime
    (FiniteEncodingNativeFields.fieldsComputableInPolyTime
      (Symbol := encoding.Γ)) generator

/-- Compose source preprocessing with the verified quadratic structural
compiler.  The physical output is the direct native formula-field stream. -/
def sourceFieldsComputableInPolyTime
    (generator : NativeRequestGenerator decider) :
    TM2ComputableInPolyTime id PartrecToTM2.trList
      (fun symbols : List encoding.Γ =>
        PolySpaceNativeCompiler.nativeCompilerFields decider
          (FiniteEncodingNativeFields.fields symbols)) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (sourceRequestComputableInPolyTime decider generator)
    TransitionEvaluatorMachine.computableInPolyTime
  simpa only [PolySpaceNativeCompiler.nativeCompilerRequest_compile] using
    composed

/-- Present the same composed machine at the semantic formula codomain. -/
def sourceFormulaComputableInPolyTime
    (generator : NativeRequestGenerator decider) :
    TM2ComputableInPolyTime id PeriodicCNFFlatEncoding.finEncoding.encode
      (PolySpaceCompiler.formulaOfSymbols decider) := by
  let fields := sourceFieldsComputableInPolyTime decider generator
  refine
    { tm := fields.tm
      inputAlphabet := fields.inputAlphabet
      outputAlphabet := fields.outputAlphabet
      time := fields.time
      outputsFun := ?_ }
  intro symbols
  have run := fields.outputsFun symbols
  convert run using 1
  all_goals
    simp only [PolySpaceNativeCompiler.nativeCompilerFields_sourceFields,
      PolySpaceNativeCompiler.trList_formulaFields_eq_finEncoding_encode]
    rfl

/-- Specialize the raw-symbol compiler to values of the source encoding. -/
def reductionComputableInPolyTime
    (generator : NativeRequestGenerator decider) :
    TM2ComputableInPolyTime encoding.encode
      PeriodicCNFFlatEncoding.finEncoding.encode
      (PolySpaceReduction.formula decider) := by
  let compiler := sourceFormulaComputableInPolyTime decider generator
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  intro input
  simpa only [id_eq, PolySpaceCompiler.formulaOfSymbols_encode] using
    compiler.outputsFun (encoding.encode input)

/-- One certified native request generator closes the polynomial-time
many-one reduction for its source PSPACE decider. -/
theorem polyTimeManyOneReducible
    (generator : NativeRequestGenerator decider) :
    Complexity.PolyTimeManyOneReducible encoding
      PeriodicCNFFlatEncoding.finEncoding language LocalPeriodicCNF1DSAT := by
  refine ⟨PolySpaceReduction.formula decider, ?_, ?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (reductionComputableInPolyTime decider generator)⟩
  · intro input
    exact PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

/-- A uniform provider of the outstanding native request generators. -/
def NativeRequestGenerators : Prop :=
  ∀ {Input : Type} (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language),
    Nonempty (NativeRequestGenerator decider)

/-- Once the native request-generator certificate is constructed uniformly,
local 1D periodic CNF satisfiability is PSPACE-hard. -/
theorem localPeriodicCNF1DSAT_PSPACEHard_of_nativeRequestGenerators
    (generators : NativeRequestGenerators) :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding
      LocalPeriodicCNF1DSAT := by
  intro Input sourceEncoding source sourceInPSPACE
  obtain ⟨sourceDecider⟩ := sourceInPSPACE
  obtain ⟨generator⟩ :=
    generators sourceEncoding source sourceDecider
  exact polyTimeManyOneReducible sourceDecider generator

/-- Compose the concrete source-uniform request generator with the verified
quadratic transition evaluator. -/
def directSourceFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id PartrecToTM2.trList
      (fun symbols : List encoding.Γ =>
        (PolySpaceNativeCompiler.sourceCompilerRequest decider symbols).compile) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (PolySpaceRequestEmitter.sourceRequestComputableInPolyTime decider)
    TransitionEvaluatorMachine.computableInPolyTime
  exact composed

/-- Present the concrete composed machine at the semantic periodic-CNF
codomain. -/
def directSourceFormulaComputableInPolyTime :
    TM2ComputableInPolyTime id PeriodicCNFFlatEncoding.finEncoding.encode
      (PolySpaceCompiler.formulaOfSymbols decider) := by
  let fields := directSourceFieldsComputableInPolyTime decider
  refine
    { tm := fields.tm
      inputAlphabet := fields.inputAlphabet
      outputAlphabet := fields.outputAlphabet
      time := fields.time
      outputsFun := ?_ }
  intro symbols
  have run := fields.outputsFun symbols
  convert run using 1
  all_goals
    simp only [PolySpaceNativeCompiler.sourceCompilerRequest_compile,
      PolySpaceNativeCompiler.trList_formulaFields_eq_finEncoding_encode]
    rfl

/-- Specialize the concrete raw-symbol compiler to encoded source values. -/
def directReductionComputableInPolyTime :
    TM2ComputableInPolyTime encoding.encode
      PeriodicCNFFlatEncoding.finEncoding.encode
      (PolySpaceReduction.formula decider) := by
  let compiler := directSourceFormulaComputableInPolyTime decider
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  intro input
  simpa only [id_eq, PolySpaceCompiler.formulaOfSymbols_encode] using
    compiler.outputsFun (encoding.encode input)

/-- The concrete request printer closes the polynomial-time many-one
reduction for every polynomial-space source decider. -/
theorem directPolyTimeManyOneReducible :
    Complexity.DeciderInPolySpace encoding language →
    Complexity.PolyTimeManyOneReducible encoding
      PeriodicCNFFlatEncoding.finEncoding language LocalPeriodicCNF1DSAT := by
  intro decider
  refine ⟨PolySpaceReduction.formula decider, ?_, ?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (directReductionComputableInPolyTime decider)⟩
  · intro input
    exact PolySpaceReduction.mem_iff_localPeriodicCNF1DSAT decider input

/-- Local one-dimensional periodic CNF satisfiability is PSPACE-hard. -/
theorem localPeriodicCNF1DSAT_PSPACEHard :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding
      LocalPeriodicCNF1DSAT := by
  intro Input sourceEncoding source sourceInPSPACE
  obtain ⟨sourceDecider⟩ := sourceInPSPACE
  exact directPolyTimeManyOneReducible sourceDecider

end PolySpaceHardness
end PeriodicCNF
end LeanTrominoes
