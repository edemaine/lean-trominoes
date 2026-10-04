/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteSATNPHard
import LeanTrominoes.FiniteThreeSATThree
import LeanTrominoes.ThreeOccurrenceProfileCompiler

/-! # Actual polynomial-time finite occurrence-three Cook–Levin compilation -/
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanTrominoes.FiniteNPThreeOccurrenceCompiler
open _root_.Computability Turing PeriodicCNF UnaryProgramTokens
open Complexity.VerifierInPolyTime
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)

def sourceFormula (input : Input) : PeriodicCNF Nat :=
  FiniteCNF.periodize (separatedRequest verifier input).compile

def source (input : Input) : SourceSplitRouteDescriptorTokens.Source where
  formula := sourceFormula verifier input
  oneDimensional := by
    intro clause hc literal hl
    exact congrArg Prod.snd (FiniteCNF.periodize_zeroOffsets _ clause hc literal hl)
  isLocal := FiniteCNF.zeroOffsets_isLocal _ (FiniteCNF.periodize_zeroOffsets _)
  isForwardLocal := by
    intro clause hc literal hl
    exact Or.inl (FiniteCNF.periodize_zeroOffsets _ clause hc literal hl)
  widthAtMostThree := (FiniteCNF.width_periodize _ _).mpr (separatedRequest_width verifier input)

def formula (input : Input) : FiniteCNF.Formula Nat :=
  FiniteCNF.erase (PeriodicThreeSATThree.Numeric.formula (sourceFormula verifier input))

@[simp] theorem source_formula (input : Input) : (source verifier input).formula=sourceFormula verifier input := rfl

theorem target_zero (input : Input) :
    FiniteCNF.ZeroOffsets (PeriodicThreeSATThree.Numeric.formula (sourceFormula verifier input)) :=
  FiniteCNF.zeroOffsets_rename _
    (FiniteThreeSATThree.formula_zero _ (FiniteCNF.periodize_zeroOffsets _)) _

theorem periodize_formula (input : Input) : FiniteCNF.periodize (formula verifier input)=
    PeriodicThreeSATThree.Numeric.formula (sourceFormula verifier input) :=
  FiniteCNF.periodize_erase _ (target_zero verifier input)

theorem correct (input : Input) : FiniteCNF.Satisfiable (formula verifier input) ↔ language input := by
  rw [formula,FiniteCNF.satisfiable_erase _ (target_zero verifier input),
    PeriodicThreeSATThree.Numeric.satisfiable_iff,sourceFormula,FiniteCNF.satisfiable_periodize,
    separatedRequest_correct]

theorem width (input : Input) : FiniteCNF.WidthAtMost 3 (formula verifier input) :=
  (FiniteCNF.width_erase _ _).mpr
    (PeriodicThreeSATThree.Numeric.width_three _ (source verifier input).widthAtMostThree)

theorem occurrences (input : Input) : (FiniteCNF.periodize (formula verifier input)).OccurrencesAtMost 3 := by
  rw [periodize_formula]
  exact PeriodicThreeSATThree.Numeric.occurrences_three _

private def sourceComputableInPolyTime :
    TM2ComputableInPolyTime encoding.encode SourceSplitRouteDescriptorTokens.finEncoding.encode (source verifier) := by
  let physical := verifier.finiteCNFComputableInPolyTime
  have encoded (input : Input) : FiniteCNFCompiler.finEncoding.encode (separatedRequest verifier input).compile=
      SourceSplitRouteDescriptorTokens.finEncoding.encode (source verifier input) := by
    rw [SourceSplitRouteDescriptorTokens.finEncoding_encode]
    change PeriodicCNFFlatEncoding.encodeNatFields _=PeriodicCNFFlatEncoding.encodeNatFields _
    rfl
  exact {
    tm := physical.tm
    inputAlphabet := physical.inputAlphabet
    outputAlphabet := physical.outputAlphabet
    time := physical.time
    outputsFun input := by
      rw [← encoded input]
      exact physical.outputsFun input
  }

def sourceTokens (word : List encoding.Γ) : List Token :=
  requestSource ((requestFreshPolynomial verifier).eval word.length)
    (sourceSeparatedExpression verifier word).program

private def tokensComputableInPolyTime : TM2ComputableInPolyTime id id (sourceTokens verifier) := by
  let fresh := FiniteNPTokenAssembly.freshCompiler
    (FiniteNPTokenAssembly.polynomialScalar (Source := encoding.Γ) (requestFreshPolynomial verifier))
  let root : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => [Token.clauseMarker]) := TM2ConstantValueCompiler.computableInPolyTime id id [Token.clauseMarker]
  let header := TM2ListAppend.nativeComputableInPolyTime fresh root
  exact TM2ComputableInPolyTime.of_eq
    (TM2ListAppend.nativeComputableInPolyTime header (FiniteNPRequestEmitter.programComputableInPolyTime verifier))
    (fun word => by simp [sourceTokens,requestSource,List.append_assoc])

def sourceProfiles (input : Input) : List UnaryProgramClauseProfile.ClauseProfile :=
  UnaryProgramClauseProfile.requestScan (sourceTokens verifier (encoding.encode input))

private theorem sourceProfiles_correct (input : Input) :
    (sourceProfiles verifier input).map UnaryProgramClauseProfile.ClauseProfile.literals=
      (source verifier input).formula.clauses.map (List.map UnaryProgramClauseProfile.LiteralProfile.ofLiteral) := by
  unfold sourceProfiles sourceTokens
  rw [UnaryProgramClauseProfile.requestScan_literals_eq_clauseProfiles]
  change _=(FiniteCNF.periodize (FiniteCNFCompiler.erase
    (requireTransitionExpr (sourceSeparatedExpression verifier (encoding.encode input)).atCurrent
      ((requestFreshPolynomial verifier).eval (encoding.encode input).length)))).clauses.map _
  rw [FiniteCNFCompiler.periodize_erase _ (FiniteCNFCompiler.required_zeroOffsets _ _),
    sourceSeparatedExpression_atCurrent]

theorem clauses_nonempty (input : Input) : ∀ clause∈formula verifier input, clause≠[] := by
  intro clause member eq
  subst clause
  have emptyPeriodic : []∈(FiniteCNF.periodize (formula verifier input)).clauses :=
    List.mem_map.mpr ⟨[],member,rfl⟩
  rw [periodize_formula] at emptyPeriodic
  exact ThreeOccurrenceProfileCompiler.clauses_nonempty (sourceProfiles_correct verifier) input [] emptyPeriodic rfl

private def computableOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime encoding.encode FiniteCNFCompiler.finEncoding.encode (formula verifier) := by
  let profiles := TM2CompositionMachine.computableInPolyTime (tokensComputableInPolyTime verifier)
    UnaryProgramClauseProfile.requestScanComputableInPolyTime
  let lifted := TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode profiles
    (fun _ => rfl) (fun _ => rfl)
  let physical := ThreeOccurrenceProfileCompiler.computableInPolyTime
    (sourceComputableInPolyTime verifier) lifted (sourceProfiles_correct verifier)
  have encoded (input : Input) : PeriodicCNFFlatEncoding.finEncoding.encode
      (ThreeOccurrenceProfileCompiler.formula (source := source verifier) input)=
        FiniteCNFCompiler.finEncoding.encode (formula verifier input) := by
    simp only [ThreeOccurrenceProfileCompiler.formula,source_formula,
      PeriodicCNFFlatEncoding.finEncoding,PeriodicCNFFlatEncoding.finEncodingOfFields,
      FiniteCNFCompiler.finEncoding,FiniteCNFCompiler.fields]
    exact congrArg (fun cnf => PeriodicCNFFlatEncoding.encodeNatFields
      (PeriodicCNFFlatEncoding.formulaFields cnf)) (periodize_formula verifier input).symm
  exact {
    tm := physical.tm
    inputAlphabet := physical.inputAlphabet
    outputAlphabet := physical.outputAlphabet
    time := physical.time
    outputsFun input := by
      rw [← encoded input]
      exact physical.outputsFun input
  }

def computableInPolyTime :
    TM2ComputableInPolyTime encoding.encode FiniteCNFCompiler.finEncoding.encode (formula verifier) := by
  classical
  by_cases h : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice h⟩
    exact computableOfInhabited verifier
  · letI : IsEmpty encoding.Γ := not_nonempty_iff.mp h
    letI : Inhabited FiniteCNFCompiler.finEncoding.Γ := ⟨.bit0⟩
    by_cases inputNonempty : Nonempty Input
    · let fixedInput := Classical.choice inputNonempty
      let physical := TM2ConstantValueCompiler.computableInPolyTime encoding.encode
        FiniteCNFCompiler.finEncoding.encode (formula verifier fixedInput)
      apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
      intro input
      have wordEmpty (word : List encoding.Γ) : word=[] := by
        cases word with
        | nil => rfl
        | cons symbol _ => exact isEmptyElim symbol
      have eq : fixedInput=input := encoding.encode_injective
        ((wordEmpty _).trans (wordEmpty _).symm)
      rw [eq]
    · letI : IsEmpty Input := not_nonempty_iff.mp inputNonempty
      let physical := TM2ConstantListCompiler.computableInPolyTime encoding.encode
        ([] : List FiniteCNFCompiler.finEncoding.Γ)
      exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (fun input => isEmptyElim input)

end LeanTrominoes.FiniteNPThreeOccurrenceCompiler
