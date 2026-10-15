/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreePolyTimeCompiler
import LeanTrominoes.SAT.CNF.FiniteAbsoluteTokenCompiler

/-! # Occurrence splitting from arbitrary compiled sources and clause profiles

The source and profile machines are explicit parameters. This factors the
existing strip compiler into a reusable machine construction for finite SAT.
-/
noncomputable section
namespace LeanTrominoes.ThreeOccurrenceProfileCompiler
open _root_.Computability Turing PeriodicCNF PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNF.SplitLiteralPrinter
variable {Input Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol}
  {source : Input → SourceSplitRouteDescriptorTokens.Source}
  {sourceProfiles : Input → List ClauseProfile}

def formula (input : Input) := PeriodicThreeSATThree.Numeric.formula (source input).formula

def profiles (input : Input) : List ClauseProfile :=
  sourceProfiles input ++ (sourceProfiles input).flatMap fun p =>
    List.replicate p.literals.length PeriodicThreeSATThree.Numeric.cycleProfile

private theorem cycleProfiles_eq (ps : List ClauseProfile) :
    (ps.flatMap fun p => List.replicate p.literals.length PeriodicThreeSATThree.Numeric.cycleProfile) =
      List.replicate (ps.flatMap ClauseProfile.literals).length PeriodicThreeSATThree.Numeric.cycleProfile := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons,List.length_append,List.replicate_add,ih]

theorem profiles_correct
    (correct : ∀ input, (sourceProfiles input).map ClauseProfile.literals=
      (source input).formula.clauses.map (List.map LiteralProfile.ofLiteral)) (input : Input) :
    (profiles (sourceProfiles := sourceProfiles) input).map ClauseProfile.literals =
      (formula (source := source) input).clauses.map (List.map LiteralProfile.ofLiteral) := by
  have count := congrArg (fun lists : List (List LiteralProfile) => lists.flatten.length) (correct input)
  simp only [List.length_flatten,List.map_map] at count
  unfold profiles formula
  rw [PeriodicThreeSATThree.Numeric.profiles,List.map_append,correct input,cycleProfiles_eq,List.map_replicate]
  congr 2
  simp only [List.length_flatMap]
  simpa only [Function.comp_def,List.length_map,presentationLiteralCount,List.length_flatten] using count

theorem clauses_nonempty
    (correct : ∀ input, (sourceProfiles input).map ClauseProfile.literals=
      (source input).formula.clauses.map (List.map LiteralProfile.ofLiteral)) (input : Input) :
    ∀ c∈(formula (source := source) input).clauses,c≠[] := by
  intro c hc eq
  subst c
  have h : []∈(formula (source := source) input).clauses.map (List.map LiteralProfile.ofLiteral) :=
    List.mem_map.mpr ⟨[],hc,rfl⟩
  rw [← profiles_correct correct input] at h
  obtain ⟨p,_,eq⟩ := List.mem_map.mp h
  cases p <;> simp [ClauseProfile.literals] at eq

def computableInPolyTime
    (sourceCompiler : TM2ComputableInPolyTime encodeInput SourceSplitRouteDescriptorTokens.finEncoding.encode source)
    (profileCompiler : TM2ComputableInPolyTime encodeInput id sourceProfiles)
    (correct : ∀ input, (sourceProfiles input).map ClauseProfile.literals=
      (source input).formula.clauses.map (List.map LiteralProfile.ofLiteral)) :
    TM2ComputableInPolyTime encodeInput PeriodicCNFFlatEncoding.finEncoding.encode
      (formula (source := source)) := by
  let cycles := TM2CompositionMachine.computableInPolyTime profileCompiler
    (FiniteBlockTransducer.computableInPolyTime fun p : ClauseProfile =>
      List.replicate p.literals.length PeriodicThreeSATThree.Numeric.cycleProfile)
  let allProfiles := TM2ListAppend.computableInPolyTime profileCompiler cycles
  let metadataCompiler := TM2CompositionMachine.computableInPolyTime allProfiles
    (FiniteBlockTransducer.computableInPolyTime fun p : ClauseProfile => clauseMetadata p.literals)
  let routes := TM2CompositionMachine.computableInPolyTime sourceCompiler SourceSplitRouteDescriptorTokens.compiler
  let projected := TM2CompositionMachine.computableInPolyTime routes RouteTargetCompiler.computableInPolyTime
  have atomCompiler : TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => (formula (source := source) input).variableOccurrences) := by
    apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq projected
    intro input
    change RouteTargetCompiler.output (PeriodicOrthocrossing.routeDescriptorTokens
      (PeriodicThreeSATThree.splitRouteDescriptors (source input).formula)) = _
    rw [RouteTargetCompiler.output_descriptors,PeriodicThreeSATThree.Numeric.target_atoms]
    rfl
  have metadataCorrect (input : Input) :
      (profiles (sourceProfiles := sourceProfiles) input).flatMap (fun p => clauseMetadata p.literals)=
        (records (formula (source := source) input)).map Prod.fst := by
    rw [records_metadata]
    have h := congrArg (List.flatMap clauseMetadata) (profiles_correct correct input)
    simpa only [List.flatMap_map] using h
  have aligned (input : Input) :
      ((profiles (sourceProfiles := sourceProfiles) input).flatMap (fun p => clauseMetadata p.literals)).length=
        (formula (source := source) input).variableOccurrences.length := by
    rw [metadataCorrect,← records_atoms]
    simp only [List.length_map]
  let body := assembleComputableInPolyTime encodeInput
    (fun input => (profiles (sourceProfiles := sourceProfiles) input).flatMap (fun p => clauseMetadata p.literals))
    (fun input => (formula (source := source) input).variableOccurrences) aligned metadataCompiler atomCompiler
  have exactBody : TM2ComputableInPolyTime encodeInput id (fun input =>
      (records (formula (source := source) input)).flatMap (fun p => literalBlock p.1 p.2)) := by
    apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq body
    intro input
    rw [metadataCorrect,← records_atoms]
    have projections (ps : List (Metadata × Nat)) :
        (ps.map Prod.fst).zip (ps.map Prod.snd)=ps := by
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [ih]
    rw [projections]
  let finalized := TM2CompositionMachine.computableInPolyTime exactBody
    UnaryProgramTokenFinalizer.countAndFinalizeComputableInPolyTime
  have fieldCompiler : TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => PeriodicCNFFlatEncoding.formulaFields (formula (source := source) input)) := by
    apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq finalized
    intro input
    exact finalize_records _ (clauses_nonempty correct input)
      (PeriodicThreeSATThree.Numeric.width_three _ (source input).widthAtMostThree)
      (PeriodicThreeSATThree.Numeric.forward _ (source input).isForwardLocal)
  let encoded := TM2CompositionMachine.computableInPolyTime fieldCompiler UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq encoded
  intro input
  exact PolySpaceNativeCompiler.trList_formulaFields_eq_finEncoding_encode _

end LeanTrominoes.ThreeOccurrenceProfileCompiler
