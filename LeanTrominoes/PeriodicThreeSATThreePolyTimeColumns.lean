/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeSATThreeNumericProfiles
import LeanTrominoes.PeriodicCNFRouteTargetCompiler
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteTokenSourceCompiler
import LeanTrominoes.PeriodicCNFStripDirectClauseProfileScan
import LeanTrominoes.TM2ListAppendCompiler

/-! # Polynomial-time atom and profile columns for the 1D 3SAT-3 reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeSATThree.PolyTime
open Computability Turing PeriodicCNF PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNF.SplitLiteralPrinter

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
variable [Inhabited encoding.Γ]

noncomputable local instance (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def source (symbols : List encoding.Γ) := PolySpaceCompiler.formulaOfSymbols decider symbols

def formula (symbols : List encoding.Γ) := Numeric.formula (source decider symbols)

def cycleProfiles (ps : List ClauseProfile) : List ClauseProfile :=
  ps.flatMap fun p => List.replicate p.literals.length Numeric.cycleProfile

def profiles (symbols : List encoding.Γ) : List ClauseProfile :=
  let ps := StripDirectClauseProfileScan.sourceClauseProfiles decider symbols
  ps ++ cycleProfiles ps

private theorem cycleProfiles_eq (ps : List ClauseProfile) :
    cycleProfiles ps = List.replicate (ps.flatMap ClauseProfile.literals).length Numeric.cycleProfile := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [cycleProfiles,List.flatMap_cons,List.length_append,List.replicate_add] at *
    rw [ih]

theorem profiles_correct (symbols : List encoding.Γ) :
    (profiles decider symbols).map ClauseProfile.literals =
      (formula decider symbols).clauses.map (List.map LiteralProfile.ofLiteral) := by
  have base := StripDirectClauseProfileScan.sourceClauseProfiles_literals_eq_formula decider symbols
  have count := congrArg (fun lists : List (List LiteralProfile) => lists.flatten.length) base
  simp only [List.length_flatten,List.map_map,List.length_map] at count
  unfold profiles formula
  rw [Numeric.profiles,List.map_append,base,cycleProfiles_eq,List.map_replicate]
  congr 2
  simp only [List.length_flatMap]
  simpa only [Function.comp_def,List.length_map,presentationLiteralCount,source,List.length_flatten] using count

noncomputable def profilesComputableInPolyTime : TM2ComputableInPolyTime id id (profiles decider) := by
  let first := StripDirectClauseProfileScan.sourceClauseProfilesComputableInPolyTime decider
  let second := TM2CompositionMachine.computableInPolyTime first
    (FiniteBlockTransducer.computableInPolyTime fun p : ClauseProfile =>
      List.replicate p.literals.length Numeric.cycleProfile)
  let pair := TM2ForkMachine.computableInPolyTime first second
  let result := TM2CompositionMachine.computableInPolyTime pair TM2ListAppend.mergeComputableInPolyTime
  exact result

def metadata (symbols : List encoding.Γ) : List Metadata :=
  (profiles decider symbols).flatMap (fun p => clauseMetadata p.literals)

theorem metadata_correct (symbols : List encoding.Γ) :
    metadata decider symbols = (records (formula decider symbols)).map Prod.fst := by
  rw [records_metadata]
  have h := congrArg (List.flatMap clauseMetadata) (profiles_correct decider symbols)
  simpa only [List.flatMap_map,metadata] using h

noncomputable def metadataComputableInPolyTime : TM2ComputableInPolyTime id id (metadata decider) := by
  let result := TM2CompositionMachine.computableInPolyTime (profilesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime fun p : ClauseProfile => clauseMetadata p.literals)
  exact result

def atoms (symbols : List encoding.Γ) := (formula decider symbols).variableOccurrences

noncomputable def atomsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (atoms decider) := by
  let promised := PeriodicCNFStripReduction.directSourceRouteTokenSourceComputableInPolyTime decider
  let routes := TM2CompositionMachine.computableInPolyTime promised SourceSplitRouteDescriptorTokens.compiler
  let projected := TM2CompositionMachine.computableInPolyTime routes RouteTargetCompiler.computableInPolyTime
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq projected ?_
  intro symbols
  change RouteTargetCompiler.output (PeriodicOrthocrossing.routeDescriptorTokens
    (splitRouteDescriptors (source decider symbols))) = _
  rw [RouteTargetCompiler.output_descriptors]
  rw [Numeric.target_atoms]
  rfl

theorem aligned (symbols : List encoding.Γ) :
    (metadata decider symbols).length=(atoms decider symbols).length := by
  rw [metadata_correct,atoms,← records_atoms]
  simp only [List.length_map]

end LeanTrominoes.PeriodicThreeSATThree.PolyTime
end
