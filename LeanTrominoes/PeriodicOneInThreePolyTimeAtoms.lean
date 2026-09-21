/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeAtomColumnSemantics
import LeanTrominoes.PeriodicOneInThreeAtomGadgetSemantics

/-! # The compiled atom stream is the native numeric exact-one formula -/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.AtomDescriptors
open PeriodicCNF.UnaryProgramClauseProfile

private theorem original_count (ps : List ClauseProfile) :
    ((ps.flatMap block).map originalStep).sum = (ps.flatMap ClauseProfile.literals).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.map_append,List.sum_append,ih]

private theorem gadgetAtoms_formula (source : PeriodicCNF Nat) :
    gadgetAtoms source 0 source.clauses = (Numeric.formula source).variableOccurrences := by
  rw [gadgetAtoms_zipIdx]
  simp [Numeric.formula,PeriodicCNF.variableOccurrences,PeriodicCNF.rename,
    PeriodicCNF.renameClause,PeriodicLiteral.rename,PeriodicOneInThree.formula,
    clauseAtoms,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def]

theorem output_formula (source : PeriodicCNF Nat) (ps : List ClauseProfile)
    (profiles : ps.map ClauseProfile.literals = source.clauses.map (List.map LiteralProfile.ofLiteral)) :
    output (ps.flatMap block) source.variableOccurrences = (Numeric.formula source).variableOccurrences := by
  have lengths := congrArg (fun lists : List (List LiteralProfile) => lists.flatten.length) profiles
  have count : (ps.flatMap ClauseProfile.literals).length = source.variableOccurrences.length := by
    simpa only [List.length_flatten,List.map_map,List.length_map,List.length_flatMap,
      PeriodicCNF.variableOccurrences,Function.comp_def] using lengths
  rw [output_eq_evaluate _ _ (by rw [original_count,count])]
  change evaluate (source.clauses.flatMap (List.map PeriodicLiteral.atom)) 0 0 (ps.flatMap block) = _
  rw [evaluate_blocks source source.clauses ps 0 (by intro j c h; simpa using h) profiles.symm]
  exact gadgetAtoms_formula source

end LeanTrominoes.PeriodicOneInThree.AtomDescriptors

namespace LeanTrominoes.PeriodicOneInThree.PolyTime
open Turing PeriodicCNF
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
variable [Inhabited encoding.Γ]
noncomputable local instance exactOneAtomsStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def descriptors (symbols : List encoding.Γ) :=
  (PeriodicThreeSATThree.PolyTime.profiles decider symbols).flatMap AtomDescriptors.block

noncomputable def descriptorsComputableInPolyTime : TM2ComputableInPolyTime id id (descriptors decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (PeriodicThreeSATThree.PolyTime.profilesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime AtomDescriptors.block)
  exact physical

noncomputable def atomsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (atoms decider) := by
  let physical := AtomDescriptors.outputComputableInPolyTime id (descriptors decider)
    (PeriodicThreeSATThree.PolyTime.atoms decider) (descriptorsComputableInPolyTime decider)
    (PeriodicThreeSATThree.PolyTime.atomsComputableInPolyTime decider)
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical ?_
  intro symbols
  apply congrArg UnaryFieldEncoderMachine.unaryFields
  exact AtomDescriptors.output_formula (source decider symbols)
    (PeriodicThreeSATThree.PolyTime.profiles decider symbols)
    (PeriodicThreeSATThree.PolyTime.profiles_correct decider symbols)

end LeanTrominoes.PeriodicOneInThree.PolyTime
