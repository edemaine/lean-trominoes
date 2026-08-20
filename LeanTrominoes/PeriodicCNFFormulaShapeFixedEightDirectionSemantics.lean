/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionCycleSemantics

/-! # Stream semantics of fixed-eight direction descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

/-- One marker for every incoming distinct-variable descriptor. -/
def sourceVariableMarkers
    (source : List FormulaShapeDirectionOrdering.Token) : List Unit :=
  source.filterMap fun
    | .clause _ => none
    | .variable => some ()

private def orderedProfile? : FormulaShapeDirectionOrdering.Token →
    Option UnaryProgramClauseProfile.ClauseProfile
  | .clause profile => some profile.orderedProfile
  | .variable => none

private def orderedProfiles
    (source : List FormulaShapeDirectionOrdering.Token) :
    List UnaryProgramClauseProfile.ClauseProfile :=
  source.filterMap orderedProfile?

@[simp] private theorem orderedProfiles_append
    (first second : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (first ++ second) =
      orderedProfiles first ++ orderedProfiles second := by
  simp [orderedProfiles]

@[simp] private theorem orderedProfiles_clause
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (.clause profile :: source) =
      profile.orderedProfile :: orderedProfiles source :=
  rfl

@[simp] private theorem orderedProfiles_variable
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (.variable :: source) = orderedProfiles source :=
  rfl

@[simp] private theorem sourceVariableMarkers_append
    (first second : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (first ++ second) =
      sourceVariableMarkers first ++ sourceVariableMarkers second := by
  simp [sourceVariableMarkers]

@[simp] private theorem sourceVariableMarkers_clause
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (source : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (.clause profile :: source) =
      sourceVariableMarkers source :=
  rfl

@[simp] private theorem sourceVariableMarkers_variable
    (source : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (.variable :: source) =
      () :: sourceVariableMarkers source :=
  rfl

@[simp] private theorem sourceVariableMarkers_replicate_variable
    (count : Nat) :
    sourceVariableMarkers
        (List.replicate count FormulaShapeDirectionOrdering.Token.variable) =
      List.replicate count () := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, sourceVariableMarkers_variable,
        induction, List.replicate_succ]

private theorem orderedProfiles_copiedClauseBlocks
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (source.flatMap copiedClauseBlock) =
      orderedProfiles source := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [List.flatMap_cons, copiedClauseBlock,
            orderedProfiles_append, orderedProfiles_clause, induction]
          simp [orderedProfiles, orderedProfile?]
      | «variable» =>
          rw [List.flatMap_cons, copiedClauseBlock, List.nil_append,
            orderedProfiles_variable, induction]

private theorem orderedProfiles_cycleClauseBlocks
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (source.flatMap cycleClauseBlock) =
      (sourceVariableMarkers source).flatMap fun _ =>
        orderedProfiles cycleClauseDescriptors := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [List.flatMap_cons, cycleClauseBlock, List.nil_append,
            sourceVariableMarkers_clause, induction]
      | «variable» =>
          rw [List.flatMap_cons, cycleClauseBlock,
            orderedProfiles_append, sourceVariableMarkers_variable,
            List.flatMap_cons, induction]

private theorem orderedProfiles_copiedVariableBlocks
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (source.flatMap copiedVariableBlock) = [] := by
  have replicateVariables : ∀ count : Nat,
      orderedProfiles
        (List.replicate count
          FormulaShapeDirectionOrdering.Token.variable) = [] := by
    intro count
    induction count with
    | zero => rfl
    | succ count induction =>
        rw [List.replicate_succ, orderedProfiles_variable, induction]
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [List.flatMap_cons, copiedVariableBlock, List.nil_append,
            induction]
      | «variable» =>
          rw [List.flatMap_cons, copiedVariableBlock,
            orderedProfiles_append, replicateVariables, induction,
            List.nil_append]

private theorem sourceVariableMarkers_copiedClauseBlocks
    (source : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (source.flatMap copiedClauseBlock) = [] := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [List.flatMap_cons, copiedClauseBlock,
            sourceVariableMarkers_append,
            sourceVariableMarkers_clause, induction]
          simp [sourceVariableMarkers]
      | «variable» =>
          rw [List.flatMap_cons, copiedClauseBlock, List.nil_append,
            induction]

private theorem sourceVariableMarkers_cycleClauseDescriptors :
    sourceVariableMarkers cycleClauseDescriptors = [] := by
  simp [sourceVariableMarkers, cycleClauseDescriptors]

private theorem sourceVariableMarkers_cycleClauseBlocks
    (source : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (source.flatMap cycleClauseBlock) = [] := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [List.flatMap_cons, cycleClauseBlock, List.nil_append,
            induction]
      | «variable» =>
          rw [List.flatMap_cons, cycleClauseBlock,
            sourceVariableMarkers_append,
            sourceVariableMarkers_cycleClauseDescriptors,
            induction, List.nil_append]

private theorem sourceVariableMarkers_copiedVariableBlocks_length
    (source : List FormulaShapeDirectionOrdering.Token) :
    (sourceVariableMarkers
      (source.flatMap copiedVariableBlock)).length =
        FormulaShapeFixedEight.copiesPerVariable *
          (sourceVariableMarkers source).length := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          simpa only [List.flatMap_cons, copiedVariableBlock,
            List.nil_append, sourceVariableMarkers_clause] using induction
      | «variable» =>
          rw [List.flatMap_cons, copiedVariableBlock,
            sourceVariableMarkers_append,
            sourceVariableMarkers_replicate_variable,
            sourceVariableMarkers_variable, List.length_append,
            List.length_replicate, List.length_cons, induction]
          rw [Nat.mul_succ]
          omega

@[simp] theorem sourceVariableMarkers_length
    (source : List FormulaShapeDirectionOrdering.Token) :
    (sourceVariableMarkers source).length =
      FormulaShape.variableCount
        (FormulaShapeDirectionOrdering.shape source) := by
  rw [FormulaShapeDirectionOrdering.variableCount_shape]
  rfl

/-- The expansion keeps incoming ordered clause profiles first and appends
one exact local ring profile block per source variable. -/
theorem clauseProfiles_shape_descriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape (descriptors source)) =
      FormulaShape.clauseProfiles
          (FormulaShapeDirectionOrdering.shape source) ++
        (sourceVariableMarkers source).flatMap fun _ =>
          FormulaShape.clauseProfiles
            (FormulaShapeDirectionOrdering.shape cycleClauseDescriptors) := by
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape,
    FormulaShapeDirectionOrdering.clauseProfiles_shape]
  change orderedProfiles (descriptors source) =
    orderedProfiles source ++
      (sourceVariableMarkers source).flatMap fun _ =>
        orderedProfiles cycleClauseDescriptors
  unfold descriptors
  rw [orderedProfiles_append, orderedProfiles_append,
    orderedProfiles_copiedClauseBlocks,
    orderedProfiles_cycleClauseBlocks,
    orderedProfiles_copiedVariableBlocks]
  simp

/-- Every incoming variable marker becomes exactly nine output variable
markers; neither copied nor ring clauses contribute markers. -/
theorem variableCount_shape_descriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    FormulaShape.variableCount
        (FormulaShapeDirectionOrdering.shape (descriptors source)) =
      FormulaShapeFixedEight.copiesPerVariable *
        FormulaShape.variableCount
          (FormulaShapeDirectionOrdering.shape source) := by
  rw [FormulaShapeDirectionOrdering.variableCount_shape,
    FormulaShapeDirectionOrdering.variableCount_shape]
  change (sourceVariableMarkers (descriptors source)).length =
    FormulaShapeFixedEight.copiesPerVariable *
      (sourceVariableMarkers source).length
  unfold descriptors
  rw [sourceVariableMarkers_append, sourceVariableMarkers_append,
    sourceVariableMarkers_copiedClauseBlocks,
    sourceVariableMarkers_cycleClauseBlocks]
  simp only [List.nil_append]
  exact sourceVariableMarkers_copiedVariableBlocks_length source

/-- Every formula-derived direction descriptor stream has the canonical
clause-prefix/variable-suffix form expected by the one-pass expansion. -/
theorem ofFormula_isCanonical
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    IsCanonical (FormulaShapeDirectionOrdering.ofFormula source routes) := by
  refine ⟨source.clauses.zipIdx.map fun taggedClause =>
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        routes taggedClause.2 taggedClause.1,
    source.erase.variableOccurrences.dedup.length, ?_⟩
  simp [FormulaShapeDirectionOrdering.ofFormula, List.map_map,
    Function.comp_def]

private theorem orderedProfiles_streamBlock_clause
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    orderedProfiles (streamBlock (.clause profile)) =
      [profile.orderedProfile] := by
  simp [streamBlock, copiedClauseBlock, cycleClauseBlock,
    copiedVariableBlock, orderedProfiles, orderedProfile?]

private theorem orderedProfiles_streamBlock_variable :
    orderedProfiles (streamBlock .variable) =
      orderedProfiles cycleClauseDescriptors := by
  simp [streamBlock, copiedClauseBlock, cycleClauseBlock,
    copiedVariableBlock, orderedProfiles, orderedProfile?]

@[simp] private theorem streamDescriptors_append
    (first second : List FormulaShapeDirectionOrdering.Token) :
    streamDescriptors (first ++ second) =
      streamDescriptors first ++ streamDescriptors second := by
  simp [streamDescriptors]

@[simp] private theorem streamDescriptors_cons
    (token : FormulaShapeDirectionOrdering.Token)
    (source : List FormulaShapeDirectionOrdering.Token) :
    streamDescriptors (token :: source) =
      streamBlock token ++ streamDescriptors source :=
  rfl

private theorem orderedProfiles_map_clause
    (profiles : List
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    orderedProfiles
        (profiles.map FormulaShapeDirectionOrdering.Token.clause) =
      profiles.map
        FormulaShapeDirectionOrdering.DirectedClauseProfile.orderedProfile := by
  induction profiles with
  | nil => rfl
  | cons profile profiles induction =>
      rw [List.map_cons, orderedProfiles_clause, List.map_cons, induction]

private theorem orderedProfiles_replicate_variable
    (count : Nat) :
    orderedProfiles
        (List.replicate count
          FormulaShapeDirectionOrdering.Token.variable) = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, orderedProfiles_variable, induction]

private theorem sourceVariableMarkers_map_clause
    (profiles : List
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    sourceVariableMarkers
        (profiles.map FormulaShapeDirectionOrdering.Token.clause) = [] := by
  induction profiles with
  | nil => rfl
  | cons profile profiles induction =>
      rw [List.map_cons, sourceVariableMarkers_clause, induction]

private theorem orderedProfiles_streamDescriptors_map_clause
    (profiles : List
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    orderedProfiles
        (streamDescriptors
          (profiles.map FormulaShapeDirectionOrdering.Token.clause)) =
      profiles.map
        FormulaShapeDirectionOrdering.DirectedClauseProfile.orderedProfile := by
  induction profiles with
  | nil => rfl
  | cons profile profiles induction =>
      rw [List.map_cons, streamDescriptors_cons, orderedProfiles_append,
        orderedProfiles_streamBlock_clause, induction, List.map_cons,
        List.singleton_append]

private theorem orderedProfiles_streamDescriptors_replicate_variable
    (count : Nat) :
    orderedProfiles
        (streamDescriptors
          (List.replicate count
            FormulaShapeDirectionOrdering.Token.variable)) =
      (List.replicate count ()).flatMap fun _ =>
        orderedProfiles cycleClauseDescriptors := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, streamDescriptors_cons,
        orderedProfiles_append, orderedProfiles_streamBlock_variable,
        induction]
      have unitReplicate :
          List.replicate (count + 1) () =
            () :: List.replicate count () := by
        rw [List.replicate_succ]
      rw [unitReplicate, List.flatMap_cons]

private theorem orderedProfiles_streamDescriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    orderedProfiles (streamDescriptors source) =
      source.flatMap fun token => orderedProfiles (streamBlock token) := by
  unfold streamDescriptors
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, orderedProfiles_append,
        List.flatMap_cons, induction]

private theorem orderedProfiles_streamDescriptors_of_isCanonical
    (source : List FormulaShapeDirectionOrdering.Token)
    (canonical : IsCanonical source) :
    orderedProfiles (streamDescriptors source) =
      orderedProfiles source ++
        (sourceVariableMarkers source).flatMap fun _ =>
          orderedProfiles cycleClauseDescriptors := by
  rcases canonical with ⟨profiles, count, rfl⟩
  rw [streamDescriptors_append, orderedProfiles_append,
    orderedProfiles_streamDescriptors_map_clause,
    orderedProfiles_streamDescriptors_replicate_variable,
    orderedProfiles_append, orderedProfiles_map_clause,
    orderedProfiles_replicate_variable,
    sourceVariableMarkers_append,
    sourceVariableMarkers_map_clause,
    sourceVariableMarkers_replicate_variable]
  simp

private theorem sourceVariableMarkers_streamBlock_clause
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    sourceVariableMarkers (streamBlock (.clause profile)) = [] := by
  simp [streamBlock, copiedClauseBlock, cycleClauseBlock,
    copiedVariableBlock, sourceVariableMarkers]

private theorem sourceVariableMarkers_streamBlock_variable :
    sourceVariableMarkers (streamBlock .variable) =
      List.replicate FormulaShapeFixedEight.copiesPerVariable () := by
  change sourceVariableMarkers
      (cycleClauseDescriptors ++
        List.replicate FormulaShapeFixedEight.copiesPerVariable .variable) = _
  rw [sourceVariableMarkers_append,
    sourceVariableMarkers_cycleClauseDescriptors,
    sourceVariableMarkers_replicate_variable, List.nil_append]

private theorem sourceVariableMarkers_streamDescriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    sourceVariableMarkers (streamDescriptors source) =
      (sourceVariableMarkers source).flatMap fun _ =>
        List.replicate FormulaShapeFixedEight.copiesPerVariable () := by
  unfold streamDescriptors
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, sourceVariableMarkers_append]
      cases token with
      | clause profile =>
          rw [sourceVariableMarkers_streamBlock_clause,
            sourceVariableMarkers_clause, List.nil_append, induction]
      | «variable» =>
          rw [sourceVariableMarkers_streamBlock_variable,
            sourceVariableMarkers_variable, List.flatMap_cons, induction]

/-- On canonical inputs, the one-pass output has exactly the same ordered
clause profiles as the phase-major specification. -/
theorem clauseProfiles_shape_streamDescriptors_eq
    (source : List FormulaShapeDirectionOrdering.Token)
    (canonical : IsCanonical source) :
    FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape (streamDescriptors source)) =
      FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape (descriptors source)) := by
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape,
    FormulaShapeDirectionOrdering.clauseProfiles_shape]
  change orderedProfiles (streamDescriptors source) =
    orderedProfiles (descriptors source)
  have streamCorrect :=
    orderedProfiles_streamDescriptors_of_isCanonical source canonical
  have specification := clauseProfiles_shape_descriptors source
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape,
    FormulaShapeDirectionOrdering.clauseProfiles_shape] at specification
  change orderedProfiles (descriptors source) =
    orderedProfiles source ++
      (sourceVariableMarkers source).flatMap fun _ =>
        orderedProfiles cycleClauseDescriptors at specification
  exact streamCorrect.trans specification.symm

/-- On canonical inputs, the one-pass output also has the exact phase-major
distinct-variable count. -/
theorem variableCount_shape_streamDescriptors_eq
    (source : List FormulaShapeDirectionOrdering.Token)
    (_canonical : IsCanonical source) :
    FormulaShape.variableCount
        (FormulaShapeDirectionOrdering.shape (streamDescriptors source)) =
      FormulaShape.variableCount
        (FormulaShapeDirectionOrdering.shape (descriptors source)) := by
  rw [FormulaShapeDirectionOrdering.variableCount_shape,
    FormulaShapeDirectionOrdering.variableCount_shape]
  change (sourceVariableMarkers (streamDescriptors source)).length =
    (sourceVariableMarkers (descriptors source)).length
  rw [sourceVariableMarkers_streamDescriptors]
  have emittedLength :
      ((sourceVariableMarkers source).flatMap fun _ =>
        List.replicate FormulaShapeFixedEight.copiesPerVariable ()).length =
      FormulaShapeFixedEight.copiesPerVariable *
        (sourceVariableMarkers source).length := by
    induction sourceVariableMarkers source with
    | nil => rfl
    | cons marker markers induction =>
        simp [induction, Nat.mul_succ, Nat.add_comm]
  rw [emittedLength]
  have specification := variableCount_shape_descriptors source
  rw [FormulaShapeDirectionOrdering.variableCount_shape,
    FormulaShapeDirectionOrdering.variableCount_shape] at specification
  change (sourceVariableMarkers (descriptors source)).length =
      FormulaShapeFixedEight.copiesPerVariable *
        (sourceVariableMarkers source).length at specification
  exact specification.symm

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
