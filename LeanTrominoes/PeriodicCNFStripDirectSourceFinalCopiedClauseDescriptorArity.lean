/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCopiedClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDeduplicatedClauseShape
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics

/-! # Arity sum of direct final copied-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDescriptorArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalDescriptorArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem copiedClauseProfile_arity_eq
    {OtherVariable : Type} [DecidableEq OtherVariable]
    (source : PeriodicCNF OtherVariable)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable OtherVariable))
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    (copiedClauseProfile source clauseIndex clause).taggedLiterals.length =
      clause.literals.length := by
  unfold copiedClauseProfile
  rw [DirectedClauseProfile.taggedLiterals_ofList]
  · simp
  · simpa using nonempty
  · simpa using width

private theorem presentationLiteralCount_erase_eq
    {OtherVariable : Type}
    (source : PositionedPeriodicCNF OtherVariable) :
    PeriodicCNF.presentationLiteralCount source.erase =
      (source.clauses.map fun clause => clause.literals.length).sum := by
  simp [PeriodicCNF.presentationLiteralCount,
    PositionedPeriodicCNF.erase, Function.comp_def]

/-- Copied-clause descriptors contain exactly one arity unit per literal when
the coordinated source is nonempty and width three. -/
private theorem copiedClauseDescriptors_aritySum_eq
    {OtherVariable : Type} [DecidableEq OtherVariable]
    (source : PeriodicCNF OtherVariable)
    (clausesNonempty : ∀ clause ∈ (finalCoordinatedSource source).clauses,
      clause.literals ≠ [])
    (clausesWidth : ∀ clause ∈ (finalCoordinatedSource source).clauses,
      clause.literals.length ≤ 3) :
    ((copiedClauseDescriptors source).map
        retainedFinalCopiedDescriptorArity).sum =
      PeriodicCNF.presentationLiteralCount
        (finalCoordinatedSource source).erase := by
  let clauses := (finalCoordinatedSource source).clauses
  have arities :
      (copiedClauseDescriptors source).map
          retainedFinalCopiedDescriptorArity =
        clauses.map fun clause => clause.literals.length := by
    unfold copiedClauseDescriptors
    simp only [List.map_map]
    calc
      _ = clauses.zipIdx.map fun taggedClause =>
          taggedClause.1.literals.length := by
        apply List.map_congr_left
        intro taggedClause taggedMember
        exact copiedClauseProfile_arity_eq source
          taggedClause.2 taggedClause.1
          (clausesNonempty taggedClause.1
            (List.fst_mem_of_mem_zipIdx taggedMember))
          (clausesWidth taggedClause.1
            (List.fst_mem_of_mem_zipIdx taggedMember))
      _ = clauses.map fun clause => clause.literals.length := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map fun clause => clause.literals.length)
            (List.zipIdx_map_fst 0 clauses)
  calc
    ((copiedClauseDescriptors source).map
        retainedFinalCopiedDescriptorArity).sum =
        (clauses.map fun clause => clause.literals.length).sum :=
      congrArg List.sum arities
    _ = PeriodicCNF.presentationLiteralCount
          (finalCoordinatedSource source).erase :=
      (presentationLiteralCount_erase_eq
        (finalCoordinatedSource source)).symm

/-- The public direct copied-clause descriptor prefix contains exactly one
arity unit for every literal of the final coordinated source. -/
theorem directSourceFinalCopiedClauseDescriptorAritySum_eq
    (symbols : List encoding.Γ) :
    ((directRetainedFigureNineCopiedClauseDescriptors decider symbols).map
        retainedFinalCopiedDescriptorArity).sum =
      PeriodicCNF.presentationLiteralCount
        (finalCoordinatedSource
          (directSourceFormula decider symbols)).erase := by
  rw [show directRetainedFigureNineCopiedClauseDescriptors decider symbols =
      copiedClauseDescriptors (directSourceFormula decider symbols) by rfl]
  apply copiedClauseDescriptors_aritySum_eq
  · intro clause clauseMember
    apply directSource_deduplicatedClauses_nonempty decider symbols
    rw [← finalCoordinatedSource_clauseLiterals_eq]
    exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
  · intro clause clauseMember
    apply directSource_deduplicatedClauses_widthAtMostThree decider symbols
    rw [← finalCoordinatedSource_clauseLiterals_eq]
    exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
