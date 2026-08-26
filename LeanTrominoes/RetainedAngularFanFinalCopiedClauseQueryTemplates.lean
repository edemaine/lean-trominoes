/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairScanData

/-! # Stable finite query templates for final copied clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Replace the directions of one finite profile by stable direct-atlas
queries at the same one, two, or three literal positions. -/
def RetainedFinalCopiedClauseQuery.directOfProfile
    (kind : RetainedDirectClauseKind) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile →
      RetainedFinalCopiedClauseQuery
  | .unary first _ =>
      .unary first (.direct ⟨kind, 0⟩)
  | .binary first _ second _ =>
      .binary first (.direct ⟨kind, 0⟩)
        second (.direct ⟨kind, 1⟩)
  | .ternary first _ second _ third _ =>
      .ternary first (.direct ⟨kind, 0⟩)
        second (.direct ⟨kind, 1⟩)
        third (.direct ⟨kind, 2⟩)

/-- Apply a direct-atlas kind to a clause token.  The variable branch is a
total fallback and is unused by clause-family blocks. -/
def RetainedFinalCopiedClauseQuery.directOfToken
    (kind : RetainedDirectClauseKind) :
    FormulaShapeDirectionOrdering.Token →
      RetainedFinalCopiedClauseQuery
  | .clause profile => .directOfProfile kind profile
  | .variable => default

/-- Preserve any already-final finite descriptor as a query. -/
def retainedFinalPrecomputedClauseQueries
    (tokens : List FormulaShapeDirectionOrdering.Token) :
    List RetainedFinalCopiedClauseQuery :=
  tokens.map RetainedFinalCopiedClauseQuery.precomputed

/-- Evaluating precomputed queries is exactly the original token stream. -/
@[simp] theorem retainedFinalCopiedClauseDescriptors_precomputed
    (tokens : List FormulaShapeDirectionOrdering.Token) :
    retainedFinalCopiedClauseDescriptors
        (retainedFinalPrecomputedClauseQueries tokens) =
      tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      change
        token ::
            retainedFinalCopiedClauseDescriptors
              (retainedFinalPrecomputedClauseQueries tokens) =
          token :: tokens
      rw [induction]

/-- Final direct query for one local crossover clause. -/
def retainedFinalDirectCrossoverClauseQueryAt
    (clauseIndex : Fin 26) : RetainedFinalCopiedClauseQuery :=
  RetainedFinalCopiedClauseQuery.directOfToken
    (.crossover clauseIndex)
    (FormulaShapeCrossoverDirection.descriptors.getD
      clauseIndex.val default)

/-- Fixed twenty-six-query block for one retained crossover. -/
def retainedFinalDirectCrossoverClauseQueries :
    List RetainedFinalCopiedClauseQuery :=
  (List.finRange 26).map retainedFinalDirectCrossoverClauseQueryAt

/-- Two consecutive crossover queries emitted at one position of a
thirteen-marker group. -/
def retainedFinalDirectCrossoverClauseQueryPair
    (index : Fin 13) : List RetainedFinalCopiedClauseQuery :=
  (retainedFinalDirectCrossoverClauseQueries.drop
    (2 * index.val)).take 2

/-- Forward and reverse duplicator implications have local indices zero and
one, respectively. -/
def retainedFinalDirectDuplicatorClauseIndex : Bool → Fin 2
  | true => 0
  | false => 1

/-- Final direct query for one routed-variable implication template. -/
def retainedFinalDirectRoutedVariableClauseQuery
    (arm : DuplicatorArm) (nextSlice forward : Bool) :
    RetainedFinalCopiedClauseQuery :=
  RetainedFinalCopiedClauseQuery.directOfToken
    (.duplicator arm
      (retainedFinalDirectDuplicatorClauseIndex forward))
    (routedVariableClauseDescriptor arm nextSlice forward)

/-- The two current-slice direct queries of one routed-variable arm. -/
def retainedFinalDirectRoutedVariableCurrentArmQueries
    (arm : DuplicatorArm) : List RetainedFinalCopiedClauseQuery :=
  [retainedFinalDirectRoutedVariableClauseQuery arm false true,
    retainedFinalDirectRoutedVariableClauseQuery arm false false]

/-- The complete six-query direct routed-variable block at one site. -/
def retainedFinalDirectRoutedVariableFullSiteQueries :
    List RetainedFinalCopiedClauseQuery :=
  retainedFinalDirectRoutedVariableCurrentArmQueries .left ++
    retainedFinalDirectRoutedVariableCurrentArmQueries .middle ++
      retainedFinalDirectRoutedVariableCurrentArmQueries .right

/-- Final direct query for one normalized routed source clause. -/
def retainedFinalDirectRoutedClauseQuery
    (profiles : List UnaryProgramClauseProfile.LiteralProfile) :
    RetainedFinalCopiedClauseQuery :=
  RetainedFinalCopiedClauseQuery.directOfToken .routedClause
    (routedClauseDescriptor profiles)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
