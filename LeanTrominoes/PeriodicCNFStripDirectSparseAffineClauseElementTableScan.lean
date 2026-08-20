/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexExplicitRedClauseScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexExplicitGreenClauseScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexExplicitBlueClauseScan

/-! # One finite table for all retained colored clause vertices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Local position of the color's internal clause vertex. -/
def horizontalThreeDMClauseInternalPositionForColor :
    WireColor → Cell
  | .red =>
      X3CClauseOrthogonal.elementPosition (.internal .left)
  | .green =>
      X3CClauseOrthogonal.elementPosition (.internal .right)
  | .blue =>
      X3CClauseOrthogonal.elementPosition (.internal .bottom)

/-- The retained local clause vertices of one color.  Every binary or ternary
clause retains its internal, top, and left vertices; precisely a ternary
clause also retains the right terminal. -/
def horizontalThreeDMRetainedClauseLocalPositions
    (color : WireColor) (clauseLength : Nat) : List Cell :=
  [horizontalThreeDMClauseInternalPositionForColor color,
    X3CClauseOrthogonal.elementPosition
      (.terminal (terminalElementForColor color .top)),
    X3CClauseOrthogonal.elementPosition
      (.terminal (terminalElementForColor color .left))] ++
    if clauseLength = 3 then
      [X3CClauseOrthogonal.elementPosition
        (.terminal (terminalElementForColor color .right))]
    else
      []

@[simp] theorem horizontalThreeDMRetainedClauseLocalPositions_length
    (color : WireColor) (clauseLength : Nat) :
    (horizontalThreeDMRetainedClauseLocalPositions
      color clauseLength).length =
      if clauseLength = 3 then 4 else 3 := by
  by_cases arity : clauseLength = 3 <;>
    simp [horizontalThreeDMRetainedClauseLocalPositions, arity]

/-- Translate the finite retained local table to one clause macrocell. -/
def horizontalThreeDMRetainedClausePositionBlockComputed
    (source : PeriodicCNF Nat) (color : WireColor)
    (tagged : PeriodicClause RoutedVariable × Nat) : List Cell :=
  (horizontalThreeDMRetainedClauseLocalPositions
      color tagged.1.length).map fun position =>
    Cell.add (horizontalThreeDMClauseOriginComputed source tagged.2)
      position

@[simp] theorem horizontalThreeDMRetainedClausePositionBlockComputed_length
    (source : PeriodicCNF Nat) (color : WireColor)
    (tagged : PeriodicClause RoutedVariable × Nat) :
    (horizontalThreeDMRetainedClausePositionBlockComputed
      source color tagged).length =
      if tagged.1.length = 3 then 4 else 3 := by
  simp [horizontalThreeDMRetainedClausePositionBlockComputed]

/-- Uniform affine request scan for one color's retained clause vertices. -/
def directSparseComputedAffineTableClauseElementRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMTypedSourceComputed source).clauses.zipIdx.flatMap
    fun tagged =>
      (horizontalThreeDMRetainedClausePositionBlockComputed
        source color tagged).flatMap fun position =>
        directSparseComputedAffinePositionRequestRecord
          input.drawing.gridSize position
          (.monochromaticVertex color)

theorem directSparseComputedAffineExplicitRedClauseRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineExplicitRedClauseRequests source input =
      directSparseComputedAffineTableClauseElementRequests
        source input .red := by
  unfold directSparseComputedAffineExplicitRedClauseRequests
    directSparseComputedAffineTableClauseElementRequests
    horizontalThreeDMRedDegreeThreeClauseElementsComputed
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro tagged _
  by_cases arity : tagged.1.length = 3 <;>
    simp [arity,
    horizontalThreeDMRetainedClausePositionBlockComputed,
    horizontalThreeDMRetainedClauseLocalPositions,
    horizontalThreeDMClauseInternalPositionForColor,
    horizontalThreeDMRedPositionComputed,
    PeriodicPlanarOneInThreeToThreeDM.assembledRedElementPositionData,
    PeriodicPlanarOneInThreeToThreeDM.redClauseElementLocalPosition]

theorem directSparseComputedAffineExplicitGreenClauseRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineExplicitGreenClauseRequests source input =
      directSparseComputedAffineTableClauseElementRequests
        source input .green := by
  unfold directSparseComputedAffineExplicitGreenClauseRequests
    directSparseComputedAffineTableClauseElementRequests
    horizontalThreeDMGreenDegreeThreeClauseElementsComputed
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro tagged _
  by_cases arity : tagged.1.length = 3 <;>
    simp [arity,
    horizontalThreeDMRetainedClausePositionBlockComputed,
    horizontalThreeDMRetainedClauseLocalPositions,
    horizontalThreeDMClauseInternalPositionForColor,
    horizontalThreeDMGreenPositionComputed,
    PeriodicPlanarOneInThreeToThreeDM.assembledGreenElementPositionData,
    PeriodicPlanarOneInThreeToThreeDM.greenClauseElementLocalPosition]

theorem directSparseComputedAffineExplicitBlueClauseRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineExplicitBlueClauseRequests source input =
      directSparseComputedAffineTableClauseElementRequests
        source input .blue := by
  unfold directSparseComputedAffineExplicitBlueClauseRequests
    directSparseComputedAffineTableClauseElementRequests
    horizontalThreeDMBlueDegreeThreeClauseElementsComputed
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro tagged _
  by_cases arity : tagged.1.length = 3 <;>
    simp [arity,
    horizontalThreeDMRetainedClausePositionBlockComputed,
    horizontalThreeDMRetainedClauseLocalPositions,
    horizontalThreeDMClauseInternalPositionForColor,
    horizontalThreeDMBluePositionComputed,
    PeriodicPlanarOneInThreeToThreeDM.assembledBlueElementPositionData,
    PeriodicPlanarOneInThreeToThreeDM.blueClauseElementLocalPosition]

theorem directSparseComputedAffineIndexedRedRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .red =
      directSparseComputedAffineTableClauseElementRequests
        source input .red := by
  rw [directSparseComputedAffineIndexedRedRequests_eq_explicit
      source input problemEq,
    directSparseComputedAffineExplicitRedClauseRequests_eq_table]

theorem directSparseComputedAffineIndexedGreenRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .green =
      directSparseComputedAffineTableClauseElementRequests
        source input .green := by
  rw [directSparseComputedAffineIndexedGreenRequests_eq_explicit
      source input problemEq,
    directSparseComputedAffineExplicitGreenClauseRequests_eq_table]

theorem directSparseComputedAffineIndexedBlueRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .blue =
      directSparseComputedAffineTableClauseElementRequests
        source input .blue := by
  rw [directSparseComputedAffineIndexedBlueRequests_eq_explicit
      source input problemEq,
    directSparseComputedAffineExplicitBlueClauseRequests_eq_table]

end PeriodicCNFStripReduction
end LeanTrominoes
