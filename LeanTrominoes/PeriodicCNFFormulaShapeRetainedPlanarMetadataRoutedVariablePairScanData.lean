/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Finite descriptor-pair scan for routed-variable clauses -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The current-slice descriptor block of one arm. -/
def routedVariableCurrentArmBlock (arm : DuplicatorArm) :
    List FormulaShapeDirectionOrdering.Token :=
  canonicalRoutedVariableDescriptorBlock arm false

/-- The complete three-arm block at a site reached by all three incidences. -/
def routedVariableFullSiteBlock :
    List FormulaShapeDirectionOrdering.Token :=
  routedVariableCurrentArmBlock .left ++
    routedVariableCurrentArmBlock .middle ++
      routedVariableCurrentArmBlock .right

/-- The two cycle arms at the left boundary of a next-slice occurrence. -/
def routedVariableCycleOnlySiteBlock :
    List FormulaShapeDirectionOrdering.Token :=
  routedVariableCurrentArmBlock .middle ++
    routedVariableCurrentArmBlock .right

/-- Three original-incidence-only sites precede the cycle suffix for each
next-slice source occurrence. -/
def routedVariableNextBoundaryBlock :
    List FormulaShapeDirectionOrdering.Token :=
  (List.replicate 3 (routedVariableCurrentArmBlock .left)).flatten

/-- A current-slice source occurrence has nine full sites. -/
def routedVariableCurrentCycleBlock :
    List FormulaShapeDirectionOrdering.Token :=
  (List.replicate 9 routedVariableFullSiteBlock).flatten

/-- A next-slice source occurrence has three cycle-only left sites followed
by six full sites. -/
def routedVariableNextCycleBlock :
    List FormulaShapeDirectionOrdering.Token :=
  (List.replicate 3 routedVariableCycleOnlySiteBlock).flatten ++
    (List.replicate 6 routedVariableFullSiteBlock).flatten

/-- The diagonal occurrence-descriptor pair that contributes the three
early right-boundary sites of a next-slice occurrence. -/
def routedVariableNextBoundaryPair
    (pair : RouteDescriptor × RouteDescriptor) : Bool :=
  decide
    (pair.1.edgeIndex = pair.2.edgeIndex ∧
      pair.1.targetPortRank = 0 ∧
        pair.1.offset = ((1, 0) : Cell))

/-- A rank-two cycle incidence joined to its current-slice rank-zero source
occurrence by variable-vertex index. -/
def routedVariableCurrentCyclePair
    (pair : RouteDescriptor × RouteDescriptor) : Bool :=
  decide
    (pair.1.targetPortRank = 2 ∧
      pair.2.targetPortRank = 0 ∧
        pair.1.targetVertexIndex = pair.2.targetVertexIndex ∧
          pair.2.offset = ((0, 0) : Cell))

/-- A rank-two cycle incidence joined to its next-slice rank-zero source
occurrence by variable-vertex index. -/
def routedVariableNextCyclePair
    (pair : RouteDescriptor × RouteDescriptor) : Bool :=
  decide
    (pair.1.targetPortRank = 2 ∧
      pair.2.targetPortRank = 0 ∧
        pair.1.targetVertexIndex = pair.2.targetVertexIndex ∧
          pair.2.offset = ((1, 0) : Cell))

/-- Fixed output contributed by one ordered numeric descriptor pair. -/
def routedVariablePairDescriptorBlock
    (pair : RouteDescriptor × RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  (if routedVariableNextBoundaryPair pair then
      routedVariableNextBoundaryBlock else []) ++
    (if routedVariableCurrentCyclePair pair then
      routedVariableCurrentCycleBlock else []) ++
    (if routedVariableNextCyclePair pair then
      routedVariableNextCycleBlock else [])

/-- Row-major descriptor-pair scan used by the direct compiler. -/
def routedVariablePairDescriptorScan
    (descriptors : List RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  (descriptors ×ˢ descriptors).flatMap
    routedVariablePairDescriptorBlock

@[simp] theorem routedVariableNextBoundaryBlock_length :
    routedVariableNextBoundaryBlock.length = 6 := by
  simp [routedVariableNextBoundaryBlock, routedVariableCurrentArmBlock]

@[simp] theorem routedVariableCurrentCycleBlock_length :
    routedVariableCurrentCycleBlock.length = 54 := by
  simp [routedVariableCurrentCycleBlock, routedVariableFullSiteBlock,
    routedVariableCurrentArmBlock]

@[simp] theorem routedVariableNextCycleBlock_length :
    routedVariableNextCycleBlock.length = 48 := by
  simp [routedVariableNextCycleBlock, routedVariableCycleOnlySiteBlock,
    routedVariableFullSiteBlock, routedVariableCurrentArmBlock]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
