/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorPairs
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerData

/-! # Direct fixed crossover clause-descriptor streams -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossoverClauseDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedCrossoverClauseDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The finite-state postprocess applied to the existing thirteen-marker
stream. -/
def directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  ThirteenMarkerPairBlocks.output
    FormulaShapeCrossoverDirection.descriptorPair
    (directRetainedPlanarMetadataCrossingMarkers decider symbols)

/-- One fixed twenty-six-token crossover descriptor block per canonical
oriented crossing. -/
def directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (List.replicate
    (orientedCrossings
      (directSourceFormula decider symbols).incidenceGraph).length
    FormulaShapeCrossoverDirection.descriptors).flatten

abbrev DirectRetainedPlanarMetadataCompiledCrossoverClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataFixedCrossoverClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataFixedCrossoverClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
