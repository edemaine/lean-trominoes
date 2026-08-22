/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Direct retained clause-descriptor family streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedClauseFamilyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedClauseFamilyDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

def directRetainedPlanarMetadataClauseDescriptorCandidates
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.metadataClauseDescriptorCandidates
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataCrossoverClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataCarrierClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataBendClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.bendMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataRoutedClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.routedClauseMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataRoutedVariableClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.routedVariableMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataFamilyClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.familyMetadataClauseDescriptors
      (directSourceFormula decider symbols)

def directRetainedPlanarMetadataRoutedClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataRoutedClauseDescriptors decider symbols ++
    directRetainedPlanarMetadataRoutedVariableClauseDescriptors
      decider symbols

def directRetainedPlanarMetadataBendClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataBendClauseDescriptors decider symbols ++
    directRetainedPlanarMetadataRoutedClauseDescriptorSuffix decider symbols

def directRetainedPlanarMetadataCarrierClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols ++
    directRetainedPlanarMetadataBendClauseDescriptorSuffix decider symbols

def directRetainedPlanarMetadataAssembledFamilyClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataCrossoverClauseDescriptors decider symbols ++
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffix decider symbols

abbrev DirectRetainedPlanarMetadataClauseDescriptorCandidateCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataClauseDescriptorCandidates decider)

abbrev DirectRetainedPlanarMetadataFamilyClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataFamilyClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataRoutedClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataRoutedClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataBendClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataBendClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataCarrierClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCarrierClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataAssembledFamilyClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataAssembledFamilyClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataCrossoverClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCrossoverClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCarrierClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataBendClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataBendClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataRoutedClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataRoutedClauseDescriptors decider)

abbrev DirectRetainedPlanarMetadataRoutedVariableClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataRoutedVariableClauseDescriptors decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
