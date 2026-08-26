/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorData

/-! # Per-family quotient descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Quotiented routed-clause and routed-variable tail. -/
def directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataBaseRoutedClauseDescriptors
      decider symbols ++
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
      decider symbols

/-- Quotiented bend family followed by the routed tail. -/
def directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataBaseBendClauseDescriptors
      decider symbols ++
    directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffix
      decider symbols

/-- Injective carrier family followed by all translated-family quotients. -/
def directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffix
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols ++
    directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffix
      decider symbols

/-- Candidate public clause-descriptor stream after applying each family's
known periodic quotient: fixed crossovers, injective retained carriers, one
copy per bend, one copy per routed source clause, and one routed-variable
arm triple per cycle.  Its equality with global representative selection is
proved at a separate semantic boundary. -/
def directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
      decider symbols ++
    directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffix
      decider symbols

abbrev DirectRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataQuotientBendClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffixCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffix decider)

abbrev DirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataQuotientClauseDescriptorAssembly decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
