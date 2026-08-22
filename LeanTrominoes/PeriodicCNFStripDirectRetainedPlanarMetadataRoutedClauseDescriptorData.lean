/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaClauseProfiles

/-! # Direct finite routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Clear the slice bit of every literal profile and retain its polarity. -/
def currentizeRoutedLiteralProfiles
    (profiles : List LiteralProfile) : List LiteralProfile :=
  profiles.map fun literal => ⟨false, literal.value⟩

/-- Currentize the finite literals of one clause profile. -/
def currentizeRoutedClauseProfiles
    (profile : ClauseProfile) : List LiteralProfile :=
  currentizeRoutedLiteralProfiles profile.literals

/-- Emit the fixed neighboring-site block from a finite literal-profile
list. -/
def directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles
    (profiles : List LiteralProfile) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicOrthocrossing.neighborTranslations.map fun _ =>
    FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
      (currentizeRoutedLiteralProfiles profiles)

/-- Emit the fixed neighboring-site block for one source clause profile. -/
def directRetainedPlanarMetadataRoutedClauseDescriptorBlock
    (profile : ClauseProfile) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles
    profile.literals

/-- Presentation-order source-clause blocks before replacing semantic
literal lists by their compiled finite profiles. -/
def directRetainedPlanarMetadataRoutedClauseSourceBlocks
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormula decider symbols).clauses.flatMap fun clause =>
    PeriodicOrthocrossing.neighborTranslations.map fun _ =>
      FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
        (clause.map fun literal =>
          (⟨false, literal.value⟩ : LiteralProfile))

/-- The same source-clause stream factored through its semantic finite
literal profiles. -/
def directRetainedPlanarMetadataRoutedClauseProfileBlocks
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  ((directSourceFormula decider symbols).clauses.map
      ClauseProfileOccurrenceSplit.literalProfiles).flatMap
    directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles

/-- The finite-state routed-clause stream compiled from exact source
clause profiles. -/
def directRetainedPlanarMetadataCompiledRoutedClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaClauseProfiles decider symbols).flatMap
    directRetainedPlanarMetadataRoutedClauseDescriptorBlock

abbrev DirectRetainedPlanarMetadataCompiledRoutedClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCompiledRoutedClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
