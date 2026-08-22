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
def currentizeRoutedClauseProfiles
    (profile : ClauseProfile) : List LiteralProfile :=
  profile.literals.map fun literal => ⟨false, literal.value⟩

/-- Emit the fixed neighboring-site block for one source clause profile. -/
def directRetainedPlanarMetadataRoutedClauseDescriptorBlock
    (profile : ClauseProfile) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicOrthocrossing.neighborTranslations.map fun _ =>
    FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
      (currentizeRoutedClauseProfiles profile)

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
