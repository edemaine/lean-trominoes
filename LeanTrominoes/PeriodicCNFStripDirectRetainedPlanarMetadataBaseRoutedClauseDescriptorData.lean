/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorData

/-! # Direct normalized routed-clause descriptor blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One routed source-clause descriptor after periodic normalization has
identified its nine translated physical sites. -/
def directRetainedPlanarMetadataBaseRoutedClauseDescriptorBlock
    (profile : ClauseProfile) :
    List FormulaShapeDirectionOrdering.Token :=
  [FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
    (currentizeRoutedClauseProfiles profile)]

/-- One normalized routed descriptor per source clause profile. -/
def directRetainedPlanarMetadataBaseRoutedClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directSourceFormulaClauseProfiles decider symbols).flatMap
    directRetainedPlanarMetadataBaseRoutedClauseDescriptorBlock

abbrev DirectRetainedPlanarMetadataBaseRoutedClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataBaseRoutedClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
