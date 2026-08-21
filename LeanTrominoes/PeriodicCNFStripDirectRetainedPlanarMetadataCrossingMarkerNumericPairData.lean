/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumerationData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerOccurrencePairData

/-! # Direct retained numeric crossing-pair markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedNumericCrossingPairDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedNumericCrossingPairDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Thirteen markers per pair retained by the compact numeric route and
segment scan. -/
def directRetainedPlanarMetadataCrossingNumericPairMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (13 * (numericOrientedCrossingOccurrencePairs
      (directSourceFormula decider symbols)).length)
    .variable

/-- Numeric route/segment crossing-marker compiler boundary. -/
abbrev DirectRetainedPlanarMetadataCrossingNumericPairMarkerCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarMetadataCrossingNumericPairMarkers decider)

end LeanTrominoes.PeriodicCNFStripReduction
