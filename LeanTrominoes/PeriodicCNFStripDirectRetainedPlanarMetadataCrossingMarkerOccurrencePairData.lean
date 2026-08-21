/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerData
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairs

/-! # Direct retained metadata occurrence-pair crossing markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossingOccurrencePairDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedCrossingOccurrencePairDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Thirteen markers per directly accepted ordered segment-occurrence pair. -/
def directRetainedPlanarMetadataCrossingOccurrencePairMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (13 * (orientedCrossingOccurrencePairs
      (directSourceFormula decider symbols).incidenceGraph).length)
    .variable

/-- Smallest current crossing compiler boundary: emit thirteen markers for
each pair accepted by one Boolean filter over the ordered occurrence product. -/
abbrev DirectRetainedPlanarMetadataCrossingOccurrencePairMarkerCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarMetadataCrossingOccurrencePairMarkers decider)

end LeanTrominoes.PeriodicCNFStripReduction
