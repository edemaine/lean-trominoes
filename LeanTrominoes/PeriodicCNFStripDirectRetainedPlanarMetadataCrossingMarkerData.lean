/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicOrthocrossingCanonicalPairScan

/-! # Direct retained metadata crossing-marker data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossingMarkerDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedCrossingMarkerDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Four boundary variables and nine internal variables are retained for each
canonical oriented crossing. -/
def directRetainedPlanarMetadataCrossingMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (13 * (orientedCrossings
      (directSourceFormula decider symbols).incidenceGraph).length)
    .variable

/-- Executable quadratic-pair-scan presentation of the same marker count. -/
def directRetainedPlanarMetadataCrossingPairMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (13 * (orientedCrossingPairScan
      (directSourceFormula decider symbols).incidenceGraph).length)
    .variable

/-- The precise remaining crossing-emission compiler boundary. -/
abbrev DirectRetainedPlanarMetadataCrossingMarkerCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarMetadataCrossingMarkers decider)

/-- Reduced compiler boundary using only the quadratic occurrence-pair scan. -/
abbrev DirectRetainedPlanarMetadataCrossingPairMarkerCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token
    id id (directRetainedPlanarMetadataCrossingPairMarkers decider)

end LeanTrominoes.PeriodicCNFStripReduction
