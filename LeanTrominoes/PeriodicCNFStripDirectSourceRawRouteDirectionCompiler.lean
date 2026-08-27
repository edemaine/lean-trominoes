/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDelimitedDirectionStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDirectionStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineScaledReversedDelimitedDirectionStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineScaledReversedDirectionStreamCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct compilation of raw source-route directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRawRouteDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceRawRouteDirectionCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete unnormalized direction words of the direct source's incidence
routes, concatenated in descriptor order. -/
def directSourceRawRouteDirections
    (symbols : List encoding.Γ) : List AxisDirection :=
  RouteDescriptorPairAffine.diagonalDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- The same raw route stream with one explicit boundary after every source
incidence route. -/
def directSourceRawRouteDirectionBlocks
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken :=
  RouteDescriptorPairAffine.diagonalDelimitedDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- Complete direct-source raw route words after the horizontal occurrence
construction's doubling and reversal. -/
def directSourceScaledReversedRawRouteDirections
    (symbols : List encoding.Γ) : List AxisDirection :=
  RouteDescriptorPairAffine.diagonalScaledReversedDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- The doubled reversed raw words with one explicit route boundary per
source incidence. -/
def directSourceScaledReversedRawRouteDirectionBlocks
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken :=
  RouteDescriptorPairAffine.diagonalScaledReversedDelimitedDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- The compiled stream is exactly the complete raw semantic route word in
descriptor order. -/
theorem directSourceRawRouteDirections_eq
    (symbols : List encoding.Γ) :
    directSourceRawRouteDirections decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
          Gadget.unitSubdivisionDirections descriptor.route := by
  unfold directSourceRawRouteDirections
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact RouteDescriptorPairAffine.diagonalDirectionStream_numericRouteDescriptors
    (directSourceFormula decider symbols)
    (PeriodicCNF.incidenceGraph_isWellFormed _)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    (by
      unfold directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
    (directSourceFormula_isForwardLocal decider symbols)

/-- Delimited direct-source output is exactly one raw direction block per
numeric route descriptor. -/
theorem directSourceRawRouteDirectionBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceRawRouteDirectionBlocks decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
          (Gadget.unitSubdivisionDirections descriptor.route).map
              PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken.direction ++
            [.routeEnd] := by
  unfold directSourceRawRouteDirectionBlocks
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact RouteDescriptorPairAffine.diagonalDelimitedDirectionStream_numericRouteDescriptors
    (directSourceFormula decider symbols)
    (PeriodicCNF.incidenceGraph_isWellFormed _)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    (by
      unfold directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
    (directSourceFormula_isForwardLocal decider symbols)

/-- The scaled-reversed direct-source stream is exactly the semantic numeric
route family after the horizontal occurrence transform. -/
theorem directSourceScaledReversedRawRouteDirections_eq
    (symbols : List encoding.Γ) :
    directSourceScaledReversedRawRouteDirections decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
          Gadget.unitSubdivisionDirections
            (scalePolyline 2 descriptor.route).reverse := by
  unfold directSourceScaledReversedRawRouteDirections
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact RouteDescriptorPairAffine.diagonalScaledReversedDirectionStream_numericRouteDescriptors
    (directSourceFormula decider symbols)
    (PeriodicCNF.incidenceGraph_isWellFormed _)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    (by
      unfold directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
    (directSourceFormula_isForwardLocal decider symbols)

/-- The delimited scaled-reversed stream has one exact semantic block per
numeric source route. -/
theorem directSourceScaledReversedRawRouteDirectionBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceScaledReversedRawRouteDirectionBlocks decider symbols =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
          (Gadget.unitSubdivisionDirections
              (scalePolyline 2 descriptor.route).reverse).map
              PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken.direction ++
            [.routeEnd] := by
  unfold directSourceScaledReversedRawRouteDirectionBlocks
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact RouteDescriptorPairAffine.diagonalScaledReversedDelimitedDirectionStream_numericRouteDescriptors
    (directSourceFormula decider symbols)
    (PeriodicCNF.incidenceGraph_isWellFormed _)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    (by
      unfold directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
    (directSourceFormula_isForwardLocal decider symbols)

/-- Direct source symbols compile to the complete raw incidence-route
direction stream in polynomial time. -/
noncomputable def directSourceRawRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceRawRouteDirections decider) := by
  let tagged :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let selected := TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.diagonalDirectionStreamComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols => RouteDescriptorPairAffine.diagonalDirectionStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact selected

/-- Direct source symbols compile to the route-delimited raw direction stream
in polynomial time. -/
noncomputable def directSourceRawRouteDirectionBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceRawRouteDirectionBlocks decider) := by
  let tagged :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let selected := TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.diagonalDelimitedDirectionStreamComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols => RouteDescriptorPairAffine.diagonalDelimitedDirectionStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact selected

/-- Direct source symbols compile to all doubled reversed raw route words. -/
noncomputable def
    directSourceScaledReversedRawRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceScaledReversedRawRouteDirections decider) := by
  let tagged :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let selected := TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.diagonalScaledReversedDirectionStreamComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      RouteDescriptorPairAffine.diagonalScaledReversedDirectionStream
        (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact selected

/-- Direct source symbols compile to the route-delimited doubled reversed raw
stream. -/
noncomputable def
    directSourceScaledReversedRawRouteDirectionBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceScaledReversedRawRouteDirectionBlocks decider) := by
  let tagged :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let selected := TM2CompositionMachine.computableInPolyTime tagged
    RouteDescriptorPairAffine.diagonalScaledReversedDelimitedDirectionStreamComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      RouteDescriptorPairAffine.diagonalScaledReversedDelimitedDirectionStream
        (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact selected

end PeriodicCNFStripReduction
end LeanTrominoes

end
