/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerRouteDirections

/-! # Finite requests for dynamic route-direction normalization -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open DegreeThreeVertexNormalization
open Gadget
open NormalizationCompiler

/-- One of the twelve first-round direction-normalizing templates. -/
structure FirstTemplateChoice where
  omitted : VertexSide
  port : CanonicalVertexPort
  deriving DecidableEq, Fintype, Repr

/-- One of the six identity/clockwise cyclic templates. -/
structure RotationTemplateChoice where
  active : Bool
  port : CanonicalVertexPort
  deriving DecidableEq, Fintype, Repr

/-- All six finite template selections retained across the three passes. -/
structure Header where
  firstSource : FirstTemplateChoice
  firstTarget : FirstTemplateChoice
  secondSource : RotationTemplateChoice
  secondTarget : RotationTemplateChoice
  finalSource : RotationTemplateChoice
  finalTarget : RotationTemplateChoice
  deriving DecidableEq, Fintype, Repr

/-- A finite header followed by one already unit-subdivided route word. -/
structure Request where
  header : Header
  directions : List AxisDirection
  deriving DecidableEq, Repr

/-- Canonically tagged tape alphabet for a dynamic normalization request. -/
inductive Token
  | firstSource (choice : FirstTemplateChoice)
  | firstTarget (choice : FirstTemplateChoice)
  | secondSource (choice : RotationTemplateChoice)
  | secondTarget (choice : RotationTemplateChoice)
  | finalSource (choice : RotationTemplateChoice)
  | finalTarget (choice : RotationTemplateChoice)
  | separator
  | direction (value : AxisDirection)
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The three passes select disjoint pairs from the retained header. -/
inductive Round
  | first
  | second
  | final
  deriving DecidableEq, Fintype, Repr

def FirstTemplateChoice.template
    (choice : FirstTemplateChoice) : List Cell :=
  route choice.omitted choice.port

def RotationTemplateChoice.template
    (choice : RotationTemplateChoice) : List Cell :=
  (rotationRoundPortAndRoute choice.active choice.port).2

def Header.sourceTemplate : Round → Header → List Cell
  | .first, header => header.firstSource.template
  | .second, header => header.secondSource.template
  | .final, header => header.finalSource.template

def Header.targetTemplate : Round → Header → List Cell
  | .first, header => header.firstTarget.template
  | .second, header => header.secondTarget.template
  | .final, header => header.finalTarget.template

/-- Fixed-width canonical header encoding. -/
def Header.tokens (header : Header) : List Token :=
  [.firstSource header.firstSource,
    .firstTarget header.firstTarget,
    .secondSource header.secondSource,
    .secondTarget header.secondTarget,
    .finalSource header.finalSource,
    .finalTarget header.finalTarget]

def Request.tokens (request : Request) : List Token :=
  request.header.tokens ++
    (.separator :: request.directions.map .direction)

/-- Mathematical effect of one dynamically selected normalization round. -/
def normalizeRound (round : Round) (request : Request) : Request :=
  { header := request.header
    directions :=
      normalizationDirectionWord
        (request.header.sourceTemplate round)
        (request.header.targetTemplate round)
        request.directions }

def normalizeThreeRounds (request : Request) : Request :=
  normalizeRound .final
    (normalizeRound .second (normalizeRound .first request))

/-- The exact six finite choices and initial unit directions of one
data-only contracted edge. -/
def ofEdge (input : NormalizationCompiler.Input)
    (edge : ContractedEdge) : Request where
  header :=
    { firstSource :=
        ⟨NormalizationCompiler.omittedSideAt
            input edge.toPeriodicEdge.source,
          NormalizationCompiler.firstNormalizedPort
            input (.source edge)⟩
      firstTarget :=
        ⟨NormalizationCompiler.omittedSideAt
            input edge.toPeriodicEdge.target,
          NormalizationCompiler.firstNormalizedPort
            input (.target edge)⟩
      secondSource :=
        ⟨NormalizationCompiler.firstRotationActive
            input edge.toPeriodicEdge.source,
          NormalizationCompiler.firstNormalizedPort
            input (.source edge)⟩
      secondTarget :=
        ⟨NormalizationCompiler.firstRotationActive
            input edge.toPeriodicEdge.target,
          NormalizationCompiler.firstNormalizedPort
            input (.target edge)⟩
      finalSource :=
        ⟨NormalizationCompiler.secondRotationActive
            input edge.toPeriodicEdge.source,
          NormalizationCompiler.secondNormalizedPort
            input (.source edge)⟩
      finalTarget :=
        ⟨NormalizationCompiler.secondRotationActive
            input edge.toPeriodicEdge.target,
          NormalizationCompiler.secondNormalizedPort
            input (.target edge)⟩ }
  directions := unitSubdivisionDirections
    (NormalizationCompiler.contractedEdgeRoute input edge)

@[simp]
theorem ofEdge_firstSourceTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.sourceTemplate .first =
      firstNormalizationTemplate input (.source edge) := by
  rfl

@[simp]
theorem ofEdge_firstTargetTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.targetTemplate .first =
      firstNormalizationTemplate input (.target edge) := by
  rfl

@[simp]
theorem ofEdge_secondSourceTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.sourceTemplate .second =
      secondNormalizationTemplate input (.source edge) := by
  rfl

@[simp]
theorem ofEdge_secondTargetTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.targetTemplate .second =
      secondNormalizationTemplate input (.target edge) := by
  rfl

@[simp]
theorem ofEdge_finalSourceTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.sourceTemplate .final =
      finalNormalizationTemplate input (.source edge) := by
  rfl

@[simp]
theorem ofEdge_finalTargetTemplate
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (ofEdge input edge).header.targetTemplate .final =
      finalNormalizationTemplate input (.target edge) := by
  rfl

/-- Evaluating the three finite header pairs gives exactly the previously
defined proof-free final direction word. -/
theorem normalizeThreeRounds_ofEdge_directions
    (input : NormalizationCompiler.Input) (edge : ContractedEdge) :
    (normalizeThreeRounds (ofEdge input edge)).directions =
      finalNormalizationRouteDirections input edge := by
  rfl

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
