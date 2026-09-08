/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripIncidenceEndpointSummaryCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceBodyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteIncidenceHeaderSemantics
import LeanTrominoes.GadgetSparseRouteDirectionEndpoints

/-! # Compiled endpoint summaries agree with actual horizontal route headers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The actual first and last directions of a canonical incidence route. -/
def horizontalIncidenceEndpoints (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    IncidenceEndpointSummary.Endpoints :=
  (AxisDirection.polylineFirstDirection (horizontalAssembledRouteAtTagComputed (source, tag)),
    AxisDirection.polylineLastDirection (horizontalAssembledRouteAtTagComputed (source, tag)))

def horizontalIncidenceEndpointSummary (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    IncidenceEndpointSummary.Summary :=
  IncidenceEndpointSummary.atTag (horizontalIncidenceEndpoints source) tag

private theorem assembledRoute_orthogonal (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (horizontalAssembledRouteAtTagComputed (source, tag)) := by
  have width := horizontalSemanticNormalizedRibbonSource_widthAtMostThree source
  have compatible := horizontalSemanticNormalizedRibbonSource_fansCompatible source
  rw [horizontalAssembledRouteAtTagComputed_eq_semantic source width compatible]
  exact assembledRouteAtTag_orthogonal
    (coordinatedSourceRibbonThreeStrandRouting
      (horizontalSemanticNormalizedRibbonReadyPresentation source) width compatible) tag

/-- Taking endpoints of the compiled word gives the actual geometric
endpoints, with no nonempty-route assumption. -/
theorem horizontalCanonicalIncidenceDirectionBlock_endpoints
    (source : PeriodicCNF Nat) (tag : IncidenceTag)
    (member : tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags) :
    ((horizontalCanonicalIncidenceDirectionBlock source tag).directions.headD .invalid,
      (horizontalCanonicalIncidenceDirectionBlock source tag).directions.getLastD .invalid) =
      horizontalIncidenceEndpoints source tag := by
  rw [horizontalCanonicalIncidenceDirectionBlock_directions source tag member,
    unitSubdivisionDirections_headD _ (assembledRoute_orthogonal source tag),
    unitSubdivisionDirections_getLastD _ (assembledRoute_orthogonal source tag)]
  rfl

/-- The source-side finite header data is exactly recovered from the summary. -/
theorem horizontalIncidenceEndpointSummary_tripleEndpointData
    (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    (horizontalIncidenceEndpointSummary source tag).tripleEndpointData =
      horizontalAssembledTripleEndpointHeaderData source tag.tripleIndex tag.color := by
  unfold horizontalIncidenceEndpointSummary
  rw [IncidenceEndpointSummary.atTag_tripleEndpointData]
  simp only [horizontalAssembledTripleEndpointHeaderData,
    horizontalAssembledIncidenceColorTripleData,
    horizontalAssembledIncidenceSideColor, horizontalIncidenceEndpoints]

/-- The terminal summary also gives the exact outward side at a retained
 element endpoint. -/
theorem horizontalIncidenceEndpointSummary_retainedSideColor
    (source : PeriodicCNF Nat) (color : WireColor) (incidence : Incidence) :
    (horizontalIncidenceEndpointSummary source ⟨incidence.tripleIndex, color⟩).retainedSideColor =
      horizontalAssembledRetainedIncidenceSideColor source color incidence := by
  unfold horizontalIncidenceEndpointSummary
  rw [IncidenceEndpointSummary.atTag_retainedSideColor]
  simp only [horizontalAssembledRetainedIncidenceSideColor, horizontalIncidenceEndpoints]

/-- The finite-state pass over all canonical incidence words emits their
complete endpoint summaries in exactly the original incidence-tag order. -/
theorem incidenceEndpointSummary_directionOutput_horizontal (source : PeriodicCNF Nat) :
    IncidenceEndpointSummary.directionOutput
      (FiniteAlphabetDelimitedBlockJoin.blocks
        ((horizontalThreeDMProblemComputed source).incidenceTags.map
          (fun tag => (horizontalCanonicalIncidenceDirectionBlock source tag).directions))) =
      (horizontalThreeDMProblemComputed source).incidenceTags.map
        (horizontalIncidenceEndpointSummary source) := by
  rw [IncidenceEndpointSummary.directionOutput_blocks, List.map_map]
  have endpointsEq :
      (horizontalThreeDMProblemComputed source).incidenceTags.map
        (fun tag => ((horizontalCanonicalIncidenceDirectionBlock source tag).directions.headD .invalid,
          (horizontalCanonicalIncidenceDirectionBlock source tag).directions.getLastD .invalid)) =
      (horizontalThreeDMProblemComputed source).incidenceTags.map (horizontalIncidenceEndpoints source) := by
    apply List.map_congr_left
    intro tag member
    exact horizontalCanonicalIncidenceDirectionBlock_endpoints source tag member
  simp only [Function.comp_def]
  rw [endpointsEq, IncidenceEndpointSummary.output_incidenceTags]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Explicit finite-state endpoint extraction from the verified source
incidence-word compiler. -/
def directSourceFinalIncidenceEndpointSummaries (symbols : List encoding.Γ) :
    List IncidenceEndpointSummary.Summary :=
  IncidenceEndpointSummary.directionOutput
    (directSourceFinalCanonicalIncidenceDirectionTokens decider symbols)

noncomputable def directSourceFinalIncidenceEndpointSummariesComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalIncidenceEndpointSummaries decider) := by
  unfold directSourceFinalIncidenceEndpointSummaries
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalIncidenceDirectionTokensComputableInPolyTime decider)
    IncidenceEndpointSummary.directionOutputComputableInPolyTime

/-- Every emitted finite record agrees with its actual horizontal incidence,
including the full RGB fan needed for header construction. -/
theorem directSourceFinalIncidenceEndpointSummaries_eq_horizontal (symbols : List encoding.Γ) :
    directSourceFinalIncidenceEndpointSummaries decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
        (horizontalIncidenceEndpointSummary
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  unfold directSourceFinalIncidenceEndpointSummaries
  rw [directSourceFinalCanonicalIncidenceDirectionTokens_eq_horizontal,
    incidenceEndpointSummary_directionOutput_horizontal]

end LeanTrominoes.PeriodicCNFStripReduction

end
