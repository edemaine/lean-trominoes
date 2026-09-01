/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceFrameDecoder
import LeanTrominoes.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestData

/-! # Colored endpoint frames for direct final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalOccurrenceEndpointFrame

open Computability Turing
open Gadget PeriodicThreeDM PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

abbrev Header :=
  PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header

/-- The finite data surrounding one colored routed occurrence word.  The
retained header identifies the dynamic route block that will be inserted
between the two endpoint queries. -/
structure Data where
  color : WireColor
  header : Header
  leading : HorizontalFiniteIncidenceDirectionQuery
  lane : WireColor
  trailing : HorizontalFiniteIncidenceDirectionQuery
  deriving DecidableEq, Fintype

instance : Inhabited Data :=
  ⟨⟨.red, default, default, .red, default⟩⟩

/-- Specialize one complete occurrence frame to one incidence color. -/
def ofColor (frame : DirectFinalOccurrenceFrame.Data)
    (color : WireColor) : Data :=
  let lane := clauseRibbonLaneForColor frame.clauseFrame.group color
  { color
    header := frame.clauseFrame.header
    leading := .variableStub frame.variableFan
      (occurrenceVariableSiteSlot frame.occurrenceSlot) color
    lane
    trailing := .clauseStub frame.clauseFrame.clauseFan
      frame.clauseFrame.group lane }

/-- The red, green, and blue endpoint frames belonging to one occurrence. -/
def frameBlock (frame : DirectFinalOccurrenceFrame.Data) : List Data :=
  incidenceColors.map (ofColor frame)

/-- Expand every complete occurrence frame to its three colored endpoint
frames while preserving occurrence-major, color-minor order. -/
def output (frames : List DirectFinalOccurrenceFrame.Data) : List Data :=
  frames.flatMap frameBlock

/-- Surround one completed routed source block by this colored endpoint
frame, in the input format consumed by the existing occurrence compiler. -/
def routedTokens (frame : Data)
    (route : HorizontalRoutedRouteDirectionBlock) :
    List HorizontalOccurrenceRoutedRequest.Token :=
  HorizontalOccurrenceRoutedRequest.tokens
    frame.leading frame.lane route frame.trailing

@[simp] theorem ofColor_color (frame : DirectFinalOccurrenceFrame.Data)
    (color : WireColor) :
    (ofColor frame color).color = color :=
  rfl

@[simp] theorem ofColor_header (frame : DirectFinalOccurrenceFrame.Data)
    (color : WireColor) :
    (ofColor frame color).header = frame.clauseFrame.header :=
  rfl

@[simp] theorem ofColor_leading (frame : DirectFinalOccurrenceFrame.Data)
    (color : WireColor) :
    (ofColor frame color).leading =
      .variableStub frame.variableFan
        (occurrenceVariableSiteSlot frame.occurrenceSlot) color :=
  rfl

@[simp] theorem ofColor_lane (frame : DirectFinalOccurrenceFrame.Data)
    (color : WireColor) :
    (ofColor frame color).lane =
      clauseRibbonLaneForColor frame.clauseFrame.group color :=
  rfl

@[simp] theorem ofColor_trailing
    (frame : DirectFinalOccurrenceFrame.Data) (color : WireColor) :
    (ofColor frame color).trailing =
      .clauseStub frame.clauseFrame.clauseFan frame.clauseFrame.group
        (clauseRibbonLaneForColor frame.clauseFrame.group color) :=
  rfl

@[simp] theorem frameBlock_map_color
    (frame : DirectFinalOccurrenceFrame.Data) :
    (frameBlock frame).map Data.color = incidenceColors := by
  unfold frameBlock
  rw [List.map_map]
  change incidenceColors.map id = incidenceColors
  exact List.map_id incidenceColors

@[simp] theorem frameBlock_length
    (frame : DirectFinalOccurrenceFrame.Data) :
    (frameBlock frame).length = 3 := by
  simp [frameBlock, incidenceColors]

@[simp] theorem output_length
    (frames : List DirectFinalOccurrenceFrame.Data) :
    (output frames).length = 3 * frames.length := by
  unfold output
  induction frames with
  | nil => rfl
  | cons frame frames induction =>
      rw [List.flatMap_cons, List.length_append, frameBlock_length,
        induction, List.length_cons]
      omega

/-- Colored endpoint-frame expansion is a fixed finite block transduction. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime frameBlock

end DirectFinalOccurrenceEndpointFrame
end LeanTrominoes.PeriodicCNFStripReduction

end
