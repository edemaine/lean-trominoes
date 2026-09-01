/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderData

/-! # Finite occurrence data carried by routed Figure 9 headers -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

open Gadget PlanarThreeDM
open PeriodicCNF.ClauseProfilePolarityNormalization
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing

/-- Literal position occupied by one polarity-normalized output occurrence.
The main normalized clause preserves the selected source slot, while the two
positions of a complement clause are fixed. -/
def outputLiteralIndex (header : Header) : Nat :=
  match header.polarity.operation with
  | .compatible | .incompatible =>
      sourceSlotNat header.polarity.sourceSlot
  | .complementFresh => 0
  | .complementOriginal => 1

/-- Connector kind of the final occurrence selected by a routed header. -/
def outputConnectorKind (header : Header) : VariableConnectorKind :=
  PeriodicPlanarOneInThreeToThreeDM.connectorKindOfLiteralIndex
    (outputLiteralIndex header)

/-- Literal polarity of the final occurrence selected by a routed header. -/
def outputPolarity (header : Header) : Bool :=
  normalizedPolarity (outputLiteralIndex header)

/-- First source direction determined by the finite route header alone. -/
def outputFirstDirection (header : Header) : AxisDirection :=
  ((block header []).directions
    RetainedFigureNineRouteDirectionBlock.directions).headD .invalid

/-- The finite local occurrence fields needed to assemble a variable fan. -/
structure OccurrenceData where
  kind : VariableConnectorKind
  polarity : Bool
  direction : AxisDirection
  deriving DecidableEq, Fintype

instance : Inhabited OccurrenceData :=
  ⟨⟨.fixedRed, false, .invalid⟩⟩

/-- Project all finite local occurrence fields from one routed header. -/
def occurrenceData (header : Header) : OccurrenceData where
  kind := outputConnectorKind header
  polarity := outputPolarity header
  direction := outputFirstDirection header

@[simp] theorem occurrenceData_kind (header : Header) :
    (occurrenceData header).kind = outputConnectorKind header :=
  rfl

@[simp] theorem occurrenceData_polarity (header : Header) :
    (occurrenceData header).polarity = outputPolarity header :=
  rfl

@[simp] theorem occurrenceData_direction (header : Header) :
    (occurrenceData header).direction = outputFirstDirection header :=
  rfl

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes
