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

abbrev PrefixDescriptor :=
  PeriodicCNF.FormulaShapeFigureNineRoutePrefix.Descriptor

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

/-- Recover the finite-template atom selected by one Figure 9 prefix.  The
codomain itself contains an unbounded clause-index field, but every value read
through this finite descriptor alphabet belongs to a fixed template. -/
def prefixAtom : PrefixDescriptor →
    PlanarOneInThreeNoUnitsFigureNine.FigureNineNoUnitsVariable
  | .local query =>
      ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        query.1).incidenceAt query.2).literal.1
  | .inherited _ query =>
      ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        query.1).incidenceAt query.2.1).literal.1

/-- Finite final-variable control relative to one parent source clause.  The
original branch compares the template atoms selected by its descriptors; the
fresh branch compares source-incidence descriptors themselves. -/
inductive AtomControl
  | original (sourceOccurrence : PrefixDescriptor)
  | fresh (sourceOccurrence : PrefixDescriptor)
  deriving DecidableEq, Fintype, Inhabited

/-- Parent-relative final variable control carried by one routed header. -/
def outputAtomControl (header : Header) : AtomControl :=
  match header.polarity.operation with
  | .compatible | .complementOriginal =>
      .original header.figurePrefix
  | .incompatible | .complementFresh =>
      .fresh header.figurePrefix

/-- Equality test for final variables generated inside the same parent source
clause.  Original variables compare their selected Figure 9 atoms; a fresh
variable is scoped to its exact pre-polarity source occurrence. -/
def AtomControl.sameAtom : AtomControl → AtomControl → Bool
  | .original first, .original second =>
      decide (prefixAtom first = prefixAtom second)
  | .fresh first, .fresh second => decide (first = second)
  | _, _ => false

/-- Finite occurrence fields. A header projection retains the stored first
direction; a completed record supplies the reversed route's variable direction. -/
structure OccurrenceData where
  atomControl : AtomControl
  kind : VariableConnectorKind
  polarity : Bool
  direction : AxisDirection
  deriving DecidableEq, Fintype

instance : Inhabited OccurrenceData :=
  ⟨⟨default, .fixedRed, false, .invalid⟩⟩

/-- Project the fields available before reading the dynamic route tail.
Variable fans use `completeOccurrenceData` after the tail is consumed. -/
def occurrenceData (header : Header) : OccurrenceData where
  atomControl := outputAtomControl header
  kind := outputConnectorKind header
  polarity := outputPolarity header
  direction := outputFirstDirection header

@[simp] theorem occurrenceData_atomControl (header : Header) :
    (occurrenceData header).atomControl = outputAtomControl header :=
  rfl

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
