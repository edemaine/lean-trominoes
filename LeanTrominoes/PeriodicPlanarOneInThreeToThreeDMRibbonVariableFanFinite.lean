/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFans

/-!
# Finite variable-side ribbon fan configurations

At one exact-one variable vertex there are one, two, or three occurrence
slots.  The local 3DM site geometry depends only on the connector kind and
polarity in those slots, while the source embedding contributes one distinct
genuine cardinal direction per active slot.  This file erases the ambient
periodic formula from that data and packages the resulting finite local
configuration.

The finite model is used to test and ultimately certify a coordinated family
of RGB endpoint stubs inside one ribbon macrocell.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- All finite data that controls the variable-side fan at one source
variable.  `countPred` represents one, two, or three active slots. -/
structure VariableRibbonFanData where
  countPred : Fin 3
  kind : VariableSiteSlot → VariableConnectorKind
  polarity : VariableSiteSlot → Bool
  direction : VariableSiteSlot → AxisDirection
  deriving DecidableEq, Fintype

namespace VariableRibbonFanData

/-- Number of active occurrence slots. -/
def count (data : VariableRibbonFanData) : Nat :=
  data.countPred + 1

/-- Whether a finite variable-site slot is active. -/
def SlotActive
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot) : Prop :=
  slot.index < data.count

instance (data : VariableRibbonFanData)
    (slot : VariableSiteSlot) :
    Decidable (data.SlotActive slot) := by
  unfold SlotActive
  infer_instance

/-- The source directions of active slots are genuine and pairwise
distinct. -/
def IsValid (data : VariableRibbonFanData) : Prop :=
  (∀ slot, data.SlotActive slot →
      (data.direction slot).IsGenuine) ∧
    ∀ firstSlot secondSlot,
      data.SlotActive firstSlot →
      data.SlotActive secondSlot →
      firstSlot ≠ secondSlot →
      data.direction firstSlot ≠ data.direction secondSlot

instance (data : VariableRibbonFanData) :
    Decidable data.IsValid := by
  unfold IsValid
  infer_instance

/-- The local variable-site triple carrying the strand of the selected
color for one connector kind. -/
def routedTriple
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (color : WireColor) :
    VariableSiteTriple :=
  match data.kind slot, color with
  | .fixedRed, .red =>
      .fixedRed slot .bottomRight
  | .fixedRed, .green
  | .fixedRed, .blue =>
      .fixedRed slot .auxiliary
  | .fixedGreen, .blue =>
      .ordinary slot .fixedGreen .first
  | .fixedGreen, .red
  | .fixedGreen, .green =>
      .ordinary slot .fixedGreen .auxiliary
  | .fixedBlue, .blue =>
      .ordinary slot .fixedBlue .first
  | .fixedBlue, .red
  | .fixedBlue, .green =>
      .ordinary slot .fixedBlue .auxiliary

/-- A routed triple in an active slot belongs to the selected local
variable-site drawing. -/
theorem routedTriple_matches
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (data.routedTriple slot color).MatchesKind
      data.count data.kind := by
  unfold SlotActive at active
  cases kindEq : data.kind slot <;>
    cases color <;>
    simp [routedTriple, VariableSiteTriple.MatchesKind,
      kindEq, active]

/-- Routed triple as an active element of the selected finite site. -/
def activeRoutedTriple
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    ActiveVariableSiteTriple data.count data.kind :=
  ⟨data.routedTriple slot color,
    data.routedTriple_matches slot active color⟩

/-- Exact local RGB port selected by one finite configuration. -/
def port
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) : Cell :=
  let drawing :=
    variableSiteDrawing data.count data.kind data.polarity
  Cell.add standardThreeStrandLayout.variableOffset
    (drawing.elementPosition
      (drawing.reference
        (data.activeRoutedTriple slot active color) color))

/-- The existing independent one-bend variable stub in local macrocell
coordinates. -/
def independentRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) : List Cell :=
  standardVariableRibbonFan
    (data.port slot active color)
    (data.direction slot)
    color

/-- The smallest finite configuration exposing a crossing in the old
independent fan construction: one fixed-red occurrence whose source route
leaves to the east. -/
def oneFixedRedEast : VariableRibbonFanData where
  countPred := 0
  kind := fun _ => .fixedRed
  polarity := fun _ => false
  direction := fun _ => .east

/-- The counterexample satisfies all genuine, distinct active-direction
requirements (there is only one active occurrence). -/
theorem oneFixedRedEast_isValid :
    oneFixedRedEast.IsValid := by
  native_decide

/-- Even at one occurrence, choosing the three colored elbows independently
does not give a separated fan.  The green horizontal segment and the blue
vertical segment cross at `(26, 20)`. -/
theorem oneFixedRedEast_green_blue_not_separated :
    let active : oneFixedRedEast.SlotActive .first := by decide
    ¬RoutesStrictlyAvoidEachOther
      (oneFixedRedEast.independentRoute
        .first active .green)
      (oneFixedRedEast.independentRoute
        .first active .blue) := by
  native_decide

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
