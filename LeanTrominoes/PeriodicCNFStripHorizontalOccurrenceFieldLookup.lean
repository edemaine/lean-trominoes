/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListFilteredRankLookup
import LeanTrominoes.PeriodicCNFStripHorizontalPresentedOccurrenceFields
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-! # Variable-slot lookup selects the same presented occurrence fields -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM (connectorKindOfLiteralIndex)
open PeriodicOneInThreeToThreeDM PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The complete finite field tuple at a tagged source incidence. -/
def taggedPresentedOccurrenceFields {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (tagged : TaggedOccurrence Variable) :
    (VariableConnectorKind × Bool) × AxisDirection :=
  ((connectorKindOfLiteralIndex tagged.2.2, tagged.1.value),
    ((unitSubdivisionDirections (routes tagged.2.1 tagged.2.2)).getLastD .invalid).opposite)

/-- The clause-major field stream is the field projection of the actual
clause/literal-tagged source list used by variable-slot lookup. -/
theorem presentedOccurrenceFields_eq_taggedLiterals {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    presentedOccurrenceFields source routes =
      (PeriodicThreeSATThree.taggedLiterals source.erase).map (taggedPresentedOccurrenceFields routes) := by
  simp only [presentedOccurrenceFields, PeriodicThreeSATThree.taggedLiterals,
    PositionedPeriodicCNF.erase, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
    taggedPresentedOccurrenceFields]

/-- A genuine variable-slot lookup recovers its complete field tuple at the
same global presentation index selected from the atom column. -/
theorem presentedOccurrenceFields_getD_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) (slot : OccurrenceSlot) (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source.erase atom slot = some tagged)
    (fallback : (VariableConnectorKind × Bool) × AxisDirection) :
    (presentedOccurrenceFields source routes).getD
        ((source.erase.variableOccurrences.idxsOf atom).getD slot.index 0) fallback =
      taggedPresentedOccurrenceFields routes tagged := by
  have filteredLookup : (occurrencesOf source.erase atom)[slot.index]? = some tagged := lookup
  have rankLt := (List.getElem?_eq_some_iff.mp filteredLookup).1
  have selected := List.filter_map_getD_eq_atomIndices_getD
    (PeriodicThreeSATThree.taggedLiterals source.erase) (fun item => item.1.atom) atom
    (taggedPresentedOccurrenceFields routes) fallback slot.index rankLt
  rw [taggedLiterals_atoms, ← presentedOccurrenceFields_eq_taggedLiterals] at selected
  rw [← selected]
  change ((occurrencesOf source.erase atom).map (taggedPresentedOccurrenceFields routes)).getD slot.index fallback = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, filteredLookup,
    Option.map_some, Option.getD_some]

end LeanTrominoes.PeriodicCNFStripReduction
