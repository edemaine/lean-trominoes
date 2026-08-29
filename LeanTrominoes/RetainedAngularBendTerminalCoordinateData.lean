/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularBendTerminalCoordinateFamily
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors

/-! # Numeric coordinates of compiler-ordered bend terminal data -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Canonical terminal data of all untranslated bends, in numeric route and
within-route bend order. -/
def baseBendTerminalData
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List RetainedTerminalData :=
  (numericRouteDescriptors source).flatMap fun descriptor =>
    (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
      fun routeBend =>
        bendRouteTerminalDataBlock
          routeBend.incomingPort routeBend.outgoingPort

/-- Ordinary coordinate pairs of the compiler-ordered base-bend data. -/
def baseBendTerminalCoordinates
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List (Nat × Nat) :=
  List.map retainedTerminalDataCoordinate
    (baseBendTerminalData source)

/-- Regrouping the numeric-route scan by its flattened bend list does not
change the exact terminal-coordinate presentation. -/
theorem retainedBendTerminalCoordinates_baseRouteBends_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedBendTerminalCoordinates (baseRouteBends source) =
      baseBendTerminalCoordinates source := by
  unfold retainedBendTerminalCoordinates baseRouteBends
    baseBendTerminalCoordinates baseBendTerminalData
  rw [List.flatMap_assoc, List.map_flatMap]
  apply List.flatMap_congr
  intro descriptor descriptorMember
  rw [List.map_flatMap]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
