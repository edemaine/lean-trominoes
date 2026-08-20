/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableCellTypeTable
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableTripleLookup

/-! # Variable-table cell types at executable stable indices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- A tagged ordinary variable-prefix triple has its finite-table cell type
at the advertised executable index. -/
theorem horizontalFinalOrdinaryVariableTripleCellTypeAtComputed_eq_table
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : PlanarThreeDM.VariableOccurrenceVariant)
    (localTriple : PlanarThreeDM.VariableOccurrenceTriple)
    (member :
      ((Triple.ordinary atom slot variant localTriple), tripleIndex) ∈
        (horizontalThreeDMVariableTriplesComputed source).zipIdx) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalVariableTripleCellTypeComputed source atom
        (.ordinary atom slot variant localTriple) := by
  exact horizontalFinalOrdinaryVariableTripleCellTypeComputed_eq_table
    source tripleIndex atom slot variant localTriple
    (horizontalThreeDMVariableTriple_indexLt
      source (.ordinary atom slot variant localTriple) tripleIndex member)
    (horizontalThreeDMVariableTriple_getElem?
      source (.ordinary atom slot variant localTriple) tripleIndex member)

/-- A tagged fixed-red variable-prefix triple has its finite-table cell type
at the advertised executable index. -/
theorem horizontalFinalFixedRedVariableTripleCellTypeAtComputed_eq_table
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : PlanarThreeDM.FixedRedConnectorTriple)
    (member :
      ((Triple.fixedRed atom slot localTriple), tripleIndex) ∈
        (horizontalThreeDMVariableTriplesComputed source).zipIdx) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalVariableTripleCellTypeComputed source atom
        (.fixedRed atom slot localTriple) := by
  exact horizontalFinalFixedRedVariableTripleCellTypeComputed_eq_table
    source tripleIndex atom slot localTriple
    (horizontalThreeDMVariableTriple_indexLt
      source (.fixedRed atom slot localTriple) tripleIndex member)
    (horizontalThreeDMVariableTriple_getElem?
      source (.fixedRed atom slot localTriple) tripleIndex member)

end PeriodicCNFStripReduction
end LeanTrominoes
