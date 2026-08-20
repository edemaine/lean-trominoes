/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionBlocks

/-! # Alignment of horizontal variable-triple prefix lengths -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- The length of the variable-triple enumeration is independent of the
chosen decision procedure for variable equality. -/
theorem variableTriples_length_decidableEq_irrel
    {Variable : Type} (first second : DecidableEq Variable)
    (source : PeriodicCNF Variable) :
    (@PeriodicPlanarOneInThreeToThreeDM.variableTriples
        Variable first source).length =
      (@PeriodicPlanarOneInThreeToThreeDM.variableTriples
        Variable second source).length := by
  have instanceEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- The variable position prefix is the pointwise position map of the same
typed variable prefix used by stable triple lookup. -/
theorem horizontalThreeDMVariableTriplePositionsComputed_eq_map_typed
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVariableTriplePositionsComputed source =
      (horizontalThreeDMVariableTriplesComputed source).map
        (horizontalThreeDMTriplePositionComputed source) := by
  have decidableEqCoherence :
      horizontalThreeDMTripleVariableDecidableEq =
        horizontalRibbonRoutedVariableDecidableEq :=
    Subsingleton.elim _ _
  unfold horizontalThreeDMVariableTriplePositionsComputed
    horizontalThreeDMVariableTriplesComputed
  exact congrArg
    (fun decEq : DecidableEq RoutedVariable =>
      (@PeriodicPlanarOneInThreeToThreeDM.variableTriples
          RoutedVariable decEq
          (horizontalNormalizedRoutedFormulaComputed source).erase).map
        (horizontalThreeDMTriplePositionComputed source))
    decidableEqCoherence

/-- Mapping the variable typed triples to their positions preserves the
length of the variable prefix. -/
@[simp] theorem horizontalThreeDMVariableTriplePositionsComputed_length
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMVariableTriplePositionsComputed source).length =
      (horizontalThreeDMVariableTriplesComputed source).length := by
  unfold horizontalThreeDMVariableTriplePositionsComputed
    horizontalThreeDMVariableTriplesComputed
  rw [List.length_map]
  apply variableTriples_length_decidableEq_irrel

end PeriodicCNFStripReduction
end LeanTrominoes
