/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripPacked
import LeanTrominoes.IndexedSavitchDFSCorrectness
import LeanTrominoes.IndexedSavitchDFSListEncoding
import LeanTrominoes.Theorem55StripDeciderSize

/-! # Enumeration-free variable-tile strip search and its serialized stack bound -/

namespace LeanTrominoes.PolyominoStripWindow

def indexedTilingCheck (tiles : Bool → Polyomino) (height bound : Nat) : Bool :=
  FiniteState.cycleSearchIndexDFSBoolAtDepth (2 ^ stateBits Bool height bound)
    (stateBits Bool height bound) (fun a b => decide (packedTransition tiles height bound a b))

theorem indexedTilingCheck_correct (tiles : Bool → Polyomino) (height bound : Nat)
    (bounded : Bounded tiles bound) :
    indexedTilingCheck tiles height bound = true ↔ Tileable tiles (horizontalStrip height) := by
  rw [indexedTilingCheck,FiniteState.cycleSearchIndexDFSBoolAtDepth_eq]
  have search := FiniteState.cycleSearchIndexBoolAtDepth_eq_true_iff
    (2 ^ stateBits Bool height bound) (stateBits Bool height bound)
    (fun a b => decide (packedTransition tiles height bound a b)) (by rfl)
  have cycles := (packed_cycle_iff tiles height bound).trans (tileable_iff_cycle bounded).symm
  have relation_eq : FiniteState.IndexedRelation (2 ^ stateBits Bool height bound)
      (fun a b => decide (packedTransition tiles height bound a b)) =
      (fun a b : IndexedState height bound => packedTransition tiles height bound a.val b.val) := by
    funext a b
    apply propext
    change decide (packedTransition tiles height bound a.val b.val) = true ↔ _
    simp
  rw [relation_eq] at search
  exact search.trans cycles

end LeanTrominoes.PolyominoStripWindow

namespace LeanTrominoes.Theorem55StripDecider

def decideStripIndexed (input : Theorem55.StripInput) : Bool :=
  decide (0 < input.1) && decide (input.2 ≠ []) &&
    decide (PolyominoConnectivitySearch.Disconnected input.2) &&
      PolyominoStripWindow.indexedTilingCheck (pairTiles PlusRefinement.bumpy input.2.toFinset) input.1 (bound input)

theorem decideStripIndexed_correct (input : Theorem55.StripInput) :
    decideStripIndexed input = true ↔ Theorem55.stripProblem input := by
  rw [decideStripIndexed]
  simp only [Bool.and_eq_true,decide_eq_true_eq,
    PolyominoStripWindow.indexedTilingCheck_correct _ _ _ (tiles_bounded input)]
  by_cases nonempty : input.2 = []
  · simp [nonempty,Theorem55.stripProblem]
  · rw [PolyominoConnectivitySearch.disconnected_iff _ nonempty]
    simp [Theorem55.stripProblem,nonempty,and_assoc]

noncomputable def driverSpacePolynomial : Polynomial Nat :=
  3 * (statePolynomial+2) + statePolynomial * (4*(statePolynomial+2)+5) + 3

/-- Every serialized DFS stack has polynomial size, independently of how long
search runs. Transition evaluation and the surrounding machine still need separate certificates. -/
theorem dfs_encoded_space_le (input : Theorem55.StripInput) (first last steps : Nat)
    (relation : Nat → Nat → Bool)
    (firstBelow : first < 2 ^ PolyominoStripWindow.stateBits Bool input.1 (bound input))
    (lastBelow : last < 2 ^ PolyominoStripWindow.stateBits Bool input.1 (bound input)) :
    Turing.PartrecToTM2.encodedListSpace
      (((FiniteState.divideEvalStep (2 ^ PolyominoStripWindow.stateBits Bool input.1 (bound input)) relation)^[steps]
        (FiniteState.divideEvalInitial (PolyominoStripWindow.stateBits Bool input.1 (bound input)) first last)).toNatList) ≤
      driverSpacePolynomial.eval (Theorem55StripEncoding.finEncoding.encode input).length := by
  let bits := PolyominoStripWindow.stateBits Bool input.1 (bound input)
  have depth : bits < 2^(bits+1) := bits.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have generic := FiniteState.divideEvalIterate_encodedListSpace_le
    (2^bits) bits (bits+1) first last steps relation firstBelow lastBelow
    (Nat.pow_le_pow_right (by omega) (by omega)) depth
  apply generic.trans
  simp only [driverSpacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  have bound := stateBits_le input
  change bits ≤ _ at bound
  nlinarith

end LeanTrominoes.Theorem55StripDecider
