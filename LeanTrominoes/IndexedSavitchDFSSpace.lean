/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedSavitchDFS
import LeanTrominoes.EncodingLengthComputability

/-!
# Flat storage bounds for depth-first Savitch configurations

The standard `Primcodable (List α)` natural encoding is useful for
computability, but it is not the intended machine representation of the DFS
continuation stack.  A space-bounded implementation stores one frame after
another.  This file defines that flat storage measure and proves its two
structural ingredients: every stored graph index stays below `stateCount`,
and at most one frame is stored per Savitch level.
-/

open Computability

namespace LeanTrominoes.FiniteState

/-- All graph indices in a query are in range. -/
def DivideQuery.IndicesBelow
    (stateCount : Nat) (query : DivideQuery) : Prop :=
  query.first < stateCount ∧ query.last < stateCount

/-- All graph indices saved in one continuation frame are in range. -/
def DivideFrame.IndicesBelow
    (stateCount : Nat) (frame : DivideFrame) : Prop :=
  frame.first < stateCount ∧ frame.last < stateCount ∧
    frame.middle < stateCount

/-- Every saved continuation frame has in-range graph indices. -/
def DivideStackIndicesBelow
    (stateCount : Nat) : List DivideFrame → Prop
  | [] => True
  | frame :: rest =>
      frame.IndicesBelow stateCount ∧
        DivideStackIndicesBelow stateCount rest

/-- The current query and all continuations have in-range graph indices. -/
def DivideEvalState.IndicesBelow
    (stateCount : Nat) (state : DivideEvalState) : Prop :=
  state.query.IndicesBelow stateCount ∧
    DivideStackIndicesBelow stateCount state.stack

theorem divideEvalInitial_indicesBelow
    (stateCount depth first last : Nat)
    (firstBelow : first < stateCount)
    (lastBelow : last < stateCount) :
    (divideEvalInitial depth first last).IndicesBelow stateCount := by
  exact ⟨⟨firstBelow, lastBelow⟩, trivial⟩

theorem divideEvalStep_indicesBelow
    (stateCount : Nat) (relation : Nat → Nat → Bool)
    (state : DivideEvalState)
    (bounded : state.IndicesBelow stateCount) :
    (divideEvalStep stateCount relation state).IndicesBelow
      stateCount := by
  rcases bounded with ⟨queryBounded, stackBounded⟩
  rcases queryBounded with ⟨firstBelow, lastBelow⟩
  cases answer : state.answer with
  | none =>
      cases depth : state.query.depth with
      | zero =>
          simpa [divideEvalStep, DivideEvalState.IndicesBelow,
            DivideQuery.IndicesBelow, answer, depth] using
              And.intro (And.intro firstBelow lastBelow) stackBounded
      | succ depth =>
          cases count : stateCount with
          | zero =>
              simpa [divideEvalStep, DivideEvalState.IndicesBelow,
                DivideQuery.IndicesBelow, answer, depth, count] using
                  And.intro (And.intro firstBelow lastBelow) stackBounded
          | succ middle =>
              have middleBelow : middle < Nat.succ middle :=
                Nat.lt_succ_self middle
              simpa [divideEvalStep, answer, depth, count,
                DivideEvalState.IndicesBelow, DivideQuery.IndicesBelow,
                DivideStackIndicesBelow, DivideFrame.IndicesBelow] using
                  And.intro (And.intro firstBelow middleBelow)
                    (And.intro
                      (And.intro firstBelow
                        (And.intro lastBelow middleBelow))
                      stackBounded)
  | some returned =>
      cases stack : state.stack with
      | nil =>
          simpa [divideEvalStep, DivideEvalState.IndicesBelow,
            DivideQuery.IndicesBelow, answer, stack] using
              And.intro (And.intro firstBelow lastBelow) stackBounded
      | cons frame rest =>
          simp only [stack, DivideStackIndicesBelow] at stackBounded
          rcases stackBounded with ⟨frameBounded, restBounded⟩
          rcases frameBounded with
            ⟨frameFirstBelow, frameLastBelow, middleBelow⟩
          cases leftAnswer : frame.leftAnswer with
          | none =>
              simp only [divideEvalStep, answer, stack, leftAnswer,
                DivideEvalState.IndicesBelow,
                DivideQuery.IndicesBelow, DivideStackIndicesBelow,
                DivideFrame.IndicesBelow]
              exact ⟨⟨middleBelow, frameLastBelow⟩,
                ⟨⟨frameFirstBelow, frameLastBelow, middleBelow⟩,
                  restBounded⟩⟩
          | some left =>
              cases middleEq : frame.middle with
              | zero =>
                  simp only [divideEvalStep, answer, stack, leftAnswer,
                    middleEq, DivideEvalState.IndicesBelow]
                  exact ⟨⟨firstBelow, lastBelow⟩, restBounded⟩
              | succ previousMiddle =>
                  simp only [divideEvalStep, answer, stack, leftAnswer,
                    middleEq, DivideEvalState.IndicesBelow,
                    DivideQuery.IndicesBelow, DivideStackIndicesBelow,
                    DivideFrame.IndicesBelow]
                  have nextMiddleBelow :
                      previousMiddle < stateCount := by omega
                  exact ⟨⟨frameFirstBelow, nextMiddleBelow⟩,
                    ⟨⟨frameFirstBelow, frameLastBelow, nextMiddleBelow⟩,
                      restBounded⟩⟩

theorem divideEvalIterate_indicesBelow
    (stateCount steps : Nat) (relation : Nat → Nat → Bool)
    (state : DivideEvalState)
    (bounded : state.IndicesBelow stateCount) :
    ((divideEvalStep stateCount relation)^[steps] state).IndicesBelow
      stateCount := by
  induction steps generalizing state with
  | zero => exact bounded
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      exact divideEvalStep_indicesBelow stateCount relation _
        (induction state bounded)

theorem divideEvalIterate_initial_indicesBelow
    (stateCount depth first last steps : Nat)
    (relation : Nat → Nat → Bool)
    (firstBelow : first < stateCount)
    (lastBelow : last < stateCount) :
    ((divideEvalStep stateCount relation)^[steps]
      (divideEvalInitial depth first last)).IndicesBelow stateCount :=
  divideEvalIterate_indicesBelow stateCount steps relation _
    (divideEvalInitial_indicesBelow stateCount depth first last
      firstBelow lastBelow)

/-- Binary natural length is bounded by any exponent whose power of two is
strictly above the number. -/
theorem encodeNat_length_le_of_lt_pow
    (number bits : Nat) (bounded : number < 2 ^ bits) :
    (encodeNat number).length ≤ bits := by
  induction bits generalizing number with
  | zero =>
      have : number = 0 := by simpa using bounded
      subst number
      rfl
  | succ bits induction =>
      by_cases zero : number = 0
      · subst number
        simp [encodeNat, encodeNum]
      · rw [LeanTrominoes.Computability.encodeNat_cons
          number (Nat.pos_of_ne_zero zero)]
        simp only [List.length_cons]
        apply Nat.succ_le_succ
        apply induction
        rw [Nat.div2_val]
        rw [pow_succ] at bounded
        omega

/-- Flat cells used by one natural-number field: its binary digits plus a
delimiter. -/
def natFlatSpace (number : Nat) : Nat :=
  (encodeNat number).length + 1

/-- Flat storage occupied by one current query. -/
def DivideQuery.flatSpace (query : DivideQuery) : Nat :=
  natFlatSpace query.depth +
    natFlatSpace query.first +
    natFlatSpace query.last

/-- Flat storage occupied by one continuation frame.  The final three cells
store the accumulated Boolean and the three-way optional-left-answer tag. -/
def DivideFrame.flatSpace (frame : DivideFrame) : Nat :=
  natFlatSpace frame.depth +
    natFlatSpace frame.first +
    natFlatSpace frame.last +
    natFlatSpace frame.middle + 3

/-- Flat storage occupied by a complete DFS configuration. -/
def DivideEvalState.flatSpace (state : DivideEvalState) : Nat :=
  state.query.flatSpace +
    (state.stack.map DivideFrame.flatSpace).sum + 2

theorem query_flatSpace_le
    (stateCount rootDepth bits : Nat) (query : DivideQuery)
    (indices : query.IndicesBelow stateCount)
    (depthBound : query.depth ≤ rootDepth)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    query.flatSpace ≤ 3 * (bits + 1) := by
  have depthBits : (encodeNat query.depth).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (depthBound.trans_lt rootDepthBound)
  have firstBits : (encodeNat query.first).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.1.trans_le stateCountBound)
  have lastBits : (encodeNat query.last).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.2.trans_le stateCountBound)
  simp only [DivideQuery.flatSpace, natFlatSpace]
  omega

theorem frame_flatSpace_le
    (stateCount rootDepth bits : Nat) (frame : DivideFrame)
    (indices : frame.IndicesBelow stateCount)
    (depthBound : frame.depth ≤ rootDepth)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    frame.flatSpace ≤ 4 * (bits + 1) + 3 := by
  have depthBits : (encodeNat frame.depth).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (depthBound.trans_lt rootDepthBound)
  have firstBits : (encodeNat frame.first).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.1.trans_le stateCountBound)
  have lastBits : (encodeNat frame.last).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.2.1.trans_le stateCountBound)
  have middleBits : (encodeNat frame.middle).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.2.2.trans_le stateCountBound)
  simp only [DivideFrame.flatSpace, natFlatSpace]
  omega

theorem stack_flatSpace_le
    (stateCount rootDepth bits : Nat) (stack : List DivideFrame)
    (indices : DivideStackIndicesBelow stateCount stack)
    (fits : DivideStackFits rootDepth stack)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    (stack.map DivideFrame.flatSpace).sum ≤
      stack.length * (4 * (bits + 1) + 3) := by
  induction stack with
  | nil => simp
  | cons frame rest induction =>
      simp only [DivideStackIndicesBelow] at indices
      simp only [DivideStackFits] at fits
      rcases indices with ⟨frameIndices, restIndices⟩
      rcases fits with ⟨frameFits, restFits⟩
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have frameDepth : frame.depth ≤ rootDepth := by omega
      have frameSpace := frame_flatSpace_le
        stateCount rootDepth bits frame frameIndices frameDepth
        stateCountBound rootDepthBound
      have restSpace := induction restIndices restFits
      calc
        frame.flatSpace + (List.map DivideFrame.flatSpace rest).sum ≤
            (4 * (bits + 1) + 3) +
              rest.length * (4 * (bits + 1) + 3) :=
          Nat.add_le_add frameSpace restSpace
        _ = (rest.length + 1) * (4 * (bits + 1) + 3) := by
          rw [Nat.add_mul]
          omega

theorem divideEvalState_flatSpace_le
    (stateCount rootDepth bits : Nat) (state : DivideEvalState)
    (indices : state.IndicesBelow stateCount)
    (fits : state.FitsDepth rootDepth)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    state.flatSpace ≤
      3 * (bits + 1) +
        rootDepth * (4 * (bits + 1) + 3) + 2 := by
  have querySpace := query_flatSpace_le
    stateCount rootDepth bits state.query indices.1
    ((Nat.le_add_right state.query.depth state.stack.length).trans fits.1)
    stateCountBound rootDepthBound
  have stackSpace := stack_flatSpace_le
    stateCount rootDepth bits state.stack indices.2 fits.2
    stateCountBound rootDepthBound
  have stackLength : state.stack.length ≤ rootDepth := by
    exact (Nat.le_add_left state.stack.length state.query.depth).trans
      fits.1
  have stackBudget :
      state.stack.length * (4 * (bits + 1) + 3) ≤
        rootDepth * (4 * (bits + 1) + 3) :=
    Nat.mul_le_mul_right (4 * (bits + 1) + 3) stackLength
  unfold DivideEvalState.flatSpace
  exact Nat.add_le_add_right
    (Nat.add_le_add querySpace (stackSpace.trans stackBudget)) 2

theorem divideEvalIterate_flatSpace_le
    (stateCount depth bits first last steps : Nat)
    (relation : Nat → Nat → Bool)
    (firstBelow : first < stateCount)
    (lastBelow : last < stateCount)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (depthBound : depth < 2 ^ bits) :
    (((divideEvalStep stateCount relation)^[steps]
      (divideEvalInitial depth first last)).flatSpace) ≤
      3 * (bits + 1) +
        depth * (4 * (bits + 1) + 3) + 2 := by
  apply divideEvalState_flatSpace_le
  · exact divideEvalIterate_initial_indicesBelow
      stateCount depth first last steps relation firstBelow lastBelow
  · exact divideEvalIterate_fitsDepth
      stateCount depth steps relation
      (divideEvalInitial depth first last)
      (divideEvalInitial_fitsDepth depth first last)
  · exact stateCountBound
  · exact depthBound

end LeanTrominoes.FiniteState
