import LeanTrominoes.IndexedSavitchDFSSpace
import LeanTrominoes.PartrecPolySpace

/-!
# Flat natural-list encoding of Savitch DFS configurations

Mathlib's partial-recursive machine natively represents a `List Nat` by
writing each natural in binary followed by a delimiter.  This file serializes
the DFS continuation stack as six consecutive naturals per frame, rather than
pairing the whole stack into one potentially enormous natural.
-/

namespace LeanTrominoes.FiniteState

open Turing.PartrecToTM2

def divideBoolTag : Bool → Nat
  | false => 0
  | true => 1

def divideBoolOfTag (tag : Nat) : Bool :=
  tag != 0

@[simp]
theorem divideBoolOfTag_tag (value : Bool) :
    divideBoolOfTag (divideBoolTag value) = value := by
  cases value <;> rfl

def divideOptionBoolTag : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def divideOptionBoolOfTag : Nat → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

@[simp]
theorem divideOptionBoolOfTag_tag (value : Option Bool) :
    divideOptionBoolOfTag (divideOptionBoolTag value) = value := by
  rcases value with _ | value
  · rfl
  · cases value <;> rfl

/-- Six natural fields representing one continuation frame. -/
def DivideFrame.toNatList (frame : DivideFrame) : List Nat :=
  [frame.depth, frame.first, frame.last, frame.middle,
    divideBoolTag frame.accumulated,
    divideOptionBoolTag frame.leftAnswer]

/-- Parse one frame and return the unused suffix.  A short input receives a
default frame; this branch is irrelevant on serialized configurations. -/
def DivideFrame.ofNatList : List Nat → DivideFrame × List Nat
  | depth :: first :: last :: middle :: accumulated :: leftAnswer :: rest =>
      (⟨depth, first, last, middle, divideBoolOfTag accumulated,
        divideOptionBoolOfTag leftAnswer⟩, rest)
  | values => (⟨0, 0, 0, 0, false, none⟩, values)

@[simp]
theorem DivideFrame.ofNatList_toNatList_append
    (frame : DivideFrame) (rest : List Nat) :
    DivideFrame.ofNatList (frame.toNatList ++ rest) = (frame, rest) := by
  cases frame
  simp [DivideFrame.toNatList, DivideFrame.ofNatList]

/-- Frames serialized consecutively with fixed arity six. -/
def divideStackToNatList (stack : List DivideFrame) : List Nat :=
  stack.flatMap DivideFrame.toNatList

/-- Parse consecutive six-field frames, dropping a malformed final suffix. -/
def divideStackOfNatList : List Nat → List DivideFrame
  | depth :: first :: last :: middle :: accumulated :: leftAnswer :: rest =>
      ⟨depth, first, last, middle, divideBoolOfTag accumulated,
        divideOptionBoolOfTag leftAnswer⟩ :: divideStackOfNatList rest
  | _ => []

@[simp]
theorem divideStackOfNatList_toNatList (stack : List DivideFrame) :
    divideStackOfNatList (divideStackToNatList stack) = stack := by
  induction stack with
  | nil => rfl
  | cons frame rest induction =>
      rw [divideStackToNatList] at induction ⊢
      cases frame
      simp [DivideFrame.toNatList, divideStackOfNatList, induction]

/-- The answer tag, three query fields, and then the consecutive stack
frames. -/
def DivideEvalState.toNatList (state : DivideEvalState) : List Nat :=
  divideOptionBoolTag state.answer ::
    state.query.depth :: state.query.first :: state.query.last ::
      divideStackToNatList state.stack

/-- Total parser for the flat evaluator representation. -/
def DivideEvalState.ofNatList : List Nat → DivideEvalState
  | answer :: depth :: first :: last :: stack =>
      ⟨⟨depth, first, last⟩, divideStackOfNatList stack,
        divideOptionBoolOfTag answer⟩
  | _ => divideEvalInitial 0 0 0

@[simp]
theorem DivideEvalState.ofNatList_toNatList (state : DivideEvalState) :
    DivideEvalState.ofNatList state.toNatList = state := by
  cases state with
  | mk query stack answer =>
      cases query
      simp [DivideEvalState.toNatList, DivideEvalState.ofNatList]

/-- Native evaluator-tape space for one frame: four delimited binary naturals,
one Boolean tag, and one three-way optional-Boolean tag. -/
def DivideFrame.partrecFlatSpace (frame : DivideFrame) : Nat :=
  natFlatSpace frame.depth +
    natFlatSpace frame.first +
    natFlatSpace frame.last +
    natFlatSpace frame.middle + 5

/-- Native evaluator-tape space of a serialized DFS configuration. -/
def DivideEvalState.partrecFlatSpace (state : DivideEvalState) : Nat :=
  state.query.flatSpace +
    (state.stack.map DivideFrame.partrecFlatSpace).sum + 3

theorem encodedListSpace_divideFrame_toNatList_le
    (frame : DivideFrame) :
    encodedListSpace frame.toNatList ≤ frame.partrecFlatSpace := by
  have accumulatedSpace :
      (Computability.encodeNat
        (divideBoolTag frame.accumulated)).length + 1 ≤ 2 := by
    cases frame.accumulated <;>
      decide
  have leftAnswerSpace :
      (Computability.encodeNat
        (divideOptionBoolTag frame.leftAnswer)).length + 1 ≤ 3 := by
    rcases frame.leftAnswer with _ | value
    · decide
    · cases value <;> decide
  rw [DivideFrame.toNatList]
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  unfold DivideFrame.partrecFlatSpace natFlatSpace
  omega

theorem encodedListSpace_append (first rest : List Nat) :
    encodedListSpace (first ++ rest) =
      encodedListSpace first + encodedListSpace rest := by
  induction first with
  | nil => simp
  | cons value first induction =>
      simp only [List.cons_append, encodedListSpace_cons, induction]
      omega

theorem encodedListSpace_divideStackToNatList_le
    (stack : List DivideFrame) :
    encodedListSpace (divideStackToNatList stack) ≤
      (stack.map DivideFrame.partrecFlatSpace).sum := by
  induction stack with
  | nil => simp [divideStackToNatList]
  | cons frame rest induction =>
      rw [divideStackToNatList, List.flatMap_cons,
        encodedListSpace_append]
      exact Nat.add_le_add
        (encodedListSpace_divideFrame_toNatList_le frame) induction

theorem encodedListSpace_divideEvalState_toNatList_le
    (state : DivideEvalState) :
    encodedListSpace state.toNatList ≤ state.partrecFlatSpace := by
  have answerSpace :
      (Computability.encodeNat
        (divideOptionBoolTag state.answer)).length + 1 ≤ 3 := by
    rcases state.answer with _ | value
    · decide
    · cases value <;> decide
  have stackBound :=
    encodedListSpace_divideStackToNatList_le state.stack
  rw [DivideEvalState.toNatList]
  simp only [encodedListSpace_cons]
  unfold DivideEvalState.partrecFlatSpace DivideQuery.flatSpace
    natFlatSpace
  omega

theorem frame_partrecFlatSpace_le
    (stateCount rootDepth bits : Nat) (frame : DivideFrame)
    (indices : frame.IndicesBelow stateCount)
    (depthBound : frame.depth ≤ rootDepth)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    frame.partrecFlatSpace ≤ 4 * (bits + 1) + 5 := by
  have depthBits : (Computability.encodeNat frame.depth).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (depthBound.trans_lt rootDepthBound)
  have firstBits : (Computability.encodeNat frame.first).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.1.trans_le stateCountBound)
  have lastBits : (Computability.encodeNat frame.last).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.2.1.trans_le stateCountBound)
  have middleBits : (Computability.encodeNat frame.middle).length ≤ bits :=
    encodeNat_length_le_of_lt_pow _ _
      (indices.2.2.trans_le stateCountBound)
  simp only [DivideFrame.partrecFlatSpace, natFlatSpace]
  omega

theorem divideStack_partrecFlatSpace_le
    (stateCount rootDepth bits : Nat) (stack : List DivideFrame)
    (indices : DivideStackIndicesBelow stateCount stack)
    (fits : DivideStackFits rootDepth stack)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    (stack.map DivideFrame.partrecFlatSpace).sum ≤
      stack.length * (4 * (bits + 1) + 5) := by
  induction stack with
  | nil => simp
  | cons frame rest induction =>
      simp only [DivideStackIndicesBelow] at indices
      simp only [DivideStackFits] at fits
      rcases indices with ⟨frameIndices, restIndices⟩
      rcases fits with ⟨frameFits, restFits⟩
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have frameDepth : frame.depth ≤ rootDepth := by omega
      have frameSpace := frame_partrecFlatSpace_le
        stateCount rootDepth bits frame frameIndices frameDepth
        stateCountBound rootDepthBound
      have restSpace := induction restIndices restFits
      calc
        frame.partrecFlatSpace +
            (List.map DivideFrame.partrecFlatSpace rest).sum ≤
            (4 * (bits + 1) + 5) +
              rest.length * (4 * (bits + 1) + 5) :=
          Nat.add_le_add frameSpace restSpace
        _ = (rest.length + 1) * (4 * (bits + 1) + 5) := by
          rw [Nat.add_mul]
          omega

theorem divideEvalState_partrecFlatSpace_le
    (stateCount rootDepth bits : Nat) (state : DivideEvalState)
    (indices : state.IndicesBelow stateCount)
    (fits : state.FitsDepth rootDepth)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (rootDepthBound : rootDepth < 2 ^ bits) :
    state.partrecFlatSpace ≤
      3 * (bits + 1) +
        rootDepth * (4 * (bits + 1) + 5) + 3 := by
  have querySpace := query_flatSpace_le
    stateCount rootDepth bits state.query indices.1
    ((Nat.le_add_right state.query.depth state.stack.length).trans fits.1)
    stateCountBound rootDepthBound
  have stackSpace := divideStack_partrecFlatSpace_le
    stateCount rootDepth bits state.stack indices.2 fits.2
    stateCountBound rootDepthBound
  have stackLength : state.stack.length ≤ rootDepth :=
    (Nat.le_add_left state.stack.length state.query.depth).trans fits.1
  have stackBudget :
      state.stack.length * (4 * (bits + 1) + 5) ≤
        rootDepth * (4 * (bits + 1) + 5) :=
    Nat.mul_le_mul_right (4 * (bits + 1) + 5) stackLength
  unfold DivideEvalState.partrecFlatSpace
  exact Nat.add_le_add_right
    (Nat.add_le_add querySpace (stackSpace.trans stackBudget)) 3

theorem divideEvalIterate_encodedListSpace_le
    (stateCount depth bits first last steps : Nat)
    (relation : Nat → Nat → Bool)
    (firstBelow : first < stateCount)
    (lastBelow : last < stateCount)
    (stateCountBound : stateCount ≤ 2 ^ bits)
    (depthBound : depth < 2 ^ bits) :
    encodedListSpace
        (((divideEvalStep stateCount relation)^[steps]
          (divideEvalInitial depth first last)).toNatList) ≤
      3 * (bits + 1) +
        depth * (4 * (bits + 1) + 5) + 3 := by
  exact (encodedListSpace_divideEvalState_toNatList_le _).trans
    (divideEvalState_partrecFlatSpace_le
      stateCount depth bits _ 
      (divideEvalIterate_initial_indicesBelow
        stateCount depth first last steps relation firstBelow lastBelow)
      (divideEvalIterate_fitsDepth
        stateCount depth steps relation
        (divideEvalInitial depth first last)
        (divideEvalInitial_fitsDepth depth first last))
      stateCountBound depthBound)

end LeanTrominoes.FiniteState
