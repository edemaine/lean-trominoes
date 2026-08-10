import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sort

/-!
# Primitive-recursive stable list sorting

Mathlib's stable insertion sort is executable, but its computability API does
not currently expose a primitive-recursive theorem for it.  The small Boolean
implementation below is convenient for geometric ordering: its comparison
may depend on a common external input, and the implementation is proved equal
to `List.insertionSort` whenever the Boolean comparison decides the relation.
-/

noncomputable section

namespace LeanTrominoes.Computability

/-- Insert one item into a sorted list using a Boolean comparison. -/
def boolOrderedInsert {Item : Type*}
    (lessEq : Item → Item → Bool) (item : Item) : List Item → List Item
  | [] => [item]
  | head :: tail =>
      if lessEq item head then
        item :: head :: tail
      else
        head :: boolOrderedInsert lessEq item tail

/-- Stable insertion sort driven by a Boolean comparison. -/
def boolInsertionSort {Item : Type*}
    (lessEq : Item → Item → Bool) (items : List Item) : List Item :=
  items.foldr (boolOrderedInsert lessEq) []

theorem boolOrderedInsert_primrec
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (lessEq : Input → Item → Item → Bool)
    (lessEqPrimrec :
      Primrec fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Item) × List Item =>
      boolOrderedInsert (lessEq input.1.1) input.1.2 input.2 := by
  let Source := (Input × Item) × List Item
  have singleton : Primrec fun input : Source => [input.1.2] :=
    Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.fst) (Primrec.const [])
  have step : Primrec₂ fun (input : Source)
      (state : Item × List Item × List Item) =>
      if lessEq input.1.1 input.1.2 state.1 then
        input.1.2 :: state.1 :: state.2.1
      else
        state.1 :: state.2.2 := by
    change Primrec fun combined : Source ×
        (Item × List Item × List Item) =>
      if lessEq combined.1.1.1 combined.1.1.2 combined.2.1 then
        combined.1.1.2 :: combined.2.1 :: combined.2.2.1
      else
        combined.2.1 :: combined.2.2.2
    let item : Primrec fun combined : Source ×
        (Item × List Item × List Item) => combined.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    let head : Primrec fun combined : Source ×
        (Item × List Item × List Item) => combined.2.1 :=
      Primrec.fst.comp Primrec.snd
    let tail : Primrec fun combined : Source ×
        (Item × List Item × List Item) => combined.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    let recursive : Primrec fun combined : Source ×
        (Item × List Item × List Item) => combined.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have comparison : Primrec fun combined : Source ×
        (Item × List Item × List Item) =>
        lessEq combined.1.1.1 combined.1.1.2 combined.2.1 :=
      lessEqPrimrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) item)
          head)
    have comparisonPred : PrimrecPred fun combined : Source ×
        (Item × List Item × List Item) =>
        lessEq combined.1.1.1 combined.1.1.2 combined.2.1 = true :=
      (comparison.of_eq fun combined => by
        cases lessEq combined.1.1.1 combined.1.1.2 combined.2.1 <;>
          rfl).primrecPred
    have before : Primrec fun combined : Source ×
        (Item × List Item × List Item) =>
        combined.1.1.2 :: combined.2.1 :: combined.2.2.1 :=
      Primrec.list_cons.comp item
        (Primrec.list_cons.comp head tail)
    have after : Primrec fun combined : Source ×
        (Item × List Item × List Item) =>
        combined.2.1 :: combined.2.2.2 :=
      Primrec.list_cons.comp head recursive
    exact Primrec.ite comparisonPred before after
  refine (Primrec.list_rec Primrec.snd singleton step).of_eq ?_
  intro input
  induction input.2 with
  | nil => rfl
  | cons head tail induction =>
      simp [boolOrderedInsert, induction]

theorem boolInsertionSort_primrec
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (items : Input → List Item)
    (lessEq : Input → Item → Item → Bool)
    (itemsPrimrec : Primrec items)
    (lessEqPrimrec :
      Primrec fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Primrec fun input => boolInsertionSort (lessEq input) (items input) := by
  have step : Primrec₂ fun (input : Input)
      (state : Item × List Item) =>
      boolOrderedInsert (lessEq input) state.1 state.2 := by
    change Primrec fun combined : Input × (Item × List Item) =>
      boolOrderedInsert (lessEq combined.1) combined.2.1 combined.2.2
    exact boolOrderedInsert_primrec lessEq lessEqPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr itemsPrimrec (Primrec.const []) step).of_eq
    fun _ => rfl

theorem boolOrderedInsert_eq_orderedInsert
    {Item : Type*} (lessEq : Item → Item → Bool)
    (relation : Item → Item → Prop) [DecidableRel relation]
    (correct : ∀ first second,
      lessEq first second = true ↔ relation first second)
    (item : Item) (items : List Item) :
    boolOrderedInsert lessEq item items =
      items.orderedInsert relation item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      rw [boolOrderedInsert, List.orderedInsert_cons]
      by_cases ordered : relation item head
      · simp [ordered, (correct item head).mpr ordered]
      · simp [ordered, Bool.eq_false_iff.mpr
          (fun equal => ordered ((correct item head).mp equal)), induction]

theorem boolInsertionSort_eq_insertionSort
    {Item : Type*} (lessEq : Item → Item → Bool)
    (relation : Item → Item → Prop) [DecidableRel relation]
    (correct : ∀ first second,
      lessEq first second = true ↔ relation first second)
    (items : List Item) :
    boolInsertionSort lessEq items = items.insertionSort relation := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      change boolOrderedInsert lessEq head
          (boolInsertionSort lessEq tail) =
        (tail.insertionSort relation).orderedInsert relation head
      rw [induction]
      exact boolOrderedInsert_eq_orderedInsert
        lessEq relation correct head (tail.insertionSort relation)

end LeanTrominoes.Computability
