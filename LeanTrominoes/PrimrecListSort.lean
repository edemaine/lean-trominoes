/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeComputability
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

set_option maxHeartbeats 200000

/-! ## Computable list folds -/

/-- Left folds preserve computability even when the folding step is merely
computable rather than primitive recursive.  Mathlib exposes the
primitive-recursive closure theorem directly; this total tail-recursive
implementation supplies the corresponding `Computable` interface. -/
theorem listFoldl_computable
    {Input Item State : Type*}
    [Primcodable Input] [Primcodable Item] [Primcodable State]
    (items : Input → List Item)
    (initial : Input → State)
    (step : Input → State → Item → State)
    (itemsComputable : Computable items)
    (initialComputable : Computable initial)
    (stepComputable :
      Computable fun input : (Input × State) × Item =>
        step input.1.1 input.1.2 input.2) :
    Computable fun input =>
      (items input).foldl (step input) (initial input) := by
  let FoldState := (Input × State) × List Item
  let transition : FoldState → State ⊕ FoldState := fun state =>
    match state.2 with
    | [] => Sum.inl state.1.2
    | head :: tail =>
        Sum.inr ((state.1.1,
          step state.1.1 state.1.2 head), tail)
  have headComputable : Computable fun state : FoldState =>
      state.2.head? :=
    Primrec.list_head?.to_comp.comp Computable.snd
  have stopComputable : Computable fun state : FoldState =>
      (Sum.inl state.1.2 : State ⊕ FoldState) :=
    Computable.sumInl.comp
      (Computable.snd.comp Computable.fst)
  have advanceComputable : Computable₂ fun (state : FoldState)
      (head : Item) =>
      (Sum.inr ((state.1.1,
        step state.1.1 state.1.2 head), state.2.tail) :
        State ⊕ FoldState) := by
    change Computable fun combined : FoldState × Item =>
      (Sum.inr ((combined.1.1.1,
        step combined.1.1.1 combined.1.1.2 combined.2),
        combined.1.2.tail) : State ⊕ FoldState)
    have updated : Computable fun combined : FoldState × Item =>
        step combined.1.1.1 combined.1.1.2 combined.2 :=
      stepComputable.to₂.comp
        (Computable.fst.comp Computable.fst)
        Computable.snd
    have source : Computable fun combined : FoldState × Item =>
        combined.1.1.1 :=
      (Primrec.fst.comp
        (Primrec.fst.comp Primrec.fst)).to_comp
    have tail : Computable fun combined : FoldState × Item =>
        combined.1.2.tail :=
      (Primrec.list_tail.comp
        (Primrec.snd.comp Primrec.fst)).to_comp
    exact Computable.sumInr.comp
      (Computable.pair (Computable.pair source updated) tail)
  have transitionComputable : Computable transition := by
    exact (Computable.option_casesOn headComputable
      stopComputable advanceComputable).of_eq fun state => by
        rcases state with ⟨state, remaining⟩
        cases remaining <;> rfl
  have initialized : Computable fun input : Input =>
      (((input, initial input), items input) : FoldState) :=
    Computable.pair
      (Computable.pair Computable.id initialComputable)
      itemsComputable
  have fixed : Partrec
      (PFun.fix (transition : FoldState →. State ⊕ FoldState)) :=
    Partrec.fix transitionComputable.partrec
  have run : Partrec fun input : Input =>
      PFun.fix (transition : FoldState →. State ⊕ FoldState)
        ((input, initial input), items input) :=
    fixed.comp initialized
  apply run.of_eq
  intro input
  apply Part.eq_some_iff.mpr
  have terminates : ∀ (state : State) (remaining : List Item),
      remaining.foldl (step input) state ∈
        PFun.fix (transition : FoldState →. State ⊕ FoldState)
          ((input, state), remaining) := by
    intro state remaining
    induction remaining generalizing state with
    | nil =>
        apply PFun.mem_fix_iff.mpr
        left
        simp [transition]
    | cons head tail induction =>
        apply PFun.mem_fix_iff.mpr
        right
        refine ⟨((input, step input state head), tail), ?_, ?_⟩
        · simp [transition]
        · simpa using induction (step input state head)
  exact terminates (initial input) (items input)

/-- Right folds preserve computability for a computable folding step. -/
theorem listFoldr_computable
    {Input Item State : Type*}
    [Primcodable Input] [Primcodable Item] [Primcodable State]
    (items : Input → List Item)
    (initial : Input → State)
    (step : Input → Item → State → State)
    (itemsComputable : Computable items)
    (initialComputable : Computable initial)
    (stepComputable :
      Computable fun input : (Input × Item) × State =>
        step input.1.1 input.1.2 input.2) :
    Computable fun input =>
      (items input).foldr (step input) (initial input) := by
  have reversed : Computable fun input => (items input).reverse :=
    Computable.list_reverse.comp itemsComputable
  have flippedStep : Computable fun input : (Input × State) × Item =>
      step input.1.1 input.2 input.1.2 :=
    stepComputable.comp
      (show Computable fun input : (Input × State) × Item =>
          ((input.1.1, input.2), input.1.2) from
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            Primrec.snd)
          (Primrec.snd.comp Primrec.fst)).to_comp)
  exact (listFoldl_computable
    (fun input => (items input).reverse) initial
    (fun input state item => step input item state)
    reversed initialComputable flippedStep).of_eq fun input => by
      simp only [List.foldr_eq_foldl_reverse]

/-- Mapping a computable function over a computable finite list is
computable. -/
theorem listMap_computable
    {Input Item Output : Type*}
    [Primcodable Input] [Primcodable Item] [Primcodable Output]
    (items : Input → List Item)
    (mapping : Input → Item → Output)
    (itemsComputable : Computable items)
    (mappingComputable : Computable₂ mapping) :
    Computable fun input => (items input).map (mapping input) := by
  have stepComputable : Computable fun input :
      (Input × Item) × List Output =>
      mapping input.1.1 input.1.2 :: input.2 := by
    have mapped : Computable fun input :
        (Input × Item) × List Output =>
        mapping input.1.1 input.1.2 :=
      mappingComputable.comp
        (Computable.fst.comp Computable.fst)
        (Computable.snd.comp Computable.fst)
    exact Computable.list_cons.comp mapped Computable.snd
  exact (listFoldr_computable items (fun _ => [])
    (fun input item outputs => mapping input item :: outputs)
    itemsComputable (Computable.const []) stepComputable).of_eq
      fun input => by simp

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

/-- Boolean ordered insertion is computable for a computable comparison. -/
theorem boolOrderedInsert_computable
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (lessEq : Input → Item → Item → Bool)
    (lessEqComputable :
      Computable fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Computable fun input : (Input × Item) × List Item =>
      boolOrderedInsert (lessEq input.1.1) input.1.2 input.2 := by
  let OrderInput := (Input × Item) × List Item
  let FoldState := List Item × List Item
  let foldStep : OrderInput → Item → FoldState → FoldState :=
    fun input head state =>
      let original := head :: state.1
      let inserted :=
        if lessEq input.1.1 input.1.2 head then
          input.1.2 :: original
        else
          head :: state.2
      (original, inserted)
  have foldStepComputable : Computable fun input :
      (OrderInput × Item) × FoldState =>
      foldStep input.1.1 input.1.2 input.2 := by
    have original : Computable fun input :
        (OrderInput × Item) × FoldState =>
        input.1.2 :: input.2.1 :=
      Computable.list_cons.comp
        (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    have comparison : Computable fun input :
        (OrderInput × Item) × FoldState =>
        lessEq input.1.1.1.1 input.1.1.1.2 input.1.2 :=
      lessEqComputable.to₂.comp
        (Computable.fst.comp
          (Computable.fst.comp Computable.fst))
        (Computable.snd.comp Computable.fst)
    have before : Computable fun input :
        (OrderInput × Item) × FoldState =>
        input.1.1.1.2 :: input.1.2 :: input.2.1 :=
      Computable.list_cons.comp
        (Computable.snd.comp
          (Computable.fst.comp
            (Computable.fst.comp Computable.fst)))
        original
    have after : Computable fun input :
        (OrderInput × Item) × FoldState =>
        input.1.2 :: input.2.2 :=
      Computable.list_cons.comp
        (Computable.snd.comp Computable.fst)
        (Computable.snd.comp Computable.snd)
    have inserted : Computable fun input :
        (OrderInput × Item) × FoldState =>
        if lessEq input.1.1.1.1 input.1.1.1.2 input.1.2 then
          input.1.1.1.2 :: input.1.2 :: input.2.1
        else
          input.1.2 :: input.2.2 :=
      (Computable.cond comparison before after).of_eq fun input => by
        cases lessEq input.1.1.1.1 input.1.1.1.2 input.1.2 <;> rfl
    exact Computable.pair original inserted
  have folded : Computable fun input : OrderInput =>
      (input.2.foldr (foldStep input)
        ([], [input.1.2])).2 := by
    have initial : Computable fun input : OrderInput =>
        (([], [input.1.2]) : FoldState) :=
      Computable.pair (Computable.const [])
        (Computable.list_cons.comp
          (Computable.snd.comp Computable.fst)
          (Computable.const []))
    exact Computable.snd.comp
      (listFoldr_computable (fun input : OrderInput => input.2)
        (fun input => ([], [input.1.2])) foldStep
        Computable.snd initial foldStepComputable)
  apply folded.of_eq
  rintro ⟨⟨input, item⟩, items⟩
  simp only
  have equality :
      List.foldr (foldStep ((input, item), items))
          ([], [item]) items =
        (items, boolOrderedInsert (lessEq input) item items) := by
    induction items with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.foldr_cons, foldStep]
        rw [induction]
        simp only [boolOrderedInsert]
  exact congrArg Prod.snd equality

/-- Boolean insertion sort is computable for a computable comparison and
computable input list. -/
theorem boolInsertionSort_computable
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (items : Input → List Item)
    (lessEq : Input → Item → Item → Bool)
    (itemsComputable : Computable items)
    (lessEqComputable :
      Computable fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Computable fun input =>
      boolInsertionSort (lessEq input) (items input) := by
  have insertComputable : Computable fun input :
      (Input × Item) × List Item =>
      boolOrderedInsert (lessEq input.1.1)
        input.1.2 input.2 :=
    boolOrderedInsert_computable lessEq lessEqComputable
  exact (listFoldr_computable items (fun _ => [])
    (fun input item sorted =>
      boolOrderedInsert (lessEq input) item sorted)
    itemsComputable (Computable.const []) insertComputable).of_eq
      fun _ => rfl

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

/-- Stable sorting can be made canonical by tagging every item with its
original index before applying insertion sort. -/
def boolStableSort {Item : Type*}
    (lessEq : Item → Item → Bool) (items : List Item) : List Item :=
  (boolInsertionSort (List.zipIdxLE lessEq) items.zipIdx).map Prod.fst

theorem zipIdxLE_primrec
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (lessEq : Input → Item → Item → Bool)
    (lessEqPrimrec :
      Primrec fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × (Item × Nat)) × (Item × Nat) =>
      List.zipIdxLE (lessEq input.1.1)
        input.1.2 input.2 := by
  have forward : Primrec fun input :
      (Input × (Item × Nat)) × (Item × Nat) =>
      lessEq input.1.1 input.1.2.1 input.2.1 :=
    lessEqPrimrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd))
  have reverse : Primrec fun input :
      (Input × (Item × Nat)) × (Item × Nat) =>
      lessEq input.1.1 input.2.1 input.1.2.1 :=
    lessEqPrimrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  have indices : Primrec fun input :
      (Input × (Item × Nat)) × (Item × Nat) =>
      decide (input.1.2.2 ≤ input.2.2) :=
    (Primrec.nat_le.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)).decide
  exact (Primrec.cond forward
    (Primrec.cond reverse indices (Primrec.const true))
    (Primrec.const false)).of_eq fun input => by
      simp [List.zipIdxLE]

theorem boolStableSort_primrec
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (items : Input → List Item)
    (lessEq : Input → Item → Item → Bool)
    (itemsPrimrec : Primrec items)
    (lessEqPrimrec :
      Primrec fun input : (Input × Item) × Item =>
        lessEq input.1.1 input.1.2 input.2) :
    Primrec fun input => boolStableSort (lessEq input) (items input) := by
  have tagged : Primrec fun input => (items input).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp itemsPrimrec
  let taggedLessEq : Input → (Item × Nat) → (Item × Nat) → Bool :=
    fun input => List.zipIdxLE (lessEq input)
  have sorted : Primrec fun input =>
      boolInsertionSort (taggedLessEq input) (items input).zipIdx :=
    boolInsertionSort_primrec
      (fun input => (items input).zipIdx) taggedLessEq tagged
      (zipIdxLE_primrec lessEq lessEqPrimrec)
  exact (Primrec.list_map sorted
    ((Primrec.fst.comp Primrec.snd).to₂)).of_eq fun _ => rfl

/-- The indexed insertion-sort implementation is exactly Lean's stable merge
sort whenever the Boolean comparison is total and transitive. -/
theorem boolStableSort_eq_mergeSort
    {Item : Type*}
    (lessEq : Item → Item → Bool)
    (transitive : ∀ first second third,
      lessEq first second = true →
      lessEq second third = true →
      lessEq first third = true)
    (total : ∀ first second,
      (lessEq first second || lessEq second first) = true)
    (items : List Item) :
    boolStableSort lessEq items = items.mergeSort lessEq := by
  let relation : (Item × Nat) → (Item × Nat) → Prop :=
    fun first second => List.zipIdxLE lessEq first second = true
  letI : Std.Total relation := ⟨fun first second => by
    simpa only [relation, Bool.or_eq_true] using
      List.zipIdxLE_total total first second⟩
  letI : IsTrans (Item × Nat) relation := ⟨fun first second third => by
    simpa only [relation] using
      List.zipIdxLE_trans transitive first second third⟩
  have insertionEq :
      boolInsertionSort (List.zipIdxLE lessEq) items.zipIdx =
        items.zipIdx.insertionSort relation :=
    boolInsertionSort_eq_insertionSort
      (List.zipIdxLE lessEq) relation
      (fun _ _ => by rfl) items.zipIdx
  have taggedEqual :
      items.zipIdx.mergeSort (List.zipIdxLE lessEq) =
        items.zipIdx.insertionSort relation := by
    apply List.Perm.eq_of_pairwise (le := relation)
    · rintro ⟨first, firstIndex⟩ ⟨second, secondIndex⟩
        firstMember secondMember
      simp only [List.mem_mergeSort] at firstMember
      simp only [List.mem_insertionSort] at secondMember
      change List.zipIdxLE lessEq (first, firstIndex)
          (second, secondIndex) = true →
        List.zipIdxLE lessEq (second, secondIndex)
          (first, firstIndex) = true →
        (first, firstIndex) = (second, secondIndex)
      intro firstSecond secondFirst
      have forward : lessEq first second = true := by
        cases equation : lessEq first second with
        | false => simp [List.zipIdxLE, equation] at firstSecond
        | true => rfl
      have reverse : lessEq second first = true := by
        cases equation : lessEq second first with
        | false => simp [List.zipIdxLE, equation] at secondFirst
        | true => rfl
      have indexLE : firstIndex ≤ secondIndex := by
        simpa [List.zipIdxLE, forward, reverse] using firstSecond
      have reverseIndexLE : secondIndex ≤ firstIndex := by
        simpa [List.zipIdxLE, forward, reverse] using secondFirst
      have indicesEqual : firstIndex = secondIndex :=
        Nat.le_antisymm indexLE reverseIndexLE
      subst secondIndex
      have firstLookup : items[firstIndex]? = some first :=
        List.mk_mem_zipIdx_iff_getElem?.mp firstMember
      have secondLookup : items[firstIndex]? = some second :=
        List.mk_mem_zipIdx_iff_getElem?.mp secondMember
      cases Option.some.inj (firstLookup.symm.trans secondLookup)
      rfl
    · exact List.pairwise_mergeSort
        (List.zipIdxLE_trans transitive)
        (List.zipIdxLE_total total) items.zipIdx
    · exact List.pairwise_insertionSort relation items.zipIdx
    · exact (List.mergeSort_perm items.zipIdx _).trans
        (List.perm_insertionSort relation items.zipIdx).symm
  unfold boolStableSort
  rw [insertionEq, ← taggedEqual, List.mergeSort_zipIdx]

end LeanTrominoes.Computability
