import LeanTrominoes.PeriodicThreeCNFComputability
import LeanTrominoes.PeriodicThreeSATThreeOccurrences
import Mathlib.Computability.Partrec

/-!
# Computability of periodic 3SAT occurrence splitting

The positional cycle construction is primitive recursive under the canonical
encodings.  This file supplies primitive-recursive implementations of indexed
list traversal and duplicate removal, then verifies the complete reduction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Enumerating a list with zero-based indices is primitive recursive. -/
theorem zipIdx_primrec {α : Type*} [Primcodable α] :
    Primrec (fun list : List α => list.zipIdx) := by
  have step : Primrec₂ fun (_list : List α)
      (state : α × List α × List (α × Nat)) =>
      (state.1, 0) ::
        state.2.2.map fun tagged => (tagged.1, tagged.2 + 1) := by
    change Primrec fun combined :
        List α × (α × List α × List (α × Nat)) =>
      (combined.2.1, 0) ::
        combined.2.2.2.map fun tagged => (tagged.1, tagged.2 + 1)
    have recursive : Primrec fun combined :
        List α × (α × List α × List (α × Nat)) =>
        combined.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have shifted : Primrec fun combined :
        List α × (α × List α × List (α × Nat)) =>
        combined.2.2.2.map fun tagged => (tagged.1, tagged.2 + 1) :=
      Primrec.list_map recursive
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂
    have head : Primrec fun combined :
        List α × (α × List α × List (α × Nat)) =>
        (combined.2.1, 0) :=
      Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.const 0)
    exact Primrec.list_cons.comp head shifted
  have recursion := Primrec.list_rec
    (f := fun list : List α => list)
    (g := fun _ => ([] : List (α × Nat)))
    (h := fun _ state =>
      (state.1, 0) ::
        state.2.2.map fun tagged => (tagged.1, tagged.2 + 1))
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun list => by
    induction list with
    | nil => rfl
    | cons head tail induction =>
        rw [List.zipIdx_cons']
        dsimp only [List.recOn]
        change
          (List.rec []
            (fun head tail recursive =>
              (head, 0) ::
                recursive.map fun tagged =>
                  (tagged.1, tagged.2 + 1))
            tail) = tail.zipIdx at induction
        rw [induction]
        rfl

/-- Removing duplicate list entries is primitive recursive. -/
theorem dedup_primrec {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (fun list : List α => list.dedup) := by
  have step : Primrec₂ fun (_list : List α)
      (state : α × List α × List α) =>
      if state.1 ∈ state.2.1 then state.2.2
      else state.1 :: state.2.2 := by
    change Primrec fun combined :
        List α × (α × List α × List α) =>
      if combined.2.1 ∈ combined.2.2.1 then combined.2.2.2
      else combined.2.1 :: combined.2.2.2
    have tail : Primrec fun combined :
        List α × (α × List α × List α) =>
        combined.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have head : Primrec fun combined :
        List α × (α × List α × List α) =>
        combined.2.1 :=
      Primrec.fst.comp Primrec.snd
    have recursive : Primrec fun combined :
        List α × (α × List α × List α) =>
        combined.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have member : PrimrecPred fun combined :
        List α × (α × List α × List α) =>
        combined.2.1 ∈ combined.2.2.1 := by
      exact (Primrec.eq.exists_mem_list.comp tail head).of_eq fun _ => by
        simp
    exact Primrec.ite member recursive
      (Primrec.list_cons.comp head recursive)
  have recursion := Primrec.list_rec
    (f := fun list : List α => list)
    (g := fun _ => ([] : List α))
    (h := fun _ state =>
      if state.1 ∈ state.2.1 then state.2.2
      else state.1 :: state.2.2)
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun list => by
    induction list with
    | nil => rfl
    | cons head tail induction =>
        rw [List.dedup_cons]
        dsimp only [List.recOn]
        change
          (List.rec []
            (fun head tail recursive =>
              if head ∈ tail then recursive else head :: recursive)
            tail) = tail.dedup at induction
        rw [induction]

theorem taggedLiterals_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (taggedLiterals :
      PeriodicCNF Variable →
        List (PeriodicLiteral Variable × Nat × Nat)) := by
  have taggedClauses : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx :=
    zipIdx_primrec.comp PeriodicCNF.equivData_primrec
  have row : Primrec₂ fun (_source : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      taggedClause.1.zipIdx.map fun taggedLiteral =>
        (taggedLiteral.1, taggedClause.2, taggedLiteral.2) := by
    change Primrec fun combined :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
      combined.2.1.zipIdx.map fun taggedLiteral =>
        (taggedLiteral.1, combined.2.2, taggedLiteral.2)
    have literals : Primrec fun combined :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
        combined.2.1.zipIdx :=
      zipIdx_primrec.comp (Primrec.fst.comp Primrec.snd)
    exact Primrec.list_map literals
      (Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.list_flatMap taggedClauses row

theorem sourceVariables_primrec {Variable : Type*}
    [Primcodable Variable] [DecidableEq Variable] :
    Primrec (sourceVariables : PeriodicCNF Variable → List Variable) := by
  have atoms : Primrec fun source : PeriodicCNF Variable =>
      (taggedLiterals source).map fun tagged => tagged.1.atom :=
    Primrec.list_map taggedLiterals_primrec
      (PeriodicThreeCNF.literal_atom_primrec.comp
        (Primrec.fst.comp Primrec.snd)).to₂
  exact dedup_primrec.comp atoms

theorem occurrenceVariables_primrec {Variable : Type*}
    [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (occurrenceVariables :
      PeriodicCNF Variable → Variable →
        List (ThreeOccurrenceVariable Variable)) := by
  change Primrec fun input : PeriodicCNF Variable × Variable =>
    occurrenceVariables input.1 input.2
  have tagged : Primrec fun input : PeriodicCNF Variable × Variable =>
      taggedLiterals input.1 :=
    taggedLiterals_primrec.comp Primrec.fst
  have select : Primrec₂ fun (input : PeriodicCNF Variable × Variable)
      (item : PeriodicLiteral Variable × Nat × Nat) =>
      if item.1.atom = input.2 then
        some (input.2, item.2.1, item.2.2)
      else
        none := by
    change Primrec fun combined :
        (PeriodicCNF Variable × Variable) ×
          (PeriodicLiteral Variable × Nat × Nat) =>
      if combined.2.1.atom = combined.1.2 then
        some (combined.1.2, combined.2.2.1, combined.2.2.2)
      else
        none
    have same : PrimrecPred fun combined :
        (PeriodicCNF Variable × Variable) ×
          (PeriodicLiteral Variable × Nat × Nat) =>
        combined.2.1.atom = combined.1.2 :=
      Primrec.eq.comp
        (PeriodicThreeCNF.literal_atom_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    have selected : Primrec fun combined :
        (PeriodicCNF Variable × Variable) ×
          (PeriodicLiteral Variable × Nat × Nat) =>
        some (combined.1.2, combined.2.2.1, combined.2.2.2) :=
      Primrec.option_some.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    exact Primrec.ite same selected (Primrec.const none)
  exact Primrec.listFilterMap tagged select

theorem occurrenceLiteral_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input : (Nat × Nat) × PeriodicLiteral Variable =>
      occurrenceLiteral input.1.1 input.1.2 input.2 := by
  have atom : Primrec fun input :
      (Nat × Nat) × PeriodicLiteral Variable =>
      (input.2.atom, input.1.1, input.1.2) :=
    Primrec.pair
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
      Primrec.fst
  have data : Primrec fun input :
      (Nat × Nat) × PeriodicLiteral Variable =>
      ((input.2.atom, input.1.1, input.1.2),
        input.2.offset, input.2.value) :=
    Primrec.pair atom
      (Primrec.pair
        (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
        (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem occurrenceClause_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec₂ (occurrenceClause :
      Nat → PeriodicClause Variable →
        PeriodicClause (ThreeOccurrenceVariable Variable)) := by
  change Primrec fun input : Nat × PeriodicClause Variable =>
    occurrenceClause input.1 input.2
  have tagged : Primrec fun input : Nat × PeriodicClause Variable =>
      input.2.zipIdx :=
    zipIdx_primrec.comp Primrec.snd
  have literal : Primrec₂ fun
      (input : Nat × PeriodicClause Variable)
      (item : PeriodicLiteral Variable × Nat) =>
      occurrenceLiteral input.1 item.2 item.1 := by
    change Primrec fun combined :
        (Nat × PeriodicClause Variable) ×
          (PeriodicLiteral Variable × Nat) =>
      occurrenceLiteral combined.1.1 combined.2.2 combined.2.1
    exact occurrenceLiteral_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map tagged literal

theorem occurrenceClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec (occurrenceClauses :
      PeriodicCNF Variable →
        List (PeriodicClause (ThreeOccurrenceVariable Variable))) := by
  have tagged : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx :=
    zipIdx_primrec.comp PeriodicCNF.equivData_primrec
  have clause : Primrec₂ fun (_source : PeriodicCNF Variable)
      (item : PeriodicClause Variable × Nat) =>
      occurrenceClause item.2 item.1 := by
    exact occurrenceClause_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_map tagged clause

theorem alignedLiteral_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        ThreeOccurrenceVariable Variable × Bool =>
      (⟨input.1, (0, 0), input.2⟩ :
        PeriodicLiteral (ThreeOccurrenceVariable Variable)) := by
  have data : Primrec fun input :
      ThreeOccurrenceVariable Variable × Bool =>
      (input.1, (((0, 0) : Cell), input.2)) :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const ((0, 0) : Cell)) Primrec.snd)
  exact ((PeriodicLiteral.equivData_symm_primrec
    (Variable := ThreeOccurrenceVariable Variable)).comp data).of_eq
    fun input => by
      rcases input with ⟨copy, value⟩
      rfl

theorem implicationClause_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec₂ (implicationClause :
      ThreeOccurrenceVariable Variable →
        ThreeOccurrenceVariable Variable →
          PeriodicClause (ThreeOccurrenceVariable Variable)) := by
  change Primrec fun input :
      ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable =>
    implicationClause input.1 input.2
  have negative : Primrec fun input :
      ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable =>
      (⟨input.1, (0, 0), false⟩ :
        PeriodicLiteral (ThreeOccurrenceVariable Variable)) :=
    alignedLiteral_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.const false))
  have positive : Primrec fun input :
      ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable =>
      (⟨input.2, (0, 0), true⟩ :
        PeriodicLiteral (ThreeOccurrenceVariable Variable)) :=
    alignedLiteral_primrec.comp
      (Primrec.pair Primrec.snd (Primrec.const true))
  exact Primrec.list_cons.comp negative
    (Primrec.list_cons.comp positive (Primrec.const []))

/-- A structurally recursive implementation of a directed cycle tail.
Unlike `cycleFrom`, the recursive call keeps the closing copy as an explicit
parameter and simply consumes the tail of the complete copy list. -/
def computableCycleTail {Variable : Type*}
    (first : ThreeOccurrenceVariable Variable) :
    List (ThreeOccurrenceVariable Variable) →
      List (PeriodicClause (ThreeOccurrenceVariable Variable))
  | [] => []
  | current :: rest =>
      match rest with
      | [] => [implicationClause current first]
      | next :: _ =>
          implicationClause current next ::
            computableCycleTail first rest

theorem computableCycleTail_eq {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    computableCycleTail first (current :: rest) =
      cycleFrom first current rest := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp only [computableCycleTail, cycleFrom]
      exact congrArg
        (List.cons (implicationClause current next))
        (induction next)

/-- A range-free, structurally recursive implementation of `cycleClauses`. -/
def computableCycleClauses {Variable : Type*} :
    List (ThreeOccurrenceVariable Variable) →
      List (PeriodicClause (ThreeOccurrenceVariable Variable))
  | [] => []
  | first :: rest => computableCycleTail first (first :: rest)

theorem computableCycleClauses_eq {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    computableCycleClauses copies = cycleClauses copies := by
  cases copies with
  | nil => rfl
  | cons first rest =>
      exact computableCycleTail_eq first first rest

theorem computableCycleTail_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec₂ (computableCycleTail :
      ThreeOccurrenceVariable Variable →
        List (ThreeOccurrenceVariable Variable) →
          List (PeriodicClause (ThreeOccurrenceVariable Variable))) := by
  change Primrec fun input :
      ThreeOccurrenceVariable Variable ×
        List (ThreeOccurrenceVariable Variable) =>
    computableCycleTail input.1 input.2
  let Copy := ThreeOccurrenceVariable Variable
  let Clause := PeriodicClause Copy
  let Input := Copy × List Copy
  let State := Copy × List Copy × List Clause
  have step : Primrec₂ fun (input : Input) (state : State) =>
      match state.2.1 with
      | [] => [implicationClause state.1 input.1]
      | next :: _ =>
          implicationClause state.1 next :: state.2.2 := by
    change Primrec fun combined : Input × State =>
      match combined.2.2.1 with
      | [] => [implicationClause combined.2.1 combined.1.1]
      | next :: _ =>
          implicationClause combined.2.1 next :: combined.2.2.2
    have tail : Primrec fun combined : Input × State =>
        combined.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have nilClause : Primrec fun combined : Input × State =>
        implicationClause combined.2.1 combined.1.1 :=
      implicationClause_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    have nilOutput : Primrec fun combined : Input × State =>
        [implicationClause combined.2.1 combined.1.1] :=
      Primrec.list_cons.comp nilClause (Primrec.const [])
    have consCase : Primrec₂ fun (combined : Input × State)
        (nextAndRest : Copy × List Copy) =>
        implicationClause combined.2.1 nextAndRest.1 ::
          combined.2.2.2 := by
      change Primrec fun pair :
          (Input × State) × (Copy × List Copy) =>
        implicationClause pair.1.2.1 pair.2.1 ::
          pair.1.2.2.2
      have clause : Primrec fun pair :
          (Input × State) × (Copy × List Copy) =>
          implicationClause pair.1.2.1 pair.2.1 :=
        implicationClause_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)
      have recursive : Primrec fun pair :
          (Input × State) × (Copy × List Copy) =>
          pair.1.2.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.fst))
      exact Primrec.list_cons.comp clause recursive
    exact (Primrec.list_casesOn tail nilOutput consCase).of_eq
      fun combined => by
        cases combined.2.2.1 <;> rfl
  have recursion := Primrec.list_rec
    (f := fun input : Input => input.2)
    (g := fun _ => ([] : List Clause))
    (h := fun input state =>
      match state.2.1 with
      | [] => [implicationClause state.1 input.1]
      | next :: _ =>
          implicationClause state.1 next :: state.2.2)
    Primrec.snd (Primrec.const []) step
  exact recursion.of_eq fun input => by
    induction input.2 with
    | nil => rfl
    | cons current rest induction =>
        dsimp only [List.recOn] at induction ⊢
        cases rest with
        | nil => rfl
        | cons next rest =>
            rw [induction]
            rfl

theorem computableCycleClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec (computableCycleClauses :
      List (ThreeOccurrenceVariable Variable) →
        List (PeriodicClause (ThreeOccurrenceVariable Variable))) := by
  have nilOutput : Primrec fun _ :
      List (ThreeOccurrenceVariable Variable) =>
      ([] : List (PeriodicClause
        (ThreeOccurrenceVariable Variable))) :=
    Primrec.const []
  have consCase : Primrec₂ fun
      (_copies : List (ThreeOccurrenceVariable Variable))
      (firstAndRest :
        ThreeOccurrenceVariable Variable ×
          List (ThreeOccurrenceVariable Variable)) =>
      computableCycleTail firstAndRest.1
        (firstAndRest.1 :: firstAndRest.2) := by
    change Primrec fun combined :
        List (ThreeOccurrenceVariable Variable) ×
          (ThreeOccurrenceVariable Variable ×
            List (ThreeOccurrenceVariable Variable)) =>
      computableCycleTail combined.2.1
        (combined.2.1 :: combined.2.2)
    have copies : Primrec fun combined :
        List (ThreeOccurrenceVariable Variable) ×
          (ThreeOccurrenceVariable Variable ×
            List (ThreeOccurrenceVariable Variable)) =>
        combined.2.1 :: combined.2.2 :=
      Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)
    exact computableCycleTail_primrec.comp
      (Primrec.fst.comp Primrec.snd) copies
  exact (Primrec.list_casesOn Primrec.id nilOutput consCase).of_eq
    fun copies => by
      cases copies <;> rfl

theorem cycleClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec (cycleClauses :
      List (ThreeOccurrenceVariable Variable) →
        List (PeriodicClause (ThreeOccurrenceVariable Variable))) :=
  computableCycleClauses_primrec.of_eq computableCycleClauses_eq

theorem allCycleClauses_primrec {Variable : Type*}
    [Primcodable Variable] [DecidableEq Variable] :
    Primrec (allCycleClauses :
      PeriodicCNF Variable →
        List (PeriodicClause (ThreeOccurrenceVariable Variable))) := by
  have cycles : Primrec₂ fun (source : PeriodicCNF Variable)
      (atom : Variable) =>
      cycleClauses (occurrenceVariables source atom) := by
    change Primrec fun input : PeriodicCNF Variable × Variable =>
      cycleClauses (occurrenceVariables input.1 input.2)
    exact cycleClauses_primrec.comp
      (occurrenceVariables_primrec.comp Primrec.fst Primrec.snd)
  exact Primrec.list_flatMap sourceVariables_primrec cycles

/-- The complete occurrence-splitting conversion is primitive recursive. -/
theorem formula_primrec {Variable : Type*}
    [Primcodable Variable] [DecidableEq Variable] :
    Primrec (formula :
      PeriodicCNF Variable →
        PeriodicCNF (ThreeOccurrenceVariable Variable)) := by
  have clauses : Primrec fun source : PeriodicCNF Variable =>
      occurrenceClauses source ++ allCycleClauses source :=
    Primrec.list_append.comp occurrenceClauses_primrec
      allCycleClauses_primrec
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

theorem formula_computable {Variable : Type*}
    [Primcodable Variable] [DecidableEq Variable] :
    Computable (formula :
      PeriodicCNF Variable →
        PeriodicCNF (ThreeOccurrenceVariable Variable)) :=
  formula_primrec.to_comp

/-- The variable type at the Wang-to-periodic-3SAT-3 endpoint. -/
abbrev WangThreeSATThreeVariable :=
  ThreeOccurrenceVariable (ThreeCNFVariable LeanWang.WangTile)

local instance : BEq (ThreeCNFVariable LeanWang.WangTile) :=
  instBEqOfDecidableEq

/-- The local periodic 3SAT-3 decision predicate, treating presentations that
violate locality, width three, or the three-occurrence bound as no-instances. -/
def LocalThreeSATThreeHolds
    (threeSATThree : PeriodicCNF WangThreeSATThreeVariable) : Prop :=
  threeSATThree.IsLocal ∧
    threeSATThree.WidthAtMost 3 ∧
    threeSATThree.OccurrencesAtMost 3 ∧
    threeSATThree.Satisfiable

/-- The Wang encoding followed by width and occurrence splitting. -/
def wangFormula (tiles : LeanWang.TileSet) :
    PeriodicCNF WangThreeSATThreeVariable :=
  formula (PeriodicThreeCNF.wangFormula tiles)

theorem wangFormula_computable : Computable wangFormula :=
  formula_computable.comp PeriodicThreeCNF.wangFormula_computable

/-- The complete Wang reduction satisfies the exact local 3SAT-3 endpoint. -/
theorem wangFormula_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔
      LocalThreeSATThreeHolds (wangFormula tiles) := by
  constructor
  · intro tilesPlane
    have sourceHolds :=
      (PeriodicThreeCNF.wangFormula_correct tiles).1 tilesPlane
    refine ⟨formula_isLocal sourceHolds.1,
      formula_widthAtMostThree sourceHolds.2.1,
      formula_occurrencesAtMostThree
        (PeriodicThreeCNF.wangFormula tiles), ?_⟩
    exact (satisfiable_iff _).1 sourceHolds.2.2
  · intro targetHolds
    apply (PeriodicThreeCNF.wangFormula_correct tiles).2
    refine ⟨PeriodicThreeCNF.formula_isLocal
        (WangPeriodicCNF.formula_isLocal tiles),
      PeriodicThreeCNF.formula_widthAtMostThree _, ?_⟩
    exact (satisfiable_iff _).2 targetHolds.2.2.2

/-- Local periodic 3SAT-3 satisfiability is co-r.e.-hard. -/
theorem localThreeSATThreeCoREHard :
    LeanWang.CoREHard LocalThreeSATThreeHolds := by
  intro α _ source source_coRE
  obtain ⟨reduce, reduce_computable, reduce_correct⟩ :=
    LeanWang.domino_problem_coRE_hard source source_coRE
  refine ⟨wangFormula ∘ reduce,
    wangFormula_computable.comp reduce_computable, ?_⟩
  intro input
  rw [reduce_correct input]
  exact wangFormula_correct (reduce input)

end PeriodicThreeSATThree
end LeanTrominoes
