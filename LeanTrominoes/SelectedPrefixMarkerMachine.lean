/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.FiniteBlockTransducer

/-!
# Finite selected-prefix marker

For a fixed cutoff, this transducer retains every input symbol and tags it by
the number of earlier selected symbols, capped at the cutoff.  The tag lets a
later unary loop skip any fixed prefix of selected positions without changing
or deleting the original prepared input.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace SelectedPrefixMarkerMachine

abbrev Count (cutoff : Nat) := Fin (cutoff + 1)

def zeroCount (cutoff : Nat) : Count cutoff := ⟨0, by omega⟩

def capSucc {cutoff : Nat} (count : Count cutoff) : Count cutoff :=
  if below : count.val < cutoff then
    ⟨count.val + 1, by omega⟩
  else
    count

@[simp]
theorem capSucc_val_of_lt {cutoff : Nat} (count : Count cutoff)
    (below : count.val < cutoff) :
    (capSucc count).val = count.val + 1 := by
  simp [capSucc, below]

@[simp]
theorem capSucc_val_of_ge {cutoff : Nat} (count : Count cutoff)
    (above : cutoff ≤ count.val) :
    (capSucc count).val = count.val := by
  simp [capSucc, Nat.not_lt.mpr above]

def nextCount {Data : Type} {cutoff : Nat} (selected : Data → Bool)
    (data : Data) (count : Count cutoff) : Count cutoff :=
  if selected data then capSucc count else count

abbrev Tagged (cutoff : Nat) (Data : Type) := Data × Count cutoff

def markAux {Data : Type} {cutoff : Nat} (selected : Data → Bool) :
    Count cutoff → List Data → List (Tagged cutoff Data)
  | _, [] => []
  | count, data :: datas =>
      (data, count) :: markAux selected (nextCount selected data count) datas

def mark {Data : Type} (selected : Data → Bool) (cutoff : Nat)
    (data : List Data) : List (Tagged cutoff Data) :=
  markAux selected (zeroCount cutoff) data

def countAfter {Data : Type} {cutoff : Nat} (selected : Data → Bool) :
    Count cutoff → List Data → Count cutoff
  | count, [] => count
  | count, data :: datas =>
      countAfter selected (nextCount selected data count) datas

@[simp]
theorem markAux_length {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (count : Count cutoff) (data : List Data) :
    (markAux selected count data).length = data.length := by
  induction data generalizing count with
  | nil => rfl
  | cons item data induction => simp [markAux, induction]

inductive Stack
  | input
  | accumulator
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | reverse
  deriving Fintype

abbrev State (cutoff : Nat) (Data : Type) :=
  Count cutoff × Option (Data ⊕ Tagged cutoff Data)

abbrev Alphabet (cutoff : Nat) (Data : Type) : Stack → Type
  | .input => Data
  | .accumulator | .output => Tagged cutoff Data

def initialState (cutoff : Nat) {Data : Type} : State cutoff Data :=
  (zeroCount cutoff, none)

def stateIsEmpty {cutoff : Nat} {Data : Type} :
    State cutoff Data → Bool
  | (_, value) => value.isNone

def taggedFromState {cutoff : Nat} {Data : Type} [Inhabited Data] :
    State cutoff Data → Tagged cutoff Data
  | (count, some (.inl data)) => (data, count)
  | (count, _) => (default, count)

def outputFromState {cutoff : Nat} {Data : Type} [Inhabited Data] :
    State cutoff Data → Tagged cutoff Data
  | (_, some (.inr tagged)) => tagged
  | (count, _) => (default, count)

def advanceState {cutoff : Nat} {Data : Type} (selected : Data → Bool) :
    State cutoff Data → State cutoff Data
  | (count, some (.inl data)) => (nextCount selected data count, none)
  | (count, _) => (count, none)

def clearState {cutoff : Nat} {Data : Type} :
    State cutoff Data → State cutoff Data
  | (count, _) => (count, none)

def program {cutoff : Nat} {Data : Type} [Inhabited Data]
    (selected : Data → Bool) :
    Label → TM2.Stmt (Alphabet cutoff Data) Label (State cutoff Data)
  | .scan =>
      .pop .input
        (fun state data => (state.1, data.map Sum.inl))
        (.branch stateIsEmpty
          (.goto fun _ => .reverse)
          (.push .accumulator taggedFromState
            (.load (advanceState selected) (.goto fun _ => .scan))))
  | .reverse =>
      .pop .accumulator
        (fun state tagged => (state.1, tagged.map Sum.inr))
        (.branch stateIsEmpty
          (.load (fun _ => initialState cutoff) .halt)
          (.push .output outputFromState
            (.load clearState (.goto fun _ => .reverse))))

abbrev machine (cutoff : Nat) (Data : Type) [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet cutoff Data
  Λ := Label
  main := .scan
  σ := State cutoff Data
  initialState := initialState cutoff
  m := program selected

def tapes {cutoff : Nat} {Data : Type} (input : List Data)
    (accumulator output : List (Tagged cutoff Data)) :
    ∀ stack, List (Alphabet cutoff Data stack)
  | .input => input
  | .accumulator => accumulator
  | .output => output

def scanCfg {cutoff : Nat} {Data : Type} (count : Count cutoff)
    (input : List Data) (accumulator : List (Tagged cutoff Data)) :
    TM2.Cfg (Alphabet cutoff Data) Label (State cutoff Data) :=
  ⟨some .scan, (count, none), tapes input accumulator []⟩

def reverseCfg {cutoff : Nat} {Data : Type} (count : Count cutoff)
    (accumulator output : List (Tagged cutoff Data)) :
    TM2.Cfg (Alphabet cutoff Data) Label (State cutoff Data) :=
  ⟨some .reverse, (count, none), tapes [] accumulator output⟩

def haltCfg {cutoff : Nat} {Data : Type}
    (output : List (Tagged cutoff Data)) :
    TM2.Cfg (Alphabet cutoff Data) Label (State cutoff Data) :=
  ⟨none, initialState cutoff, tapes [] [] output⟩

@[simp]
theorem update_tapes_input {cutoff : Nat} {Data : Type}
    (head : Data) (input : List Data)
    (accumulator output : List (Tagged cutoff Data)) :
    Function.update (tapes (head :: input) accumulator output)
        Stack.input input =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem push_tapes_accumulator {cutoff : Nat} {Data : Type}
    (input : List Data) (head : Tagged cutoff Data)
    (accumulator output : List (Tagged cutoff Data)) :
    Function.update (tapes input accumulator output)
        Stack.accumulator (head :: accumulator) =
      tapes input (head :: accumulator) output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_accumulator {cutoff : Nat} {Data : Type}
    (input : List Data) (head : Tagged cutoff Data)
    (accumulator output : List (Tagged cutoff Data)) :
    Function.update (tapes input (head :: accumulator) output)
        Stack.accumulator accumulator =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {cutoff : Nat} {Data : Type}
    (input : List Data) (accumulator : List (Tagged cutoff Data))
    (head : Tagged cutoff Data) (output : List (Tagged cutoff Data)) :
    Function.update (tapes input accumulator output)
        Stack.output (head :: output) =
      tapes input accumulator (head :: output) := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scan_cons {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (data : Data) (input : List Data)
    (accumulator : List (Tagged cutoff Data)) :
    TM2.step (program selected) (scanCfg count (data :: input) accumulator) =
      some (scanCfg (nextCount selected data count) input
        ((data, count) :: accumulator)) := by
  rcases count with ⟨count, countBound⟩
  cases choice : selected data <;>
    simp [TM2.step, program, scanCfg, tapes, stateIsEmpty,
      taggedFromState, advanceState, nextCount, choice] <;>
    (funext stack; cases stack <;> simp [tapes, Function.update])

theorem step_scan_nil {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (accumulator : List (Tagged cutoff Data)) :
    TM2.step (program selected) (scanCfg count [] accumulator) =
      some (reverseCfg count accumulator []) := by
  rcases count with ⟨count, countBound⟩
  simp [TM2.step, program, scanCfg, reverseCfg, tapes, stateIsEmpty,
    Function.update]

theorem step_reverse_cons {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (tagged : Tagged cutoff Data)
    (accumulator output : List (Tagged cutoff Data)) :
    TM2.step (program selected)
        (reverseCfg count (tagged :: accumulator) output) =
      some (reverseCfg count accumulator (tagged :: output)) := by
  rcases count with ⟨count, countBound⟩
  rcases tagged with ⟨data, tag⟩
  simp [TM2.step, program, reverseCfg, tapes, stateIsEmpty,
    outputFromState, clearState]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverse_nil {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (output : List (Tagged cutoff Data)) :
    TM2.step (program selected) (reverseCfg count [] output) =
      some (haltCfg output) := by
  rcases count with ⟨count, countBound⟩
  simp [TM2.step, program, reverseCfg, haltCfg, tapes, stateIsEmpty,
    initialState, Function.update]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

def scan_evalsInTime {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (input : List Data)
    (accumulator : List (Tagged cutoff Data)) :
    EvalsToInTime (TM2.step (program selected))
      (scanCfg count input accumulator)
      (some (reverseCfg (countAfter selected count input)
        ((markAux selected count input).reverse ++ accumulator) []))
      (input.length + 1) := by
  induction input generalizing count accumulator with
  | nil =>
      simpa [countAfter, markAux] using
        oneStep (step_scan_nil selected count accumulator)
  | cons data input induction =>
      have first := oneStep
        (step_scan_cons selected count data input accumulator)
      have rest := induction (nextCount selected data count)
        ((data, count) :: accumulator)
      have composed := EvalsToInTime.trans
        (TM2.step (program selected)) 1 (input.length + 1)
        (scanCfg count (data :: input) accumulator)
        (scanCfg (nextCount selected data count) input
          ((data, count) :: accumulator))
        (some (reverseCfg
          (countAfter selected (nextCount selected data count) input)
          ((markAux selected (nextCount selected data count) input).reverse ++
            (data, count) :: accumulator) []))
        first rest
      simpa [countAfter, markAux, List.reverse_cons, List.append_assoc] using
        composed

def reverse_evalsInTime {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (count : Count cutoff) (accumulator output : List (Tagged cutoff Data)) :
    EvalsToInTime (TM2.step (program selected))
      (reverseCfg count accumulator output)
      (some (haltCfg (accumulator.reverse ++ output)))
      (accumulator.length + 1) := by
  induction accumulator generalizing output with
  | nil =>
      simpa using oneStep (step_reverse_nil selected count output)
  | cons tagged accumulator induction =>
      have first := oneStep
        (step_reverse_cons selected count tagged accumulator output)
      have rest := induction (tagged :: output)
      have composed := EvalsToInTime.trans
        (TM2.step (program selected)) 1 (accumulator.length + 1)
        (reverseCfg count (tagged :: accumulator) output)
        (reverseCfg count accumulator (tagged :: output))
        (some (haltCfg (accumulator.reverse ++ tagged :: output)))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

theorem initList_eq_scanCfg {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (input : List Data) :
    initList (machine cutoff Data selected) input =
      scanCfg (zeroCount cutoff) input [] := by
  unfold initList machine scanCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (output : List (Tagged cutoff Data)) :
    haltList (machine cutoff Data selected) output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_outputsInTime {cutoff : Nat} {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (input : List Data) :
    TM2OutputsInTime (machine cutoff Data selected) input
      (some (mark selected cutoff input)) (2 * input.length + 2) := by
  have scanned := scan_evalsInTime selected (zeroCount cutoff) input []
  have reversed := reverse_evalsInTime selected
    (countAfter selected (zeroCount cutoff) input)
    (mark selected cutoff input).reverse []
  have whole := EvalsToInTime.trans (TM2.step (program selected))
    (input.length + 1) (input.length + 1)
    (scanCfg (zeroCount cutoff) input [])
    (reverseCfg (countAfter selected (zeroCount cutoff) input)
      (mark selected cutoff input).reverse [])
    (some (haltCfg (mark selected cutoff input)))
    (by simpa [mark] using scanned) (by
      simpa [mark, markAux_length] using reversed)
  change EvalsToInTime (TM2.step (program selected))
    (initList (machine cutoff Data selected) input)
    (some (haltList (machine cutoff Data selected)
      (mark selected cutoff input)))
    (2 * input.length + 2)
  rw [initList_eq_scanCfg selected input,
    haltList_eq_haltCfg selected]
  exact
    { toEvalsTo := whole.toEvalsTo
      steps_le_m := whole.steps_le_m.trans (by omega) }

end SelectedPrefixMarkerMachine
end LeanTrominoes
