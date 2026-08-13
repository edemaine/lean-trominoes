import LeanTrominoes.Complexity

/-!
# Polynomial-time finite block transducers

The periodic-CNF hardness compiler ultimately consumes the symbols of an
arbitrary finite source encoding, while its arithmetic evaluator uses a fixed
native alphabet.  This file supplies the first machine-level bridge: a
three-stack `FinTM2` which replaces every source symbol by a fixed finite word.

One scan step removes a source symbol, one emit step prepends the reversed
block to an accumulator, and a final pass reverses the accumulator onto the
output stack.  The exact run takes
`2 * input.length + output.length + 2` machine steps.  Finiteness of the source
alphabet turns the output length into a uniform linear bound and hence gives a
`TM2ComputableInPolyTime` certificate.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace FiniteBlockTransducer

inductive Stack
  | input
  | accumulator
  | output
deriving DecidableEq, Fintype

inductive Label (Source : Type)
  | scan
  | emit (symbol : Source)
  | reverse
deriving Fintype

abbrev State (Source Target : Type) := Option (Source ⊕ Target)

abbrev Alphabet (Source Target : Type) : Stack → Type
  | .input => Source
  | .accumulator => Target
  | .output => Target

def pushWord {Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source Target)) :
    TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source Target) :=
  word.foldr
    (fun symbol continuation =>
      .push .accumulator (fun _ => symbol) continuation)
    next

def program {Source Target : Type} [Inhabited Target]
    (word : Source → List Target) :
    Label Source →
      TM2.Stmt (Alphabet Source Target) (Label Source)
        (State Source Target)
  | .scan =>
      .pop .input (fun _ symbol => symbol.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .reverse)
          (.goto fun state =>
            match state with
            | some (.inl symbol) => .emit symbol
            | _ => .reverse))
  | .emit symbol =>
      pushWord (word symbol)
        (.load (fun _ => none) (.goto fun _ => .scan))
  | .reverse =>
      .pop .accumulator (fun _ symbol => symbol.map Sum.inr)
        (.branch Option.isNone
          .halt
          (.push .output
            (fun state =>
              match state with
              | some (.inr symbol) => symbol
              | _ => default)
            (.load (fun _ => none) (.goto fun _ => .reverse))))

abbrev machine (Source Target : Type)
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Source Target
  Λ := Label Source
  main := .scan
  σ := State Source Target
  initialState := none
  m := program word

def tapes {Source Target : Type}
    (input : List Source) (accumulator output : List Target) :
    ∀ stack, List (Alphabet Source Target stack)
  | .input => input
  | .accumulator => accumulator
  | .output => output

def scanCfg {Source Target : Type}
    (input : List Source) (accumulator : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source Target) :=
  ⟨some .scan, none, tapes input accumulator []⟩

def emitCfg {Source Target : Type}
    (symbol : Source) (input : List Source)
    (accumulator : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source Target) :=
  ⟨some (.emit symbol), some (.inl symbol),
    tapes input accumulator []⟩

def reverseCfg {Source Target : Type}
    (accumulator output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source Target) :=
  ⟨some .reverse, none, tapes [] accumulator output⟩

def haltCfg {Source Target : Type} (output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source Target) :=
  ⟨none, none, tapes [] [] output⟩

@[simp]
theorem update_tapes_input {Source Target : Type}
    (head : Source) (input : List Source)
    (accumulator output : List Target) :
    Function.update (tapes (head :: input) accumulator output)
        Stack.input input =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_accumulator {Source Target : Type}
    (input : List Source) (head : Target)
    (accumulator output : List Target) :
    Function.update (tapes input (head :: accumulator) output)
        Stack.accumulator accumulator =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem push_tapes_accumulator {Source Target : Type}
    (input : List Source) (head : Target)
    (accumulator output : List Target) :
    Function.update (tapes input accumulator output)
        Stack.accumulator (head :: accumulator) =
      tapes input (head :: accumulator) output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {Source Target : Type}
    (input : List Source) (accumulator : List Target)
    (head : Target) (output : List Target) :
    Function.update (tapes input accumulator output)
        Stack.output (head :: output) =
      tapes input accumulator (head :: output) := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushWord {Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source Target))
    (state : State Source Target)
    (input : List Source) (accumulator output : List Target) :
    TM2.stepAux (pushWord word next) state
        (tapes input accumulator output) =
      TM2.stepAux next state
        (tapes input (word.reverse ++ accumulator) output) := by
  induction word generalizing accumulator with
  | nil => simp [pushWord]
  | cons symbol word induction =>
      simp only [pushWord, List.foldr_cons, TM2.stepAux]
      simp only [tapes]
      rw [push_tapes_accumulator]
      change TM2.stepAux (pushWord word next) state
          (tapes input (symbol :: accumulator) output) =
        TM2.stepAux next state
          (tapes input ((symbol :: word).reverse ++ accumulator) output)
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem step_scan_cons {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (symbol : Source)
    (input : List Source) (accumulator : List Target) :
    TM2.step (program word)
        (scanCfg (symbol :: input) accumulator) =
      some (emitCfg symbol input accumulator) := by
  simp [TM2.step, program, scanCfg, emitCfg, tapes]

theorem step_emit {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (symbol : Source)
    (input : List Source) (accumulator : List Target) :
    TM2.step (program word)
        (emitCfg symbol input accumulator) =
      some (scanCfg input ((word symbol).reverse ++ accumulator)) := by
  simp only [TM2.step, program, emitCfg, scanCfg]
  rw [stepAux_pushWord]
  rfl

theorem step_scan_nil {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (accumulator : List Target) :
    TM2.step (program word) (scanCfg [] accumulator) =
      some (reverseCfg accumulator []) := by
  simp [TM2.step, program, scanCfg, reverseCfg, tapes]

theorem step_reverse_cons {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (symbol : Target)
    (accumulator output : List Target) :
    TM2.step (program word)
        (reverseCfg (symbol :: accumulator) output) =
      some (reverseCfg accumulator (symbol :: output)) := by
  simp [TM2.step, program, reverseCfg, tapes,
    update_tapes_accumulator]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverse_nil {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (output : List Target) :
    TM2.step (program word) (reverseCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseCfg, haltCfg, tapes]

def oneStep {Configuration : Type} {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    change (some first).bind transition = some last
    simpa using step
  steps_le_m := Nat.le_refl 1

def scan_evalsInTime {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (input : List Source)
    (accumulator : List Target) :
    EvalsToInTime (TM2.step (program word))
      (scanCfg input accumulator)
      (some (reverseCfg
        ((input.flatMap word).reverse ++ accumulator) []))
      (2 * input.length + 1) := by
  induction input generalizing accumulator with
  | nil =>
      simpa using oneStep (step_scan_nil word accumulator)
  | cons symbol input induction =>
      let emitted := (word symbol).reverse ++ accumulator
      have popStep : EvalsToInTime (TM2.step (program word))
          (scanCfg (symbol :: input) accumulator)
          (some (emitCfg symbol input accumulator)) 1 :=
        oneStep (step_scan_cons word symbol input accumulator)
      have emitStep : EvalsToInTime (TM2.step (program word))
          (emitCfg symbol input accumulator)
          (some (scanCfg input emitted)) 1 :=
        oneStep (step_emit word symbol input accumulator)
      have first := EvalsToInTime.trans _ 1 1 _ _ _ popStep emitStep
      have rest := induction emitted
      have target :
          (input.flatMap word).reverse ++ emitted =
            (((symbol :: input).flatMap word).reverse ++ accumulator) := by
        simp [emitted, List.reverse_append, List.append_assoc]
      rw [target] at rest
      have composed := EvalsToInTime.trans _ 2
        (2 * input.length + 1) _ _ _ first rest
      convert composed using 1
      all_goals
        simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

def reverse_evalsInTime {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (accumulator output : List Target) :
    EvalsToInTime (TM2.step (program word))
      (reverseCfg accumulator output)
      (some (haltCfg (accumulator.reverse ++ output)))
      (accumulator.length + 1) := by
  induction accumulator generalizing output with
  | nil =>
      simpa using oneStep (step_reverse_nil word output)
  | cons symbol accumulator induction =>
      have first : EvalsToInTime (TM2.step (program word))
          (reverseCfg (symbol :: accumulator) output)
          (some (reverseCfg accumulator (symbol :: output))) 1 :=
        oneStep (step_reverse_cons word symbol accumulator output)
      have rest := induction (symbol :: output)
      have composed := EvalsToInTime.trans _ 1
        (accumulator.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

theorem initList_eq_scanCfg {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (input : List Source) :
    initList (machine Source Target word) input = scanCfg input [] := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some (Label.scan)) none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (output : List Target) :
    haltList (machine Source Target word) output = haltCfg output := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk none none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

def outputsInExactTime {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) (input : List Source) :
    TM2OutputsInTime (machine Source Target word) input
      (some (input.flatMap word))
      (2 * input.length + (input.flatMap word).length + 2) := by
  have scanned := scan_evalsInTime word input []
  have reversed := reverse_evalsInTime word
    (input.flatMap word).reverse []
  have scanned' : EvalsToInTime (TM2.step (program word))
      (scanCfg input [])
      (some (reverseCfg (input.flatMap word).reverse []))
      (2 * input.length + 1) := by
    simpa using scanned
  have composed := EvalsToInTime.trans (TM2.step (program word))
    (2 * input.length + 1) ((input.flatMap word).length + 1)
    (scanCfg input [])
    (reverseCfg (input.flatMap word).reverse [])
    (some (haltCfg (input.flatMap word))) scanned' (by
      simpa using reversed)
  change EvalsToInTime (TM2.step (program word))
    (initList (machine Source Target word) input)
    (some (haltList (machine Source Target word) (input.flatMap word)))
    (2 * input.length + (input.flatMap word).length + 2)
  rw [initList_eq_scanCfg word input, haltList_eq_haltCfg word]
  exact
    { toEvalsTo := composed.toEvalsTo
      steps_le_m := composed.steps_le_m.trans (by omega) }

def wordLengthBound {Source Target : Type} [Fintype Source]
    (word : Source → List Target) : Nat :=
  ∑ symbol, (word symbol).length

theorem word_length_le_bound {Source Target : Type} [Fintype Source]
    (word : Source → List Target) (symbol : Source) :
    (word symbol).length ≤ wordLengthBound word := by
  classical
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (word other).length)
    (Finset.mem_univ symbol)

theorem flatMap_length_le {Source Target : Type} [Fintype Source]
    (word : Source → List Target) (input : List Source) :
    (input.flatMap word).length ≤ input.length * wordLengthBound word := by
  induction input with
  | nil => simp
  | cons symbol input induction =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      calc
        (word symbol).length + (input.flatMap word).length ≤
            wordLengthBound word + input.length * wordLengthBound word :=
          Nat.add_le_add (word_length_le_bound word symbol) induction
        _ = (input.length + 1) * wordLengthBound word := by
          simp [Nat.add_mul, Nat.add_comm]

noncomputable def timePolynomial {Source Target : Type} [Fintype Source]
    (word : Source → List Target) : Polynomial Nat :=
  Polynomial.C (wordLengthBound word + 2) * Polynomial.X +
    Polynomial.C 2

@[simp]
theorem timePolynomial_eval {Source Target : Type} [Fintype Source]
    (word : Source → List Target) (length : Nat) :
    (timePolynomial word).eval length =
      (wordLengthBound word + 2) * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

@[simp]
theorem map_refl_invFun {Symbol : Type} (symbols : List Symbol) :
    symbols.map (Equiv.refl Symbol).invFun = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp only [List.map_cons]
      rw [induction]
      change symbol :: symbols = symbol :: symbols
      rfl

/-- Fixed finite block substitution is computable in polynomial time under
the native list encodings. -/
noncomputable def computableInPolyTime
    {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target]
    (word : Source → List Target) :
    TM2ComputableInPolyTime id id (fun input => input.flatMap word) where
  tm := machine Source Target word
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial word
  outputsFun input := by
    have exact := outputsInExactTime word input
    have exact' : TM2OutputsInTime (machine Source Target word)
        (List.map (Equiv.refl Source).invFun (id input))
        (some (List.map (Equiv.refl Target).invFun
          (id (input.flatMap word))))
        (2 * input.length + (input.flatMap word).length + 2) := by
      simpa only [id_eq, map_refl_invFun] using exact
    refine
      { toEvalsTo := exact'.toEvalsTo
        steps_le_m := exact'.steps_le_m.trans ?_ }
    rw [timePolynomial_eval]
    have outputBound := flatMap_length_le word input
    calc
      2 * input.length + (input.flatMap word).length + 2 ≤
          2 * input.length +
            input.length * wordLengthBound word + 2 := by omega
      _ = (wordLengthBound word + 2) * input.length + 2 := by
        ring

end FiniteBlockTransducer

end LeanTrominoes
