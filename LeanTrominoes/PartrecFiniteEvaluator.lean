import LeanTrominoes.FiniteTMCompiler

/-!
# A finite-label partial-recursive evaluator

Mathlib proves correctness of `PartrecToTM2.tr`, a four-stack evaluator for
partial-recursive codes, and proves that a fixed code reaches only the finite
set `codeSupp code halt`.  This file applies the finite-label compiler to that
certificate.
-/

namespace Turing
namespace PartrecToTM2

instance : Fintype K' :=
  Fintype.ofList [.main, .rev, .aux, .stack] (by
    intro index
    cases index <;> simp)

/-- The universal evaluator restricted to the finite labels reachable for one
fixed partial-recursive code.  Its input and output are Mathlib's `trList`
encoding on the evaluator's main stack. -/
noncomputable def finiteEvaluator (code : ToPartrec.Code) : FinTM2 := by
  letI : Inhabited Λ' := ⟨trNormal code Cont'.halt⟩
  exact FinTM2.ofSupported .main .main (fun _ : K' => Γ')
    none tr (codeSupp code Cont'.halt) (tr_supports code Cont'.halt)

theorem erase_finiteEvaluator_init (code : ToPartrec.Code)
    (input : List Nat) :
    TM2.eraseRestrictedCfg
        (initList (finiteEvaluator code) (trList input)) =
      init code input := by
  unfold finiteEvaluator FinTM2.ofSupported initList
    TM2.eraseRestrictedCfg init
  congr 1
  funext stackIndex
  cases stackIndex <;> rfl

theorem erase_finiteEvaluator_halt (code : ToPartrec.Code)
    (output : List Nat) :
    TM2.eraseRestrictedCfg
        (haltList (finiteEvaluator code) (trList output)) =
      halt output := by
  unfold finiteEvaluator FinTM2.ofSupported haltList
    TM2.eraseRestrictedCfg halt
  congr 1
  funext stackIndex
  cases stackIndex <;> rfl

/-- The finite evaluator inherits Mathlib's correctness theorem for the
ambient partial-recursive evaluator.  `Nonempty` hides the concrete number of
steps, which is forgotten by the proposition-valued support simulation. -/
theorem nonempty_finiteEvaluator_outputs {code : ToPartrec.Code}
    {input output : List Nat}
    (evaluates : output ∈ ToPartrec.Code.eval code input) :
    Nonempty (TM2Outputs (finiteEvaluator code) (trList input)
      (some (trList output))) := by
  letI : Inhabited Λ' := ⟨trNormal code Cont'.halt⟩
  have ambientEval :
      halt output ∈
        StateTransition.eval (TM2.step tr) (init code input) := by
    rw [tr_eval]
    exact (Part.mem_map_iff _).2 ⟨output, evaluates, rfl⟩
  have ambientReaches :=
    (StateTransition.mem_eval.mp ambientEval).1
  have initialWithin :
      (init code input).l ∈
        Finset.insertNone (codeSupp code Cont'.halt) := by
    exact Finset.some_mem_insertNone.mpr
      (tr_supports code Cont'.halt).1
  obtain ⟨haltWithin, restrictedReaches⟩ :=
    TM2.restrictCfg_reaches tr (codeSupp code Cont'.halt)
      (tr_supports code Cont'.halt) initialWithin ambientReaches
  have restrictedInit :
      TM2.restrictCfg (codeSupp code Cont'.halt)
          (init code input) initialWithin =
        initList (finiteEvaluator code) (trList input) := by
    apply TM2.eraseRestrictedCfg_injective
    rw [TM2.eraseRestrictedCfg_restrictCfg]
    unfold finiteEvaluator FinTM2.ofSupported initList
      TM2.eraseRestrictedCfg init
    congr 1
    funext stackIndex
    cases stackIndex <;> rfl
  have restrictedHalt :
      TM2.restrictCfg (codeSupp code Cont'.halt)
          (halt output) haltWithin =
        haltList (finiteEvaluator code) (trList output) := by
    apply TM2.eraseRestrictedCfg_injective
    rw [TM2.eraseRestrictedCfg_restrictCfg]
    unfold finiteEvaluator FinTM2.ofSupported haltList
      TM2.eraseRestrictedCfg halt
    congr 1
    funext stackIndex
    cases stackIndex <;> rfl
  rw [restrictedInit, restrictedHalt] at restrictedReaches
  exact Turing.nonempty_evalsTo_of_reaches restrictedReaches

/-- Select the step count hidden by
`nonempty_finiteEvaluator_outputs`. -/
noncomputable def finiteEvaluator_outputs {code : ToPartrec.Code}
    {input output : List Nat}
    (evaluates : output ∈ ToPartrec.Code.eval code input) :
    TM2Outputs (finiteEvaluator code) (trList input)
      (some (trList output)) :=
  Classical.choice (nonempty_finiteEvaluator_outputs evaluates)

/-- Package any total function represented by a partial-recursive code as a
finite Turing machine using the evaluator-native finite encodings. -/
noncomputable def finiteEvaluatorComputable
    {α β : Type} [Primcodable α] [Primcodable β]
    (code : ToPartrec.Code) (function : α → β)
    (computes : ∀ input,
      [Encodable.encode (function input)] ∈
        ToPartrec.Code.eval code [Encodable.encode input]) :
    TM2Computable
      (LeanTrominoes.Complexity.primcodableFinEncoding α).encode
      (LeanTrominoes.Complexity.primcodableFinEncoding β).encode
      function where
  tm := finiteEvaluator code
  inputAlphabet := by
    unfold finiteEvaluator FinTM2.ofSupported
    exact Equiv.refl _
  outputAlphabet := by
    unfold finiteEvaluator FinTM2.ofSupported
    exact Equiv.refl _
  outputsFun input := by
    unfold finiteEvaluator FinTM2.ofSupported
    simp only [LeanTrominoes.Complexity.primcodableFinEncoding,
      id_eq]
    have mapRefl (values : List Γ') :
        List.map (Equiv.refl Γ').invFun values = values := by
      induction values with
      | nil => rfl
      | cons head tail ih =>
          change head :: List.map (Equiv.refl Γ').invFun tail =
            head :: tail
          rw [ih]
    rw [mapRefl, mapRefl]
    simpa only [finiteEvaluator, FinTM2.ofSupported] using
      finiteEvaluator_outputs (computes input)

/-- Total natural-number realization of a typed function, with an arbitrary
default on natural numbers that do not decode as inputs. -/
def encodedFunction {α β : Type} [Primcodable α] [Primcodable β]
    [Inhabited α] (function : α → β) (inputCode : Nat) : Nat :=
  Encodable.encode
    (function ((Encodable.decode (α := α) inputCode).getD default))

theorem encodedFunction_primrec
    {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α]
    {function : α → β} (primrec : Primrec function) :
    Nat.Primrec (encodedFunction function) := by
  apply Primrec.nat_iff.mp
  exact Primrec.encode.comp
    (primrec.comp
      (Primrec.option_getD_default.comp Primrec.decode))

/-- Extract a unary `ToPartrec.Code` for any typed primitive-recursive
function.  On valid encoded inputs it returns the encoded typed output. -/
theorem exists_code_of_primrec
    {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α]
    (function : α → β) (primrec : Primrec function) :
    ∃ code : ToPartrec.Code,
      ∀ input : α,
        code.eval [Encodable.encode input] =
          pure [Encodable.encode (function input)] := by
  have vectorPrimrec :
    Nat.Primrec'
        (fun values : List.Vector Nat 1 =>
          encodedFunction function values.head) :=
    Nat.Primrec'.prim_iff₁.mpr
      (Primrec.nat_iff.mpr (encodedFunction_primrec primrec))
  have partialRecursive :
      Nat.Partrec'
        (fun values : List.Vector Nat 1 =>
          encodedFunction function values.head) :=
    Nat.Partrec'.prim vectorPrimrec
  obtain ⟨code, codeCorrect⟩ :=
    ToPartrec.Code.exists_code partialRecursive
  refine ⟨code, fun input => ?_⟩
  let encodedInput : List.Vector Nat 1 :=
    ⟨[Encodable.encode input], rfl⟩
  have correctness := codeCorrect encodedInput
  change code.eval [Encodable.encode input] =
    pure [encodedFunction function (Encodable.encode input)] at correctness
  simpa [encodedInput, encodedFunction] using correctness

/-- A chosen partial-recursive program representing `function`. -/
noncomputable def codeOfPrimrec
    {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α]
    (function : α → β) (primrec : Primrec function) :
    ToPartrec.Code :=
  Classical.choose (exists_code_of_primrec function primrec)

theorem codeOfPrimrec_eval
    {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α]
    (function : α → β) (primrec : Primrec function) (input : α) :
    [Encodable.encode (function input)] ∈
      (codeOfPrimrec function primrec).eval
        [Encodable.encode input] := by
  unfold codeOfPrimrec
  have correctness :=
    Classical.choose_spec (exists_code_of_primrec function primrec)
  rw [correctness input]
  exact Part.mem_some _

/-- Compile a typed primitive-recursive function all the way to a finite
four-stack Turing machine with the project's standard finite encodings. -/
noncomputable def primrecFiniteEvaluatorComputable
    {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α]
    (function : α → β) (primrec : Primrec function) :
    TM2Computable
      (LeanTrominoes.Complexity.primcodableFinEncoding α).encode
      (LeanTrominoes.Complexity.primcodableFinEncoding β).encode
      function :=
  finiteEvaluatorComputable (codeOfPrimrec function primrec)
    function (codeOfPrimrec_eval function primrec)

end PartrecToTM2
end Turing
