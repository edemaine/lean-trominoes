import LeanTrominoes.PartrecFiniteEvaluator

/-!
# Polynomial-space certificates for partial-recursive evaluator programs

This file packages the quantitative interface needed to turn a verified
`ToPartrec.Code` decider into the project's explicit `FinTM2` PSPACE model.
The only program-specific space obligation is stated on Mathlib's ambient
four-stack evaluator; finite-label restriction preserves the stacks exactly.
-/

namespace Turing
namespace PartrecToTM2

open Computability
open Relation

/-- Native tape cells occupied by an evaluator-encoded list of naturals. -/
def encodedListSpace (values : List Nat) : Nat :=
  (trList values).length

/-- Native tape cells used to store the data retained by a continuation. -/
def continuationSpace (continuation : ToPartrec.Cont) : Nat :=
  (trContStack continuation).length

/-- Data space at a milestone of the high-level sequential evaluator. -/
def evaluatorCfgSpace : ToPartrec.Cfg → Nat
  | .halt values => encodedListSpace values
  | .ret continuation values =>
      encodedListSpace values + continuationSpace continuation

@[simp]
theorem encodedListSpace_nil :
    encodedListSpace [] = 0 := rfl

@[simp]
theorem encodedListSpace_cons (value : Nat) (values : List Nat) :
    encodedListSpace (value :: values) =
      (encodeNat value).length + 1 + encodedListSpace values := by
  simp only [encodedListSpace, trList, List.length_append,
    List.length_cons,
    LeanTrominoes.Complexity.partrec_trNat_length]
  omega

theorem encodedListSpace_eq_sum (values : List Nat) :
    encodedListSpace values =
      (values.map fun value => (encodeNat value).length + 1).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodedListSpace_cons, ih]
      simp

theorem list_length_le_encodedListSpace (values : List Nat) :
    values.length ≤ encodedListSpace values := by
  induction values with
  | nil => simp
  | cons value values ih =>
      rw [encodedListSpace_cons]
      simp only [List.length_cons]
      omega

theorem trLList_length_eq_sum (values : List (List Nat)) :
    (trLList values).length =
      (values.map fun value => encodedListSpace value + 1).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [trLList, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons, ih,
        encodedListSpace]
      omega

theorem continuationSpace_eq_sum (continuation : ToPartrec.Cont) :
    continuationSpace continuation =
      ((contStack continuation).map
        fun value => encodedListSpace value + 1).sum := by
  rw [continuationSpace, trContStack, trLList_length_eq_sum]

/-- Expanding the four named evaluator stacks computes their total size. -/
theorem stackSpace_elim (label : Option Λ') (state : Option Γ')
    (mainStack reverseStack auxiliaryStack continuationStack : List Γ') :
    TM2.stackSpace
        (TM2.Cfg.mk label state
          (K'.elim mainStack reverseStack auxiliaryStack
            continuationStack)) =
      mainStack.length + reverseStack.length +
        auxiliaryStack.length + continuationStack.length := by
  unfold TM2.stackSpace
  rw [show (Finset.univ : Finset K') =
      {.main, .rev, .aux, .stack} by
    ext index
    cases index <;> simp]
  simp [Nat.add_assoc]

@[simp]
theorem stackSpace_init (code : ToPartrec.Code) (values : List Nat) :
    TM2.stackSpace (init code values) = encodedListSpace values := by
  rw [init, stackSpace_elim]
  simp [encodedListSpace]

@[simp]
theorem stackSpace_halt (values : List Nat) :
    TM2.stackSpace (halt values) = encodedListSpace values := by
  rw [halt, stackSpace_elim]
  simp [encodedListSpace]

/-- At every high-level evaluator milestone, the transcription relation
records exactly the value and continuation data counted by
`evaluatorCfgSpace`. -/
theorem stackSpace_eq_evaluatorCfgSpace_of_TrCfg
    {source : ToPartrec.Cfg} {target : Cfg'}
    (related : TrCfg source target) :
    TM2.stackSpace target = evaluatorCfgSpace source := by
  cases source with
  | halt values =>
      rw [TrCfg] at related
      subst target
      simp [evaluatorCfgSpace]
  | ret continuation values =>
      rw [TrCfg] at related
      obtain ⟨state, rfl⟩ := related
      rw [stackSpace_elim]
      simp [evaluatorCfgSpace, encodedListSpace, continuationSpace]

/-- The typed input encoding length is exactly the initial ambient evaluator
stack space. -/
theorem stackSpace_typed_init
    {α : Type} [Primcodable α] (code : ToPartrec.Code) (input : α) :
    TM2.stackSpace (init code [Encodable.encode input]) =
      ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
        input).length := by
  simp [encodedListSpace,
    LeanTrominoes.Complexity.primcodableFinEncoding]

/-- Erasing a run of the finite evaluator gives a run of Mathlib's ambient
partial-recursive evaluator. -/
theorem erase_finiteEvaluator_reaches (code : ToPartrec.Code)
    {first last : (finiteEvaluator code).Cfg}
    (reaches : ReflTransGen
      (fun before after =>
        after ∈ (finiteEvaluator code).step before)
      first last) :
    ReflTransGen (fun before after => after ∈ TM2.step tr before)
      (TM2.eraseRestrictedCfg first)
      (TM2.eraseRestrictedCfg last) := by
  letI : Inhabited Λ' := ⟨trNormal code Cont'.halt⟩
  unfold finiteEvaluator FinTM2.ofSupported FinTM2.step at reaches
  exact TM2.eraseRestrictedCfg_reaches tr
    (codeSupp code Cont'.halt) (tr_supports code Cont'.halt) reaches

/-- A fixed partial-recursive Boolean decider together with a polynomial
bound on every ambient evaluator configuration reachable on a typed input. -/
structure PolySpaceDecider {α : Type} [Primcodable α]
    (language : α → Prop) where
  code : ToPartrec.Code
  result : α → Bool
  correct : ∀ input, result input = true ↔ language input
  evaluates : ∀ input,
    [Encodable.encode (result input)] ∈
      code.eval [Encodable.encode input]
  space : Polynomial Nat
  space_le :
    ∀ input configuration,
      ReflTransGen (fun before after => after ∈ TM2.step tr before)
          (init code [Encodable.encode input]) configuration →
        TM2.stackSpace configuration ≤
          space.eval
            ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
              input).length

/-- Restricting the certified evaluator program to its finite support turns
an ambient `PolySpaceDecider` into the explicit finite-machine certificate
required by `Complexity.InPSPACE`. -/
noncomputable def PolySpaceDecider.toFiniteDecider
    {α : Type} [Primcodable α] {language : α → Prop}
    (decider : PolySpaceDecider language) :
    LeanTrominoes.Complexity.DeciderInPolySpace
      (LeanTrominoes.Complexity.primcodableFinEncoding α)
      language := by
  refine
    { tm := finiteEvaluator decider.code
      inputAlphabet := finiteEvaluatorInputAlphabet decider.code
      outputAlphabet := finiteEvaluatorOutputAlphabet decider.code
      stackAlphabetFinite := ?_
      result := decider.result
      correct := decider.correct
      outputs := ?_
      space := decider.space
      space_le := ?_ }
  · intro stackIndex
    change Fintype Γ'
    infer_instance
  · intro input
    exact
      (finiteEvaluatorComputable decider.code decider.result
        decider.evaluates).outputsFun input
  · intro input configuration reaches
    have ambientReaches :=
      erase_finiteEvaluator_reaches decider.code reaches
    have ambientFromInit :
        ReflTransGen (fun before after => after ∈ TM2.step tr before)
          (init decider.code [Encodable.encode input])
          (TM2.eraseRestrictedCfg configuration) := by
      have inputTape :
          List.map (finiteEvaluatorInputAlphabet decider.code).invFun
              ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
                input) =
            trList [Encodable.encode input] := by
        calc
          _ = (LeanTrominoes.Complexity.primcodableFinEncoding α).encode
                input :=
            map_finiteEvaluatorInputAlphabet_symm decider.code _
          _ = trList [Encodable.encode input] := rfl
      have erasedInit :
          TM2.eraseRestrictedCfg
              (initList (finiteEvaluator decider.code)
                (List.map
                  (finiteEvaluatorInputAlphabet decider.code).invFun
                  ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
                    input))) =
            init decider.code [Encodable.encode input] := by
        rw [inputTape]
        exact erase_finiteEvaluator_init _ _
      convert ambientReaches using 1
      exact erasedInit.symm
    letI : Fintype (finiteEvaluator decider.code).K :=
      (finiteEvaluator decider.code).kFin
    calc
      LeanTrominoes.Complexity.configurationSpace
          (finiteEvaluator decider.code) configuration =
          TM2.stackSpace configuration := rfl
      _ = TM2.stackSpace
          (TM2.eraseRestrictedCfg configuration) :=
        (TM2.stackSpace_eraseRestrictedCfg configuration).symm
      _ ≤ decider.space.eval
          ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
            input).length :=
        decider.space_le input _ ambientFromInit

/-- The proposition-level PSPACE membership consequence. -/
theorem inPSPACE_of_partrec
    {α : Type} [Primcodable α] {language : α → Prop}
    (decider : PolySpaceDecider language) :
    LeanTrominoes.Complexity.InPSPACE
      (LeanTrominoes.Complexity.primcodableFinEncoding α)
      language :=
  ⟨decider.toFiniteDecider⟩

end PartrecToTM2
end Turing
