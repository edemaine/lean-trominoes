import LeanTrominoes.PeriodicOneInThreePolarityNormalization
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of periodic exact-one polarity normalization

The occurrence-local complement construction is a finite list transform.
This module records its primitive-recursive implementation independently of
the later geometric choice of subdivision points.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

noncomputable instance polarityNormalizedVariablePrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (PolarityNormalizedVariable Variable) :=
  inferInstance

theorem normalizedPolarity_primrec : Primrec normalizedPolarity := by
  have bounded : Primrec fun index : Nat => decide (2 ≤ index) :=
    (Primrec.nat_le.comp (Primrec.const 2) Primrec.id).decide
  exact bounded.of_eq fun index => by
    cases index with
    | zero => rfl
    | succ index =>
        cases index with
        | zero => rfl
        | succ index => simp [normalizedPolarity]

theorem liftLiteral_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (liftLiteral :
      PeriodicLiteral Variable →
        PeriodicLiteral (PolarityNormalizedVariable Variable)) := by
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      ((Sum.inl literal.atom : PolarityNormalizedVariable Variable),
        literal.offset, literal.value) :=
    Primrec.pair
      (Primrec.sumInl.comp PeriodicThreeCNF.literal_atom_primrec)
      (Primrec.pair PeriodicThreeCNF.literal_offset_primrec
        PeriodicThreeCNF.literal_value_primrec)
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem complementLiteral_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Nat × Nat) × PeriodicLiteral Variable =>
      complementLiteral input.1.1 input.1.2 input.2 := by
  let Input := (Nat × Nat) × PeriodicLiteral Variable
  have atom : Primrec fun input : Input =>
      (Sum.inr (input.1, input.2) :
        PolarityNormalizedVariable Variable) :=
    Primrec.sumInr.comp (Primrec.pair Primrec.fst Primrec.snd)
  have data : Primrec fun input : Input =>
      ((Sum.inr (input.1, input.2) :
          PolarityNormalizedVariable Variable),
        input.2.offset, normalizedPolarity input.1.2) :=
    Primrec.pair atom
      (Primrec.pair
        (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
        (normalizedPolarity_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem normalizeLiteral_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Nat × Nat) × PeriodicLiteral Variable =>
      normalizeLiteral input.1.1 input.1.2 input.2 := by
  let Input := (Nat × Nat) × PeriodicLiteral Variable
  have compatible : PrimrecPred fun input : Input =>
      input.2.value = normalizedPolarity input.1.2 :=
    Primrec.eq.comp
      (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd)
      (normalizedPolarity_primrec.comp
        (Primrec.snd.comp Primrec.fst))
  exact Primrec.ite compatible
    (liftLiteral_primrec.comp Primrec.snd)
    complementLiteral_primrec

theorem originalFalseLiteral_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (originalFalseLiteral :
      PeriodicLiteral Variable →
        PeriodicLiteral (PolarityNormalizedVariable Variable)) := by
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      ((Sum.inl literal.atom : PolarityNormalizedVariable Variable),
        literal.offset, false) :=
    Primrec.pair
      (Primrec.sumInl.comp PeriodicThreeCNF.literal_atom_primrec)
      (Primrec.pair PeriodicThreeCNF.literal_offset_primrec
        (Primrec.const false))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem complementFalseLiteral_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Nat × Nat) × PeriodicLiteral Variable =>
      complementFalseLiteral input.1.1 input.1.2 input.2 := by
  let Input := (Nat × Nat) × PeriodicLiteral Variable
  have atom : Primrec fun input : Input =>
      (Sum.inr (input.1, input.2) :
        PolarityNormalizedVariable Variable) :=
    Primrec.sumInr.comp (Primrec.pair Primrec.fst Primrec.snd)
  have data : Primrec fun input : Input =>
      ((Sum.inr (input.1, input.2) :
          PolarityNormalizedVariable Variable),
        input.2.offset, false) :=
    Primrec.pair atom
      (Primrec.pair
        (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
        (Primrec.const false))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem complementClause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Nat × Nat) × PeriodicLiteral Variable =>
      complementClause input.1.1 input.1.2 input.2 := by
  exact Primrec.list_cons.comp complementFalseLiteral_primrec
    (Primrec.list_cons.comp
      (originalFalseLiteral_primrec.comp Primrec.snd)
      (Primrec.const []))

theorem clauseClauses_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      clauseClauses input.1 input.2 := by
  let Input := Nat × PeriodicClause Variable
  have tagged : Primrec fun input : Input => input.2.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp Primrec.snd
  have normalizedOne : Primrec₂ fun (input : Input)
      (taggedLiteral : PeriodicLiteral Variable × Nat) =>
      normalizeLiteral input.1 taggedLiteral.2 taggedLiteral.1 := by
    change Primrec fun combined :
        Input × (PeriodicLiteral Variable × Nat) =>
      normalizeLiteral combined.1.1 combined.2.2 combined.2.1
    exact normalizeLiteral_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  have normalized : Primrec fun input : Input =>
      normalizeClause input.1 input.2 := by
    simpa [normalizeClause, normalizeClauseFrom] using
      Primrec.list_map tagged normalizedOne
  have complementOne : Primrec₂ fun (input : Input)
      (taggedLiteral : PeriodicLiteral Variable × Nat) =>
      if taggedLiteral.1.value = normalizedPolarity taggedLiteral.2 then
        none
      else
        some (complementClause input.1 taggedLiteral.2 taggedLiteral.1) := by
    change Primrec fun combined :
        Input × (PeriodicLiteral Variable × Nat) =>
      if combined.2.1.value = normalizedPolarity combined.2.2 then
        none
      else
        some (complementClause combined.1.1 combined.2.2 combined.2.1)
    have compatible : PrimrecPred fun combined :
        Input × (PeriodicLiteral Variable × Nat) =>
        combined.2.1.value = normalizedPolarity combined.2.2 :=
      Primrec.eq.comp
        (PeriodicThreeCNF.literal_value_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (normalizedPolarity_primrec.comp
          (Primrec.snd.comp Primrec.snd))
    have clause : Primrec fun combined :
        Input × (PeriodicLiteral Variable × Nat) =>
        complementClause combined.1.1 combined.2.2 combined.2.1 :=
      complementClause_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd))
    exact Primrec.ite compatible (Primrec.const none)
      (Primrec.option_some.comp clause)
  have complements : Primrec fun input : Input =>
      complementClauses input.1 input.2 := by
    simpa [complementClauses, complementClausesFrom] using
      Primrec.listFilterMap tagged complementOne
  exact (Primrec.list_cons.comp normalized complements).of_eq fun _ => rfl

theorem formula_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formula :
      PeriodicCNF Variable →
        PeriodicCNF (PolarityNormalizedVariable Variable)) := by
  have tagged : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have one : Primrec₂ fun (_source : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      clauseClauses taggedClause.2 taggedClause.1 := by
    change Primrec fun combined : PeriodicCNF Variable ×
        (PeriodicClause Variable × Nat) =>
      clauseClauses combined.2.2 combined.2.1
    exact clauseClauses_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx.flatMap fun taggedClause =>
        clauseClauses taggedClause.2 taggedClause.1 :=
    Primrec.list_flatMap tagged one
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq fun _ => rfl

theorem formula_computable
    {Variable : Type*} [Primcodable Variable] :
    Computable (formula :
      PeriodicCNF Variable →
        PeriodicCNF (PolarityNormalizedVariable Variable)) :=
  formula_primrec.to_comp

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
