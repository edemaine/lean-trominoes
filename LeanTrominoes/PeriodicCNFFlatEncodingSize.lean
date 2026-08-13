import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PeriodicCNFFlatEncoding
import LeanTrominoes.PeriodicCNFTransitionExprBounds
import LeanTrominoes.PeriodicCNFTransitionExprSize

/-!
# Size bounds for the flat periodic-CNF encoding

This file turns structural bounds on a forward-local CNF into a bound on the
actual number of symbols in its flat encoding.  It also records that the
Tseitin transition compiler produces clauses of width at most three and keeps
all atoms below its final fresh boundary.
-/

noncomputable section

namespace LeanTrominoes

open Computability

namespace PeriodicCNFFlatEncoding

/-- Number of literals in a finite periodic CNF presentation. -/
def literalCount (formula : PeriodicCNF Nat) : Nat :=
  (formula.clauses.map List.length).sum

@[simp]
theorem literalFields_length (literal : PeriodicLiteral Nat) :
    (literalFields literal).length = 4 := by
  simp [literalFields]

@[simp]
theorem clauseFields_length (clause : PeriodicClause Nat) :
    (clauseFields clause).length = 1 + 4 * clause.length := by
  have flat : (clause.flatMap literalFields).length = 4 * clause.length := by
    induction clause with
    | nil => rfl
    | cons literal clause ih =>
        simp only [List.flatMap_cons, List.length_append,
          literalFields_length, List.length_cons, ih]
        omega
  simp [clauseFields, flat]
  omega

@[simp]
theorem formulaFields_length (formula : PeriodicCNF Nat) :
    (formulaFields formula).length =
      1 + formula.clauses.length + 4 * literalCount formula := by
  rcases formula with ⟨clauses⟩
  have body : (clauses.flatMap clauseFields).length =
      clauses.length + 4 * (clauses.map List.length).sum := by
    induction clauses with
    | nil => rfl
    | cons clause clauses ih =>
        simp only [List.flatMap_cons, List.length_append,
          clauseFields_length, List.length_cons, List.map_cons,
          List.sum_cons, ih]
        omega
  simp [formulaFields, literalCount, body]
  omega

/-- Encoding every natural field costs at most the field value plus its one
delimiter symbol. -/
theorem encodeNatFields_length_le_sum_add_length (fields : List Nat) :
    (encodeNatFields fields).length ≤ fields.sum + fields.length := by
  rw [encodeNatFields_length]
  induction fields with
  | nil => simp
  | cons field fields ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have bits := Turing.PartrecToTM2.encodeNat_length_le_self field
      omega

/-- Fixed contribution of offsets and polarity to a forward-local literal.
The atom itself is accounted for separately. -/
def forwardLiteralFieldBudget : Nat :=
  max (Encodable.encode (0 : Int)) (Encodable.encode (1 : Int)) +
    Encodable.encode (0 : Int) + 1

theorem literalFields_sum_le {literal : PeriodicLiteral Nat} {atomBound : Nat}
    (forward : literal.IsForwardLocal) (atomLt : literal.atom < atomBound) :
    (literalFields literal).sum ≤ atomBound + forwardLiteralFieldBudget := by
  rcases literal with ⟨atom, ⟨x, y⟩, value⟩
  have atomLe : atom ≤ atomBound := Nat.le_of_lt atomLt
  have valueLe : encodeBoolField value ≤ 1 := by
    cases value <;> simp [encodeBoolField]
  rcases forward with current | next
  · have xEq : x = 0 := by
      simpa using congrArg Prod.fst current
    have yEq : y = 0 := by
      simpa using congrArg Prod.snd current
    subst x
    subst y
    have offsetLe : Encodable.encode (0 : Int) ≤
        max (Encodable.encode (0 : Int)) (Encodable.encode (1 : Int)) :=
      Nat.le_max_left _ _
    simp only [literalFields, List.sum_cons, List.sum_nil, Nat.add_zero]
    unfold forwardLiteralFieldBudget
    omega
  · have xEq : x = 1 := by
      simpa using congrArg Prod.fst next
    have yEq : y = 0 := by
      simpa using congrArg Prod.snd next
    subst x
    subst y
    have offsetLe : Encodable.encode (1 : Int) ≤
        max (Encodable.encode (0 : Int)) (Encodable.encode (1 : Int)) :=
      Nat.le_max_right _ _
    simp only [literalFields, List.sum_cons, List.sum_nil, Nat.add_zero]
    unfold forwardLiteralFieldBudget
    omega

private theorem clauseLiteralFields_sum_le
    (clause : PeriodicClause Nat) (atomBound : Nat)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal)
    (atoms : ∀ literal ∈ clause, literal.atom < atomBound) :
    (clause.flatMap literalFields).sum ≤
      clause.length * (atomBound + forwardLiteralFieldBudget) := by
  induction clause with
  | nil => simp
  | cons literal clause ih =>
      simp only [List.flatMap_cons, List.sum_append, List.length_cons]
      have head := literalFields_sum_le
        (forward literal (by simp)) (atoms literal (by simp))
      have tail := ih
        (fun member memberMem => forward member (by simp [memberMem]))
        (fun member memberMem => atoms member (by simp [memberMem]))
      nlinarith

private theorem clauseFields_sum_le
    (clause : PeriodicClause Nat) (atomBound : Nat)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal)
    (atoms : ∀ literal ∈ clause, literal.atom < atomBound) :
    (clauseFields clause).sum ≤
      clause.length * (atomBound + forwardLiteralFieldBudget + 1) := by
  unfold clauseFields
  simp only [List.sum_cons]
  have literals := clauseLiteralFields_sum_le clause atomBound forward atoms
  nlinarith

private theorem literalCount_le_mul
    (formula : PeriodicCNF Nat) (width : Nat)
    (widthBound : formula.WidthAtMost width) :
    literalCount formula ≤ formula.clauses.length * width := by
  rcases formula with ⟨clauses⟩
  induction clauses with
  | nil => simp [literalCount]
  | cons clause clauses ih =>
      have head : clause.length ≤ width :=
        widthBound clause (by simp)
      have tail : (PeriodicCNF.mk clauses).WidthAtMost width := by
        intro member memberMem
        exact widthBound member (by simp [memberMem])
      have tailBound := ih tail
      change (clauses.map List.length).sum ≤ clauses.length * width
        at tailBound
      simp only [literalCount, List.map_cons, List.sum_cons,
        List.length_cons]
      nlinarith

private theorem formulaFields_sum_le
    (formula : PeriodicCNF Nat) (width atomBound : Nat)
    (widthBound : formula.WidthAtMost width)
    (forward : formula.IsForwardLocal)
    (atoms : PeriodicCNF.ClausesAtomsBelow formula.clauses atomBound) :
    (formulaFields formula).sum ≤
      formula.clauses.length +
        formula.clauses.length * width *
          (atomBound + forwardLiteralFieldBudget + 1) := by
  rcases formula with ⟨clauses⟩
  simp only [formulaFields, List.sum_cons]
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
      have clauseWidth : clause.length ≤ width :=
        widthBound clause (by simp)
      have clauseSum := clauseFields_sum_le clause atomBound
        (fun literal literalMem =>
          forward clause (by simp) literal literalMem)
        (fun literal literalMem =>
          atoms clause (by simp) literal literalMem)
      have tailWidth : (PeriodicCNF.mk clauses).WidthAtMost width := by
        intro member memberMem
        exact widthBound member (by simp [memberMem])
      have tailForward : (PeriodicCNF.mk clauses).IsForwardLocal := by
        intro member memberMem literal literalMem
        exact forward member (by simp [memberMem]) literal literalMem
      have tailAtoms : PeriodicCNF.ClausesAtomsBelow clauses atomBound := by
        intro member memberMem literal literalMem
        exact atoms member (by simp [memberMem]) literal literalMem
      have tailBound := ih tailWidth tailForward tailAtoms
      simp only [List.flatMap_cons, List.sum_append, List.length_cons]
      nlinarith

/-- A width, atom-range, and clause-count certificate bounds the actual flat
encoded length. -/
theorem finEncoding_encode_length_le
    (formula : PeriodicCNF Nat) (width atomBound clauseBound : Nat)
    (widthBound : formula.WidthAtMost width)
    (forward : formula.IsForwardLocal)
    (atoms : PeriodicCNF.ClausesAtomsBelow formula.clauses atomBound)
    (clauses : formula.clauses.length ≤ clauseBound) :
    (finEncoding.encode formula).length ≤
      1 + 2 * clauseBound + clauseBound * width *
        (atomBound + forwardLiteralFieldBudget + 5) := by
  have encoded := encodeNatFields_length_le_sum_add_length
    (formulaFields formula)
  have fieldSum := formulaFields_sum_le formula width atomBound
    widthBound forward atoms
  have literalBound := literalCount_le_mul formula width widthBound
  have fieldLength := formulaFields_length formula
  change (encodeNatFields (formulaFields formula)).length ≤ _
  calc
    (encodeNatFields (formulaFields formula)).length ≤
        (formulaFields formula).sum + (formulaFields formula).length := encoded
    _ ≤ (formula.clauses.length +
          formula.clauses.length * width *
            (atomBound + forwardLiteralFieldBudget + 1)) +
        (1 + formula.clauses.length +
          4 * (formula.clauses.length * width)) := by omega
    _ = 1 + 2 * formula.clauses.length +
        formula.clauses.length * width *
          (atomBound + forwardLiteralFieldBudget + 5) := by ring
    _ ≤ 1 + 2 * clauseBound + clauseBound * width *
        (atomBound + forwardLiteralFieldBudget + 5) := by
      apply Nat.add_le_add
      · exact
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 clauses) 1)
      · simpa [Nat.mul_assoc] using
          (Nat.mul_le_mul_right
            (width * (atomBound + forwardLiteralFieldBudget + 5)) clauses)

end PeriodicCNFFlatEncoding

namespace PeriodicCNF

private theorem constantClauses_widthAtMost_three (output : Nat)
    (value : Bool) :
    ∀ clause ∈ constantClauses output value, clause.length ≤ 3 := by
  simp [constantClauses]

private theorem equalityClauses_widthAtMost_three (output : Nat)
    (input : TransitionWire) :
    ∀ clause ∈ equalityClauses output input, clause.length ≤ 3 := by
  simp [equalityClauses]

private theorem notClauses_widthAtMost_three (output : Nat)
    (input : TransitionWire) :
    ∀ clause ∈ notClauses output input, clause.length ≤ 3 := by
  simp [notClauses]

private theorem andClauses_widthAtMost_three (output : Nat)
    (first second : TransitionWire) :
    ∀ clause ∈ andClauses output first second, clause.length ≤ 3 := by
  simp [andClauses]

private theorem orClauses_widthAtMost_three (output : Nat)
    (first second : TransitionWire) :
    ∀ clause ∈ orClauses output first second, clause.length ≤ 3 := by
  simp [orClauses]

theorem compileTransitionExpr_widthAtMost_three
    (expression : TransitionExpr) (fresh : Nat) :
    ∀ clause ∈ (compileTransitionExpr expression fresh).clauses,
      clause.length ≤ 3 := by
  induction expression generalizing fresh with
  | constant value =>
      exact constantClauses_widthAtMost_three fresh value
  | wire input =>
      exact equalityClauses_widthAtMost_three fresh input
  | not input ih =>
      intro clause clauseMem
      rcases List.mem_append.mp clauseMem with compiled | gate
      · exact ih fresh clause compiled
      · exact notClauses_widthAtMost_three _ _ clause gate
  | and first second firstIH secondIH =>
      intro clause clauseMem
      rcases List.mem_append.mp clauseMem with previous | gate
      · rcases List.mem_append.mp previous with inFirst | inSecond
        · exact firstIH fresh clause inFirst
        · exact secondIH
            (compileTransitionExpr first fresh).nextFresh clause inSecond
      · exact andClauses_widthAtMost_three _ _ _ clause gate
  | or first second firstIH secondIH =>
      intro clause clauseMem
      rcases List.mem_append.mp clauseMem with previous | gate
      · rcases List.mem_append.mp previous with inFirst | inSecond
        · exact firstIH fresh clause inFirst
        · exact secondIH
            (compileTransitionExpr first fresh).nextFresh clause inSecond
      · exact orClauses_widthAtMost_three _ _ _ clause gate

theorem requireTransitionExpr_widthAtMost_three
    (expression : TransitionExpr) (fresh : Nat) :
    (requireTransitionExpr expression fresh).WidthAtMost 3 := by
  intro clause clauseMem
  rcases List.mem_append.mp clauseMem with compiled | root
  · exact compileTransitionExpr_widthAtMost_three expression fresh
      clause compiled
  · exact constantClauses_widthAtMost_three _ true clause root

theorem requireTransitionExpr_atomsBelow
    (expression : TransitionExpr) (fresh : Nat)
    (sourceBound : expression.AtomsBelow fresh) :
    ClausesAtomsBelow (requireTransitionExpr expression fresh).clauses
      (fresh + expression.gateCount) := by
  unfold requireTransitionExpr
  rw [← compileTransitionExpr_nextFresh expression fresh]
  apply clausesAtomsBelow_append
  · exact compileTransitionExpr_atomsBelow expression fresh sourceBound
  · exact constantClauses_atomsBelow
      (compileTransitionExpr_root_lt_nextFresh expression fresh) true

end PeriodicCNF

end LeanTrominoes
