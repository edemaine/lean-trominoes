import LeanTrominoes.PeriodicCNFTransitionExprVectors

/-!
# Requiring a compiled transition expression

The structural Tseitin compiler makes its root equal the direct expression
value but does not itself require that root to be true.  This file appends that
unit clause and proves the resulting forward-local periodic CNF is satisfiable
on the line exactly when the direct Boolean relation has a bi-infinite path.
-/

namespace LeanTrominoes

namespace PeriodicCNF

namespace TransitionExpr

/-- An expression is current-only when none of its wires reads the next
transition endpoint. -/
def CurrentOnly : TransitionExpr → Prop
  | .constant _ => True
  | .wire input => input.slice = .current
  | .not input => input.CurrentOnly
  | .and first second => first.CurrentOnly ∧ second.CurrentOnly
  | .or first second => first.CurrentOnly ∧ second.CurrentOnly

theorem CurrentOnly.eval_eq {expression : TransitionExpr}
    (currentOnly : expression.CurrentOnly)
    (current firstNext secondNext : Nat → Bool) :
    expression.eval current firstNext = expression.eval current secondNext := by
  induction expression with
  | constant value => rfl
  | wire input =>
      cases input with
      | mk slice atom =>
          cases slice <;> simp_all [CurrentOnly, TransitionExpr.eval,
            TransitionWire.value]
  | not input ih =>
      simp only [TransitionExpr.eval]
      rw [ih currentOnly]
  | and first second firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH currentOnly.1, secondIH currentOnly.2]
  | or first second firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH currentOnly.1, secondIH currentOnly.2]

theorem current_currentOnly (atom : Nat) :
    (current atom).CurrentOnly :=
  rfl

theorem CurrentOnly.all {expressions : List TransitionExpr}
    (allCurrent : ∀ expression ∈ expressions, expression.CurrentOnly) :
    (TransitionExpr.all expressions).CurrentOnly := by
  induction expressions with
  | nil => trivial
  | cons expression expressions ih =>
      exact ⟨allCurrent expression (by simp),
        ih (fun member memberMem => allCurrent member (by simp [memberMem]))⟩

theorem CurrentOnly.exactlyOne {expressions : List TransitionExpr}
    (allCurrent : ∀ expression ∈ expressions, expression.CurrentOnly) :
    (TransitionExpr.exactlyOne expressions).CurrentOnly := by
  induction expressions with
  | nil => trivial
  | cons expression expressions ih =>
      have head := allCurrent expression (by simp)
      have tail : ∀ member ∈ expressions, member.CurrentOnly :=
        fun member memberMem => allCurrent member (by simp [memberMem])
      exact ⟨⟨head, CurrentOnly.all (by
        intro negated negatedMem
        obtain ⟨member, memberMem, rfl⟩ := List.mem_map.mp negatedMem
        exact tail member memberMem)⟩,
        head, ih tail⟩

theorem currentExactlyOne_currentOnly (atoms : List Nat) :
    (currentExactlyOne atoms).CurrentOnly := by
  apply CurrentOnly.exactlyOne
  intro expression expressionMem
  obtain ⟨atom, _, rfl⟩ := List.mem_map.mp expressionMem
  exact current_currentOnly atom

end TransitionExpr

/-- Compile a transition expression and require its edge-local root to be
true at every translate. -/
def requireTransitionExpr (expression : TransitionExpr) (fresh : Nat) :
    PeriodicCNF Nat where
  clauses := (compileTransitionExpr expression fresh).clauses ++
    constantClauses (compileTransitionExpr expression fresh).root true

/-- Only atoms read at the next endpoint need to remain below `bound`; gate
outputs are edge-local current atoms. -/
def ClausesNextAtomsBelow (clauses : List (PeriodicClause Nat))
    (bound : Nat) : Prop :=
  ∀ clause ∈ clauses, ∀ literal ∈ clause,
    literal.offset = (1, 0) → literal.atom < bound

private theorem clausesNextAtomsBelow_append
    {first second : List (PeriodicClause Nat)} {bound : Nat}
    (firstBound : ClausesNextAtomsBelow first bound)
    (secondBound : ClausesNextAtomsBelow second bound) :
    ClausesNextAtomsBelow (first ++ second) bound := by
  intro clause clauseMem literal literalMem nextOffset
  rcases List.mem_append.mp clauseMem with inFirst | inSecond
  · exact firstBound clause inFirst literal literalMem nextOffset
  · exact secondBound clause inSecond literal literalMem nextOffset

private theorem constantClauses_nextAtomsBelow (output bound : Nat)
    (value : Bool) :
    ClausesNextAtomsBelow (constantClauses output value) bound := by
  simp [ClausesNextAtomsBelow, constantClauses, gateOutput,
    TransitionWire.literal]

private theorem equalityClauses_nextAtomsBelow (output bound : Nat)
    (input : TransitionWire) (inputBound : input.atom < bound) :
    ClausesNextAtomsBelow (equalityClauses output input) bound := by
  cases input with
  | mk slice atom =>
      cases slice <;>
        simp [ClausesNextAtomsBelow, equalityClauses, gateOutput,
          TransitionWire.literal, inputBound]

private theorem notClauses_nextAtomsBelow (output input bound : Nat) :
    ClausesNextAtomsBelow
      (notClauses output (gateOutput input)) bound := by
  simp [ClausesNextAtomsBelow, notClauses, gateOutput,
    TransitionWire.literal]

private theorem andClauses_nextAtomsBelow
    (output first second bound : Nat) :
    ClausesNextAtomsBelow
      (andClauses output (gateOutput first) (gateOutput second)) bound := by
  simp [ClausesNextAtomsBelow, andClauses, gateOutput,
    TransitionWire.literal]

private theorem orClauses_nextAtomsBelow
    (output first second bound : Nat) :
    ClausesNextAtomsBelow
      (orClauses output (gateOutput first) (gateOutput second)) bound := by
  simp [ClausesNextAtomsBelow, orClauses, gateOutput,
    TransitionWire.literal]

private theorem compileTransitionExpr_nextAtomsBelow_at
    (expression : TransitionExpr) (compileFresh sourceBound : Nat)
    (atoms : expression.AtomsBelow sourceBound) :
    ClausesNextAtomsBelow
      (compileTransitionExpr expression compileFresh).clauses sourceBound := by
  induction expression generalizing compileFresh with
  | constant value =>
      exact constantClauses_nextAtomsBelow compileFresh sourceBound value
  | wire input =>
      exact equalityClauses_nextAtomsBelow compileFresh sourceBound input atoms
  | not input ih =>
      simp only [compileTransitionExpr]
      exact clausesNextAtomsBelow_append (ih compileFresh atoms)
        (notClauses_nextAtomsBelow _ _ _)
  | and first second firstIH secondIH =>
      simp only [compileTransitionExpr]
      apply clausesNextAtomsBelow_append
      · apply clausesNextAtomsBelow_append
        · exact firstIH compileFresh atoms.1
        · exact secondIH
            (compileTransitionExpr first compileFresh).nextFresh atoms.2
      · exact andClauses_nextAtomsBelow _ _ _ _
  | or first second firstIH secondIH =>
      simp only [compileTransitionExpr]
      apply clausesNextAtomsBelow_append
      · apply clausesNextAtomsBelow_append
        · exact firstIH compileFresh atoms.1
        · exact secondIH
            (compileTransitionExpr first compileFresh).nextFresh atoms.2
      · exact orClauses_nextAtomsBelow _ _ _ _

/-- Compiled clauses read the next endpoint only through original source
atoms, never through generated gate atoms. -/
theorem compileTransitionExpr_nextAtomsBelow (expression : TransitionExpr)
    (fresh : Nat) (sourceBound : expression.AtomsBelow fresh) :
    ClausesNextAtomsBelow
      (compileTransitionExpr expression fresh).clauses fresh :=
  compileTransitionExpr_nextAtomsBelow_at expression fresh fresh sourceBound

private theorem literal_holdsBetween_congr_next
    {bound : Nat} {current first second : Nat → Bool}
    {literal : PeriodicLiteral Nat}
    (nextBound : literal.offset = (1, 0) → literal.atom < bound)
    (agree : ∀ atom < bound, first atom = second atom) :
    literal.HoldsBetween current first ↔
      literal.HoldsBetween current second := by
  constructor
  · rintro (⟨offset, value⟩ | ⟨offset, value⟩)
    · exact Or.inl ⟨offset, value⟩
    · exact Or.inr ⟨offset, by
        simpa [agree literal.atom (nextBound offset)] using value⟩
  · rintro (⟨offset, value⟩ | ⟨offset, value⟩)
    · exact Or.inl ⟨offset, value⟩
    · exact Or.inr ⟨offset, by
        simpa [agree literal.atom (nextBound offset)] using value⟩

/-- Clause satisfaction is stable when next-endpoint values agree below the
source-atom bound. -/
theorem clausesHoldBetween_congr_next
    {clauses : List (PeriodicClause Nat)} {bound : Nat}
    (atoms : ClausesNextAtomsBelow clauses bound)
    {current first second : Nat → Bool}
    (agree : ∀ atom < bound, first atom = second atom) :
    ClausesHoldBetween current first clauses ↔
      ClausesHoldBetween current second clauses := by
  constructor
  · intro holds clause clauseMem
    obtain ⟨literal, literalMem, literalHolds⟩ := holds clause clauseMem
    exact ⟨literal, literalMem,
      (literal_holdsBetween_congr_next
        (atoms clause clauseMem literal literalMem) agree).mp literalHolds⟩
  · intro holds clause clauseMem
    obtain ⟨literal, literalMem, literalHolds⟩ := holds clause clauseMem
    exact ⟨literal, literalMem,
      (literal_holdsBetween_congr_next
        (atoms clause clauseMem literal literalMem) agree).mpr literalHolds⟩

/-- Expression evaluation is unchanged when next-slice source atoms agree
below their declared bound. -/
theorem TransitionExpr.eval_congr_next {expression : TransitionExpr}
    {bound : Nat} (atoms : expression.AtomsBelow bound)
    {current first second : Nat → Bool}
    (agree : ∀ atom < bound, first atom = second atom) :
    expression.eval current first = expression.eval current second := by
  induction expression with
  | constant value => rfl
  | wire input =>
      cases input with
      | mk slice atom =>
          cases slice with
          | current => rfl
          | next => exact agree atom atoms
  | not input ih =>
      simp only [TransitionExpr.eval]
      rw [ih atoms]
  | and firstExpr secondExpr firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH atoms.1, secondIH atoms.2]
  | or firstExpr secondExpr firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH atoms.1, secondIH atoms.2]

/-- Requiring a compiled expression preserves the forward-local fragment. -/
theorem requireTransitionExpr_forward (expression : TransitionExpr)
    (fresh : Nat) :
    (requireTransitionExpr expression fresh).IsForwardLocal := by
  intro clause clauseMem literal literalMem
  rw [requireTransitionExpr, List.mem_append] at clauseMem
  rcases clauseMem with compiled | forced
  · exact compileTransitionExpr_forward expression fresh
      clause compiled literal literalMem
  · exact constantClauses_forward
      (compileTransitionExpr expression fresh).root true
      clause forced literal literalMem

/-- Every transition of the required CNF makes the direct source expression
true. -/
theorem requireTransitionExpr_transition_sound
    (expression : TransitionExpr) (fresh : Nat)
    {current next : Nat → Bool}
    (transition :
      (requireTransitionExpr expression fresh).Transition current next) :
    expression.eval current next = true := by
  change ClausesHoldBetween current next
    ((compileTransitionExpr expression fresh).clauses ++
      constantClauses (compileTransitionExpr expression fresh).root true)
    at transition
  have parts := (clausesHoldBetween_append_iff current next _ _).mp transition
  have rootValue := compileTransitionExpr_sound expression fresh current next
    parts.1
  have rootTrue := (constantClauses_hold_iff
    (compileTransitionExpr expression fresh).root true current next).mp parts.2
  rwa [rootValue] at rootTrue

/-- Whenever the direct source expression is true, generated current-slice
gate values can be chosen without changing any source atom. -/
theorem requireTransitionExpr_transition_complete
    (expression : TransitionExpr) (fresh : Nat)
    {current next : Nat → Bool}
    (sourceBound : expression.AtomsBelow fresh)
    (truth : expression.eval current next = true) :
    ∃ realized : Nat → Bool,
      (∀ atom < fresh, realized atom = current atom) ∧
        (requireTransitionExpr expression fresh).Transition realized next := by
  obtain ⟨realized, preserves, holds, rootValue⟩ :=
    compileTransitionExpr_complete expression fresh current next sourceBound
  refine ⟨realized, preserves, ?_⟩
  change ClausesHoldBetween realized next
    ((compileTransitionExpr expression fresh).clauses ++
      constantClauses (compileTransitionExpr expression fresh).root true)
  apply (clausesHoldBetween_append_iff realized next _ _).mpr
  refine ⟨holds, (constantClauses_hold_iff _ true realized next).mpr ?_⟩
  exact rootValue.trans truth

/-- The required forward-local formula is satisfiable on the line exactly
when the direct Boolean transition relation has a bi-infinite path. -/
theorem requireTransitionExpr_satisfiableOnLine_iff
    (expression : TransitionExpr) (fresh : Nat)
    (sourceBound : expression.AtomsBelow fresh) :
    (requireTransitionExpr expression fresh).SatisfiableOnLine ↔
      FiniteState.HasBiInfinitePath
        (fun current next => expression.eval current next = true) := by
  constructor
  · intro satisfiable
    obtain ⟨states, follows⟩ :=
      (satisfiableOnLine_iff_hasBiInfinitePath
        (requireTransitionExpr_forward expression fresh)).mp satisfiable
    exact ⟨states, fun index =>
      requireTransitionExpr_transition_sound expression fresh
        (follows index)⟩
  · rintro ⟨sourceStates, sourceFollows⟩
    let realizedStates : Int → Nat → Bool := fun index =>
      realizeTransitionExpr expression fresh (sourceStates index)
        (sourceStates (index + 1))
    have preserves (index : Int) :
        ∀ atom < fresh,
          realizedStates index atom = sourceStates index atom := by
      intro atom atomLt
      exact realizeTransitionExpr_preserves expression fresh
        (sourceStates index) (sourceStates (index + 1)) atomLt
    apply (satisfiableOnLine_iff_hasBiInfinitePath
      (requireTransitionExpr_forward expression fresh)).mpr
    refine ⟨realizedStates, ?_⟩
    intro index
    have direct := sourceFollows index
    change (requireTransitionExpr expression fresh).Transition
      (realizedStates index) (realizedStates (index + 1))
    change ClausesHoldBetween (realizedStates index) (realizedStates (index + 1))
      ((compileTransitionExpr expression fresh).clauses ++
        constantClauses (compileTransitionExpr expression fresh).root true)
    have compiledNextBound := compileTransitionExpr_nextAtomsBelow
      expression fresh sourceBound
    have forcedNextBound := constantClauses_nextAtomsBelow
      (compileTransitionExpr expression fresh).root fresh true
    apply (clausesHoldBetween_congr_next
      (clausesNextAtomsBelow_append compiledNextBound forcedNextBound)
      (preserves (index + 1))).mpr
    apply (clausesHoldBetween_append_iff _ _ _ _).mpr
    refine ⟨realizeTransitionExpr_holds expression fresh
      (sourceStates index) (sourceStates (index + 1)) sourceBound, ?_⟩
    apply (constantClauses_hold_iff _ true _ _).mpr
    exact (realizeTransitionExpr_root expression fresh
      (sourceStates index) (sourceStates (index + 1))).trans direct

end PeriodicCNF

end LeanTrominoes
