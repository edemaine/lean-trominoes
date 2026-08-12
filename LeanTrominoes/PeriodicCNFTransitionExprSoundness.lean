import LeanTrominoes.PeriodicCNFTransitionExpr

/-!
# Soundness of transition-expression compilation

Every satisfying assignment of the generated Tseitin clauses gives the root
atom exactly the direct Boolean value of the source transition expression.
-/

namespace LeanTrominoes

namespace PeriodicCNF

@[simp]
theorem clausesHoldBetween_append_iff (current next : Nat → Bool)
    (first second : List (PeriodicClause Nat)) :
    ClausesHoldBetween current next (first ++ second) ↔
      ClausesHoldBetween current next first ∧
        ClausesHoldBetween current next second := by
  simp only [ClausesHoldBetween, List.mem_append]
  aesop

/-- Satisfying the compiled clauses forces the root atom to equal direct
expression evaluation. -/
theorem compileTransitionExpr_sound (expression : TransitionExpr)
    (fresh : Nat) (current next : Nat → Bool)
    (holds : ClausesHoldBetween current next
      (compileTransitionExpr expression fresh).clauses) :
    current (compileTransitionExpr expression fresh).root =
      expression.eval current next := by
  induction expression generalizing fresh with
  | constant value =>
      simpa [compileTransitionExpr, TransitionExpr.eval] using
        (constantClauses_hold_iff fresh value current next).mp holds
  | wire input =>
      simpa [compileTransitionExpr, TransitionExpr.eval] using
        (equalityClauses_hold_iff fresh input current next).mp holds
  | not input ih =>
      let compiled := compileTransitionExpr input fresh
      have parts := (clausesHoldBetween_append_iff current next
        compiled.clauses
        (notClauses compiled.nextFresh (gateOutput compiled.root))).mp
        (by simpa [compileTransitionExpr, compiled] using holds)
      have inputValue := ih fresh parts.1
      have gateValue :=
        (notClauses_hold_iff compiled.nextFresh
          (gateOutput compiled.root) current next).mp parts.2
      simpa [compileTransitionExpr, TransitionExpr.eval, compiled,
        inputValue] using gateValue
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have outer := (clausesHoldBetween_append_iff current next
        (firstCompiled.clauses ++ secondCompiled.clauses)
        (andClauses secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root))).mp
        (by simpa [compileTransitionExpr, firstCompiled, secondCompiled]
          using holds)
      have inner := (clausesHoldBetween_append_iff current next
        firstCompiled.clauses secondCompiled.clauses).mp outer.1
      have firstValue := firstIH fresh inner.1
      have secondValue := secondIH firstCompiled.nextFresh inner.2
      have firstValue' : current firstCompiled.root =
          first.eval current next := by
        simpa [firstCompiled] using firstValue
      have secondValue' : current secondCompiled.root =
          second.eval current next := by
        simpa [secondCompiled] using secondValue
      have gateValue :=
        (andClauses_hold_iff secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root) current next).mp outer.2
      simp only [gateOutput_value] at gateValue
      rw [firstValue', secondValue'] at gateValue
      simpa [compileTransitionExpr, TransitionExpr.eval,
        firstCompiled, secondCompiled] using gateValue
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have outer := (clausesHoldBetween_append_iff current next
        (firstCompiled.clauses ++ secondCompiled.clauses)
        (orClauses secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root))).mp
        (by simpa [compileTransitionExpr, firstCompiled, secondCompiled]
          using holds)
      have inner := (clausesHoldBetween_append_iff current next
        firstCompiled.clauses secondCompiled.clauses).mp outer.1
      have firstValue := firstIH fresh inner.1
      have secondValue := secondIH firstCompiled.nextFresh inner.2
      have firstValue' : current firstCompiled.root =
          first.eval current next := by
        simpa [firstCompiled] using firstValue
      have secondValue' : current secondCompiled.root =
          second.eval current next := by
        simpa [secondCompiled] using secondValue
      have gateValue :=
        (orClauses_hold_iff secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root) current next).mp outer.2
      simp only [gateOutput_value] at gateValue
      rw [firstValue', secondValue'] at gateValue
      simpa [compileTransitionExpr, TransitionExpr.eval,
        firstCompiled, secondCompiled] using gateValue

end PeriodicCNF

end LeanTrominoes
