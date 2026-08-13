import LeanTrominoes.PeriodicCNFMachineSize

/-!
# Size bounds for finite TM2 statement expansion

The bounded-machine compiler symbolically expands one atomic TM2 statement.
This file gives syntax-directed machine constants for the number of terminal
paths and for the largest guard on any such path.  In particular, neither
constant depends on the represented stack width or reset-clock width.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

private theorem sum_le_length_mul (values : List Nat) (bound : Nat)
    (bounded : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      calc
        value + values.sum ≤ bound + values.length * bound :=
          Nat.add_le_add (bounded value (by simp))
            (ih (fun member memberMem => bounded member (by simp [memberMem])))
        _ = (values.length + 1) * bound := by ring

/-- A machine-syntax bound for the number of terminal symbolic paths through
one atomic statement.  An unknown stack observation contributes only its
fixed optional-alphabet cardinality. -/
def statementPathCountBudget :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | .push _ _ next => statementPathCountBudget next
  | .peek stackIndex _ next =>
      Fintype.card (Option (tm.Γ stackIndex)) * statementPathCountBudget next
  | .pop stackIndex _ next =>
      Fintype.card (Option (tm.Γ stackIndex)) * statementPathCountBudget next
  | .load _ next => statementPathCountBudget next
  | .branch _ yes no =>
      max (statementPathCountBudget yes) (statementPathCountBudget no)
  | .goto _ => 1
  | .halt => 1

/-- Maximum number of still-unknown stack observations along one syntactic
branch of an atomic statement. -/
def statementObservationDepth :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | .push _ _ next => statementObservationDepth next
  | .peek _ _ next => statementObservationDepth next + 1
  | .pop _ _ next => statementObservationDepth next + 1
  | .load _ next => statementObservationDepth next
  | .branch _ yes no =>
      max (statementObservationDepth yes) (statementObservationDepth no)
  | .goto _ => 0
  | .halt => 0

/-- Symbolic execution produces no more paths than its fixed syntactic
branching budget. -/
theorem statementPaths_length_le
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (statementPaths (space := space) (clockBits := clockBits)
      statement control transforms).length ≤
      statementPathCountBudget statement := by
  classical
  induction statement generalizing control transforms with
  | push stack write next ih =>
      exact ih control
        (Function.update transforms stack
          ((transforms stack).push (write control)))
  | peek stack read next ih =>
      simp only [statementPaths]
      split
      · change _ ≤ Fintype.card (Option (tm.Γ stack)) *
          statementPathCountBudget next
        calc
          _ ≤ statementPathCountBudget next := ih _ _
          _ = 1 * statementPathCountBudget next := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (by
          have positive : 1 ≤ Fintype.card (Option (tm.Γ stack)) := by simp
          exact positive)
      · split
        · rw [List.length_flatMap]
          simp only [List.length_map]
          have sumBound := sum_le_length_mul
            ((finiteValues (Option (tm.Γ stack))).map fun observed =>
              (statementPaths (space := space) (clockBits := clockBits)
                next (read control observed) transforms).length)
            (statementPathCountBudget next) (by
              intro count countMem
              obtain ⟨observed, _, rfl⟩ := List.mem_map.mp countMem
              exact ih (read control observed) transforms)
          change _ ≤ Fintype.card (Option (tm.Γ stack)) *
            statementPathCountBudget next
          simpa only [List.length_map, finiteValues_length] using sumBound
        · change _ ≤ Fintype.card (Option (tm.Γ stack)) *
            statementPathCountBudget next
          calc
            _ ≤ statementPathCountBudget next := ih _ _
            _ = 1 * statementPathCountBudget next := by simp
            _ ≤ _ := Nat.mul_le_mul_right _ (by
            have positive : 1 ≤ Fintype.card (Option (tm.Γ stack)) := by simp
            exact positive)
  | pop stack read next ih =>
      simp only [statementPaths]
      split
      · change _ ≤ Fintype.card (Option (tm.Γ stack)) *
          statementPathCountBudget next
        calc
          _ ≤ statementPathCountBudget next := ih _ _
          _ = 1 * statementPathCountBudget next := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (by
          have positive : 1 ≤ Fintype.card (Option (tm.Γ stack)) := by simp
          exact positive)
      · split
        · rw [List.length_flatMap]
          simp only [List.length_map]
          have sumBound := sum_le_length_mul
            ((finiteValues (Option (tm.Γ stack))).map fun observed =>
              (statementPaths (space := space) (clockBits := clockBits)
                next (read control observed)
                  (Function.update transforms stack
                    (transforms stack).pop)).length)
            (statementPathCountBudget next) (by
              intro count countMem
              obtain ⟨observed, _, rfl⟩ := List.mem_map.mp countMem
              exact ih (read control observed)
                (Function.update transforms stack (transforms stack).pop))
          change _ ≤ Fintype.card (Option (tm.Γ stack)) *
            statementPathCountBudget next
          simpa only [List.length_map, finiteValues_length] using sumBound
        · change _ ≤ Fintype.card (Option (tm.Γ stack)) *
            statementPathCountBudget next
          calc
            _ ≤ statementPathCountBudget next := ih _ _
            _ = 1 * statementPathCountBudget next := by simp
            _ ≤ _ := Nat.mul_le_mul_right _ (by
            have positive : 1 ≤ Fintype.card (Option (tm.Γ stack)) := by simp
            exact positive)
  | load update next ih =>
      exact ih (update control) transforms
  | branch test yes no yesIH noIH =>
      simp only [statementPaths]
      split
      · exact (yesIH _ _).trans (Nat.le_max_left _ _)
      · exact (noIH _ _).trans (Nat.le_max_right _ _)
  | goto target => simp [statementPaths, statementPathCountBudget]
  | halt => simp [statementPaths, statementPathCountBudget]

/-- Every generated guard has one constant leaf plus at most two expression
nodes for each unknown stack observation encountered on its path. -/
theorem statementPaths_guard_gateCount_le
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (path : StatementPath tm space clockBits)
    (pathMem : path ∈ statementPaths (space := space)
      (clockBits := clockBits) statement control transforms) :
    path.guard.gateCount ≤ 2 * statementObservationDepth statement + 1 := by
  classical
  induction statement generalizing control transforms path with
  | push stack write next ih =>
      exact ih control
        (Function.update transforms stack
          ((transforms stack).push (write control))) path pathMem
  | peek stack read next ih =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact (ih _ _ _ pathMem).trans (by
          simp only [statementObservationDepth]
          omega)
      · split at pathMem
        · rw [List.mem_flatMap] at pathMem
          obtain ⟨observed, _, pathMem⟩ := pathMem
          obtain ⟨sourcePath, sourceMem, rfl⟩ := List.mem_map.mp pathMem
          have sourceBound := ih _ _ _ sourceMem
          simp only [StatementPath.andGuard, TransitionExpr.gateCount]
          rw [show
            (currentStackCellIs (tm := tm) (clockBits := clockBits)
              stack _ observed).gateCount = 1 by rfl]
          simp only [statementObservationDepth]
          omega
        · exact (ih _ _ _ pathMem).trans (by
            simp only [statementObservationDepth]
            omega)
  | pop stack read next ih =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact (ih _ _ _ pathMem).trans (by
          simp only [statementObservationDepth]
          omega)
      · split at pathMem
        · rw [List.mem_flatMap] at pathMem
          obtain ⟨observed, _, pathMem⟩ := pathMem
          obtain ⟨sourcePath, sourceMem, rfl⟩ := List.mem_map.mp pathMem
          have sourceBound := ih _ _ _ sourceMem
          simp only [StatementPath.andGuard, TransitionExpr.gateCount]
          rw [show
            (currentStackCellIs (tm := tm) (clockBits := clockBits)
              stack _ observed).gateCount = 1 by rfl]
          simp only [statementObservationDepth]
          omega
        · exact (ih _ _ _ pathMem).trans (by
            simp only [statementObservationDepth]
            omega)
  | load update next ih =>
      exact ih (update control) transforms path pathMem
  | branch test yes no yesIH noIH =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact (yesIH _ _ _ pathMem).trans (by
          simp only [statementObservationDepth]
          omega)
      · exact (noIH _ _ _ pathMem).trans (by
          simp only [statementObservationDepth]
          omega)
  | goto target =>
      simp only [statementPaths, List.mem_singleton] at pathMem
      rcases pathMem with rfl
      simp [statementObservationDepth, TransitionExpr.gateCount]
  | halt =>
      simp only [statementPaths, List.mem_singleton] at pathMem
      rcases pathMem with rfl
      simp [statementObservationDepth, TransitionExpr.gateCount]

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
