/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATWordRAMPolynomialTime
import LeanTrominoes.Computation.RAM.Recode

/-! # The periodic 2SAT word-RAM theorem in the graph abstract's notation

The public tuples, predicates, and signed input words below are definitionally
identical to the original-input solver's representation. No conversion steps
or auxiliary input data are needed.
-/
namespace LeanTrominoes.GraphTwoSATAbstractBridge
/-! A periodic binary clause has two signed variables and their lattice offsets.
`true` is a positive sign. Repeating a literal gives a unit clause; `none` is
an empty clause. Every lattice translate of every listed clause is required. -/
namespace TwoSAT
abbrev Literal (n d : ℕ) := (Fin n × Bool) × (Fin d → ℤ)
abbrev Clause (n d : ℕ) := Option (Literal n d × Literal n d)
abbrev Formula (n d : ℕ) := List (Clause n d)

def Truth {n d : ℕ} (model : Fin n → (Fin d → ℤ) → Prop)
    (literal : Fin n × Bool) (z : (Fin d → ℤ)) : Prop :=
  if literal.2 then model literal.1 z else ¬ model literal.1 z

def Holds {n d : ℕ} (model : Fin n → (Fin d → ℤ) → Prop)
    (z : (Fin d → ℤ)) : Clause n d → Prop
  | none => False
  | some (a,b) => Truth model a.1 (z+a.2) ∨ Truth model b.1 (z+b.2)

def Satisfiable {n d : ℕ} (formula : Formula n d) : Prop :=
  ∃ model, ∀ clause ∈ formula, ∀ z, Holds model z clause

/-- Locality bounds relative offsets coordinatewise by one. The two literals
may have an arbitrarily large common offset. -/
def Local {n d : ℕ} (formula : Formula n d) : Prop :=
  ∀ a b, some (a,b) ∈ formula → ∀ i, (b.2 i-a.2 i).natAbs ≤ 1

abbrev Input (d : ℕ) := {input : (Σ n : ℕ, Formula n d) // Local input.2}

/-- Each clause record stores a presence flag, two variable indices, two sign
bits, and both original offset vectors. Empty clauses use zero records.
The input starts with the variable and clause counts and ends with a zero
record for padding. Its structural size is variables plus clauses plus one. -/
def clauseWords {n d : ℕ} : Clause n d → List ℤ
  | none => List.replicate (5+2*d) 0
  | some (a,b) => [(1:ℤ),(a.1.1.val:ℤ),(if a.1.2 then 1 else 0),
      (b.1.1.val:ℤ),(if b.1.2 then 1 else 0)] ++
      (List.finRange d).map a.2 ++ (List.finRange d).map b.2

def encode {d : ℕ} (input : Input d) : List ℤ :=
  [(input.val.1:ℤ),(input.val.2.length:ℤ)] ++
    (input.val.2++[none]).flatMap clauseWords

def size {d : ℕ} (input : Input d) : ℕ := input.val.1+input.val.2.length+1
end TwoSAT


theorem polynomialTime (d : ℕ) :
    ComplexityAbstract.RAM.PolynomialTime TwoSAT.encode TwoSAT.size
      (fun input : TwoSAT.Input d => TwoSAT.Satisfiable input.val.2) := by
  let map : TwoSAT.Input d → PeriodicTwoSAT.WordRAM.Raw.LocalInput d :=
    fun input => ⟨input.val,input.property⟩
  exact ComplexityAbstract.RAM.PolynomialTime.recode map
    (fun input => rfl) (fun input => rfl) (fun input => by
      constructor
      all_goals
        rintro ⟨model,satisfied⟩
        refine ⟨model,?_⟩
        intro clause member z
        have holds := satisfied clause member z
        cases clause with
        | none => exact holds
        | some pair => exact holds)
    (PeriodicTwoSAT.WordRAM.polynomialTime d)

end LeanTrominoes.GraphTwoSATAbstractBridge
