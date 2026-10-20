/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderBounds
import LeanTrominoes.Computation.RAM.PolynomialBounds

/-! # Uniform polynomial bounds for the complete 2SAT constructor -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ComplexityAbstract.RAM WordBounds
open WordBounds.PolynomialBound

/-- Every mathematical header field has a uniform polynomial bound. -/
theorem polynomial_fields (d : ℕ) :
    PolynomialBound (fun n _ => bound d n) ∧
    PolynomialBound (fun n _ => period d n) ∧
    PolynomialBound (fun n _ => coordinateCount d n) ∧
    PolynomialBound (fun n _ => vertexCount d n) ∧
    PolynomialBound (fun n m => edgeCount d n m) ∧
    PolynomialBound (fun n _ => atomCount d n) ∧
    PolynomialBound (fun n m => ruleCount d n m) ∧
    PolynomialBound (fun n m => occurrenceCount d n m) ∧
    PolynomialBound (fun n m => size d n m) ∧
    PolynomialBound (fun n m => length d n m) ∧
    PolynomialBound (fun n m => arena d n m) ∧
    PolynomialBound (fun n m => tableBase d n m) := by
  have det : PolynomialBound (fun n _ => bound d n) := by
    exact (constant d.factorial).mul ((((constant 8).mul (left.add (constant 1))).add (constant 3)).pow d)
  have per : PolynomialBound (fun n _ => period d n) := by
    apply ((constant 2).mul (det.add (constant 1))).mono
    intro n m
    simpa only [period,ImplicationGraph.coverPeriod,← Nat.log2_eq_log_two] using
      ImplicationGraph.coverPeriod_le (bound d n)
  have coords := per.pow d
  have vertices := ((left.add (constant 1)).mul (constant 2)).mul coords
  have edges := coords.mul (right.mul (constant 2))
  have atoms := ((left.mul (constant 2)).mul vertices).add (constant 1)
  have rules := (((constant 3).mul left).add (((constant 2).mul left).mul edges)).add right
  have occs := ((constant 2).mul left).add (((constant 2).mul left).mul edges)
  have sizes := ((atoms.add rules).add occs).add (constant 1)
  have lengths := ((constant 4).add rules).add ((constant 2).mul occs)
  have arenas := (constant (4*(Raw.recordSize d+1))).mul
    ((((((sizes.add det).add coords).add left).add ((constant 3).mul right)).add (constant 4)).pow 27)
  have tables := ((((((((((((arenas.add sizes).add lengths).add coords).add vertices).add edges).add atoms).add rules).add occs).add left).add right).add per).add (constant (Raw.recordSize d))).add (constant 2)
  exact ⟨det,per,coords,vertices,edges,atoms,rules,occs,sizes,lengths,arenas,tables⟩

def originalLength (d m : ℕ) : ℕ := 2+Raw.recordSize d*(m+1)

theorem originalLength_polynomial (d : ℕ) : PolynomialBound (fun _ m => originalLength d m) :=
  (constant 2).add ((constant (Raw.recordSize d)).mul (right.add (constant 1)))

/-- This single polynomial dominates every allocation endpoint, expression
budget, and input length needed by the concrete constructor. -/
def resources (d n m : ℕ) : ℕ :=
  base d n m^exponent d+tableBase d n m^(2*(Cells.cell d).nodes)+
    (arena d n m+originalLength d m)+length d n m+2

theorem resources_polynomial (d : ℕ) : PolynomialBound (resources d) := by
  obtain ⟨det,per,coords,vertices,edges,atoms,rules,occs,sizes,lengths,arenas,tables⟩ := polynomial_fields d
  have bases : PolynomialBound (base d) :=
    ((((((constant (constants d)).add left).add right).add det).add per).add (constant 4))
  exact ((((bases.pow (exponent d)).add (tables.pow (2*(Cells.cell d).nodes))).add
    (arenas.add (originalLength_polynomial d))).add lengths).add (constant 2)

theorem resource_fits (d : ℕ) : ∃ k, ∀ n m w,
    k*Nat.log2 (n+m+3)+2≤w → Fits w (resources d n m : ℕ) :=
  (resources_polynomial d).fits

/-- The exact header cost is polynomial as well; logarithm evaluation is
realized by the doubling loop, whose iteration count is bounded here. -/
theorem cost_polynomial (d : ℕ) : PolynomialBound (fun n _ => cost d n) := by
  have det := (polynomial_fields d).1
  apply (((constant (ImplicationGraph.TwoSATExpression.Assignment.cost (prepare d))).add
    (((constant 3).mul (det.add (constant 1))).add (constant 2))).add
    (constant (ImplicationGraph.TwoSATExpression.Assignment.cost (finish d)))).mono
  intro n m
  have log : Nat.log2 (bound d n)≤bound d n := Nat.log2_le_self (bound d n)
  unfold cost
  omega

def totalBound (d n m : ℕ) : ℕ := cost d n+9*originalLength d m+
  ((Cells.cell d).nodes+5)*length d n m+4*arena d n m+55+120*(size d n m+1)

theorem totalBound_polynomial (d : ℕ) : PolynomialBound (totalBound d) := by
  obtain ⟨det,per,coords,vertices,edges,atoms,rules,occs,sizes,lengths,arenas,tables⟩ := polynomial_fields d
  exact (((((cost_polynomial d).add ((constant 9).mul (originalLength_polynomial d))).add
    ((constant ((Cells.cell d).nodes+5)).mul lengths)).add ((constant 4).mul arenas)).add
    (constant 55)).add ((constant 120).mul (sizes.add (constant 1)))


end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
