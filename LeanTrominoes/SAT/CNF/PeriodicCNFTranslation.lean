/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoder

/-! # Translating a satisfying assignment and its local decoder -/
namespace LeanTrominoes.PeriodicCNF.Translation
variable {V W : Type}

def assignment (base : Cell) (a : V → Cell → Bool) : V → Cell → Bool :=
  fun v c => a v (Cell.sub c base)

theorem clause_holds (base : Cell) (a : V → Cell → Bool) (c : Cell) (clause : PeriodicClause V) :
    clause.Holds (assignment base a) c ↔ clause.Holds a (Cell.sub c base) := by
  simp only [PeriodicClause.Holds,PeriodicLiteral.Holds,assignment,Cell.add,Cell.sub]
  have same (l : PeriodicLiteral V) :
      (c.1+l.offset.1-base.1,c.2+l.offset.2-base.2) =
        (c.1-base.1+l.offset.1,c.2-base.2+l.offset.2) := by ext <;> omega
  simp_rw [same]

theorem satisfies (base : Cell) (formula : PeriodicCNF V) (a : V → Cell → Bool)
    (valid : formula.Satisfies a) : formula.Satisfies (assignment base a) :=
  fun c clause member => (clause_holds base a c clause).2 (valid _ clause member)

theorem decode (base : Cell) (read : SignedDecoder.Read V W) (a : W → Cell → Bool) :
    SignedDecoder.decode read (assignment base a) = assignment base (SignedDecoder.decode read a) := by
  funext v c
  simp only [SignedDecoder.decode,assignment,Cell.add,Cell.sub]
  have same : (c.1+(read v).offset.1-base.1,c.2+(read v).offset.2-base.2) =
      (c.1-base.1+(read v).offset.1,c.2-base.2+(read v).offset.2) := by ext <;> omega
  rw [same]

theorem at_shift (base : Cell) (a : V → Cell → Bool) (v : V) (c : Cell) :
    assignment base a v (Cell.add base c) = a v c := by
  simp [assignment,Cell.add,Cell.sub]

theorem decode_add (base : Cell) (read : SignedDecoder.Read V W) (a : W → Cell → Bool) :
    SignedDecoder.decode read (fun v c => a v (Cell.add base c)) =
      fun v c => SignedDecoder.decode read a v (Cell.add base c) := by
  funext v c
  simp only [SignedDecoder.decode,Cell.add,add_assoc]

end LeanTrominoes.PeriodicCNF.Translation
