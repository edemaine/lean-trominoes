/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCoverTables
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawFields

/-! # Arithmetic endpoint formulas for original clause records -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph
variable {n d : ℕ}

def rawSourceLiteral (c : Clause (Fin n) d) (direction : ℤ) : ℤ :=
  Raw.validFlag c*((1-direction)*(2*Raw.firstVariable c+1-Raw.firstSign c)+
    direction*(2*Raw.secondVariable c+1-Raw.secondSign c))

def rawTargetLiteral (c : Clause (Fin n) d) (direction : ℤ) : ℤ :=
  Raw.validFlag c*((1-direction)*(2*Raw.secondVariable c+Raw.secondSign c)+
    direction*(2*Raw.firstVariable c+Raw.firstSign c))

def rawDisplacement (c : Clause (Fin n) d) (direction : ℤ) (j : Fin d) : ℤ :=
  (1-direction)*(Raw.secondOffset c j-Raw.firstOffset c j)+
    direction*(Raw.firstOffset c j-Raw.secondOffset c j)

theorem paddedArcAt_sourceField (c : Clause (Fin n) d) (direction : Fin 2) :
    ((literalIndex (n+1) (paddedArcAt (by omega) (liftClause c) direction).source).val : ℤ)=
      rawSourceLiteral c direction.val := by
  cases c with
  | none =>
    fin_cases direction <;>
      simp [paddedArcAt,liftClause,dummyArc,dummy,literalIndex_value,rawSourceLiteral,Raw.validFlag]
  | some pair =>
    rcases pair with ⟨⟨⟨av,ap⟩,az⟩,⟨⟨bv,bp⟩,bz⟩⟩
    fin_cases direction <;> cases ap <;> cases bp <;>
      simp [paddedArcAt,liftClause,liftLiteral,literalIndex_value,negate,rawSourceLiteral,
        Raw.validFlag,Raw.firstVariable,Raw.secondVariable,Raw.firstSign,Raw.secondSign,Nat.cast_add,Nat.cast_mul]
    all_goals ring

theorem paddedArcAt_targetField (c : Clause (Fin n) d) (direction : Fin 2) :
    ((literalIndex (n+1) (paddedArcAt (by omega) (liftClause c) direction).target).val : ℤ)=
      rawTargetLiteral c direction.val := by
  cases c with
  | none =>
    fin_cases direction <;>
      simp [paddedArcAt,liftClause,dummyArc,dummy,literalIndex_value,rawTargetLiteral,Raw.validFlag]
  | some pair =>
    rcases pair with ⟨⟨⟨av,ap⟩,az⟩,⟨⟨bv,bp⟩,bz⟩⟩
    fin_cases direction <;> cases ap <;> cases bp <;>
      simp [paddedArcAt,liftClause,liftLiteral,literalIndex_value,negate,rawTargetLiteral,
        Raw.validFlag,Raw.firstVariable,Raw.secondVariable,Raw.firstSign,Raw.secondSign,Nat.cast_add,Nat.cast_mul]
    all_goals ring

theorem paddedArcAt_offsetField (c : Clause (Fin n) d) (direction : Fin 2) (j : Fin d) :
    (paddedArcAt (by omega) (liftClause c) direction).offset j=rawDisplacement c direction.val j := by
  cases c with
  | none => fin_cases direction <;> simp [paddedArcAt,liftClause,dummyArc,rawDisplacement,Raw.secondOffset,Raw.firstOffset]
  | some pair =>
    rcases pair with ⟨a,b⟩
    fin_cases direction <;> simp [paddedArcAt,liftClause,liftLiteral,rawDisplacement,Raw.firstOffset,Raw.secondOffset]

end LeanTrominoes.PeriodicTwoSAT.WordRAM
