/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATSelection
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawInput
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATDigits

/-! # The fixed arithmetic expression generating each Horn table cell

The only memory loads are fields of original clause records. Coordinate
quotients, signed differences, modular shifts, graph-copy indices, and Horn
record indices are computed by ordinary RAM arithmetic. The expression has
fixed finite size at each fixed dimension.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
open ImplicationGraph.TwoSATExpression

abbrev Expression := Expr 17

def constant (n : ℤ) : Expression := .constant n
def input (r : Fin 17) : Expression := .inputValue r
def add (a b : Expression) : Expression := .arithmetic .add a b
def sub (a b : Expression) : Expression := .arithmetic .sub a b
def mul (a b : Expression) : Expression := .arithmetic .mul a b
def div (a b : Expression) : Expression := .arithmetic .div a b
def mod (a b : Expression) : Expression := .arithmetic .mod a b

abbrev position : Expression := input 1
abbrev outputLength : Expression := input 2
abbrev original : Expression := input 5
abbrev numVars : Expression := input 6
abbrev clauses : Expression := input 7
abbrev period : Expression := input 8
abbrev coordinates : Expression := input 9
abbrev vertices : Expression := input 10
abbrev edges : Expression := input 11
abbrev atoms : Expression := input 12
abbrev rules : Expression := input 13
abbrev occurrences : Expression := input 14

def two (x : Expression) : Expression := mul (constant 2) x
def three (x : Expression) : Expression := mul (constant 3) x
def increment (x : Expression) : Expression := add x (constant 1)
def complement (x : Expression) : Expression := sub (constant 1) x

def select (a b yes no : Expression) : Expression :=
  Expr.selectLt (increment outputLength) a b yes no

def mask (x : Expression) : Expression := mod x outputLength

def power : ℕ → Expression
  | 0 => constant 1
  | d+1 => mul (power d) period

def record (d : ℕ) (clause field : Expression) : Expression :=
  .load (add (add original (constant 2))
    (add (mul (constant (Raw.recordSize d)) (mod clause (increment clauses))) field))

def flag (d : ℕ) (clause : Expression) : Expression := record d clause (constant 0)

def direction (edge : Expression) : Expression := mod edge (constant 2)
def row (edge : Expression) : Expression := mod (div edge (two clauses)) coordinates

def clauseIndex (edge : Expression) : Expression := div (mod edge (two clauses)) (constant 2)

def sourceLiteral (d : ℕ) (edge : Expression) : Expression :=
  let clause := clauseIndex edge
  let sign := direction edge
  add (mul (complement sign) (add (two (record d clause (constant 1)))
    (complement (record d clause (constant 2)))))
    (mul sign (add (two (record d clause (constant 3))) (complement (record d clause (constant 4)))))

def targetLiteral (d : ℕ) (edge : Expression) : Expression :=
  let clause := clauseIndex edge
  let sign := direction edge
  add (mul (complement sign) (add (two (record d clause (constant 3))) (record d clause (constant 4))))
    (mul sign (add (two (record d clause (constant 1))) (record d clause (constant 2))))

def displacement (d : ℕ) (edge : Expression) (j : Fin d) : Expression :=
  let clause := clauseIndex edge
  let sign := direction edge
  let a := record d clause (constant (5+j.val))
  let b := record d clause (constant (5+d+j.val))
  add (mul (complement sign) (sub b a)) (mul sign (sub a b))

def shifted (d : ℕ) (edge : Expression) : Expression :=
  (List.finRange d).foldr (fun j rest => add
    (mul (mod (add (mod (div (row edge) (power j.val)) period) (displacement d edge j)) period)
      (power j.val)) rest) (constant 0)

def sourceVertex (d : ℕ) (edge : Expression) : Expression :=
  add (mul (mul (flag d (clauseIndex edge)) (sourceLiteral d edge)) coordinates) (row edge)

def targetVertex (d : ℕ) (edge : Expression) : Expression :=
  add (mul (mul (flag d (clauseIndex edge)) (targetLiteral d edge)) coordinates) (shifted d edge)

def sourceFact (block : Expression) : Expression :=
  increment (add (mul block vertices)
    (mul (add (two (div block (constant 2))) (complement (direction block))) coordinates))

def oppositeTarget (block : Expression) : Expression :=
  increment (add (mul block vertices)
    (mul (add (two (div block (constant 2))) (direction block)) coordinates))

def unaryHead (d : ℕ) (i : Expression) : Expression :=
  increment (add (mul (div i edges) vertices) (targetVertex d (mod i edges)))

def unaryAtom (d : ℕ) (i : Expression) : Expression :=
  increment (add (mul (div i edges) vertices) (sourceVertex d (mod i edges)))

def headCell (d : ℕ) (i : Expression) : Expression :=
  select i (two numVars) (sourceFact i)
    (select i (three numVars) (constant 0)
      (select i (add (three numVars) (mul (two numVars) edges))
        (unaryHead d (mask (sub i (three numVars))))
        (mul (flag d (sub i (add (three numVars) (mul (two numVars) edges)))) atoms)))

def atomCell (d : ℕ) (i : Expression) : Expression :=
  select i (two numVars) (oppositeTarget i) (unaryAtom d (mask (sub i (two numVars))))

def ruleCell (i : Expression) : Expression :=
  select i (two numVars) (add (two numVars) (div i (constant 2)))
    (add (three numVars) (mask (sub i (two numVars))))

def cell (d : ℕ) : Expression :=
  select position (constant 1) (sub outputLength (constant 1))
    (select position (constant 2) atoms
      (select position (constant 3) rules
        (select position (constant 4) occurrences
          (select position (add (constant 4) rules) (headCell d (mask (sub position (constant 4))))
            (select position (add (add (constant 4) rules) occurrences)
              (atomCell d (mask (sub position (add (constant 4) rules))))
              (ruleCell (mask (sub position (add (add (constant 4) rules) occurrences)))))))))

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Cells
