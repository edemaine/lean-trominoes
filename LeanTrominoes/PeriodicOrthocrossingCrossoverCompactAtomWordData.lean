/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Compact atom-word roles of one fixed crossover -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open PeriodicCNFStripReduction.DirectSourceFinalAtomWords
open PlanarThreeSAT

/-- Clause-major literal roles of the fixed Figure 8(b) crossover. -/
def roles : List CrossoverVariable :=
  crossoverFormula.flatMap fun clause =>
    clause.literals.map Prod.fst

@[simp] theorem roles_length : roles.length = 58 := by
  native_decide

/-- Boundary side supplying the compact source-key pair of a crossover role.
Internal variables use the fixed left boundary as their site identifier. -/
def sourceSide : CrossoverVariable → CrossingSide
  | .aLeft => .left
  | .aRight => .right
  | .bTop => .top
  | .bBottom => .bottom
  | _ => .left

/-- Internal constructor represented by a non-boundary crossover role. -/
def internal? : CrossoverVariable → Option CrossoverInternal
  | .aLeft | .aRight | .bTop | .bBottom => none
  | .aInnerLeft => some .aInnerLeft
  | .upperLeft => some .upperLeft
  | .lowerLeft => some .lowerLeft
  | .bInnerTop => some .bInnerTop
  | .center => some .center
  | .bInnerBottom => some .bInnerBottom
  | .upperRight => some .upperRight
  | .lowerRight => some .lowerRight
  | .aInnerRight => some .aInnerRight

/-- Two-bit compact constructor tag of a crossover literal role. -/
def constructorPrefix (role : CrossoverVariable) : List Bool :=
  if (internal? role).isSome then [true, true] else [false, true]

/-- Internal-role suffix; boundary roles need no suffix. -/
def suffix (role : CrossoverVariable) : List Bool :=
  match internal? role with
  | some internal => crossoverInternalWord internal
  | none => []

/-- Remove one active support guard and decorate its source-key pair with the
constructor data of the corresponding crossover literal role. -/
def word (role : CrossoverVariable) : List Bool → List (List Bool)
  | true :: sourcePair =>
      [constructorPrefix role ++ sourcePair ++ suffix role]
  | _ => []

/-- Expand one guarded canonical crossing key into its complete fixed
clause-major literal block. -/
def wordsForRoles (guarded : List Bool) : List (List Bool) :=
  roles.flatMap fun role => word role guarded

def words (guarded : List (List Bool)) : List (List Bool) :=
  guarded.flatMap wordsForRoles

def compact (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨words input.words⟩

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
