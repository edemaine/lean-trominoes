/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSignedCountSemantics

/-! # Polynomial-time evaluation of one signed affine atom -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open DelimitedBinaryWordPairLengthComparisonMachine

/-- Interpret one ordering according to a fixed affine relation. -/
def Relation.orderingBlock
    (relation : Relation) (ordering : LengthOrdering) : List Bool :=
  [relation.acceptsOrdering ordering]

/-- Physical singleton Boolean output of one affine atom comparison. -/
def Atom.truthResults
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  (atom.difference.comparisonOrderings tokens).flatMap
    atom.relation.orderingBlock

/-- The singleton machine output is exactly the atom's tagged-field truth
value. -/
@[simp] theorem Atom.truthResults_eq
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    atom.truthResults tokens = [atom.eval (tokenFieldValue tokens)] := by
  unfold Atom.truthResults
  rw [atom.difference.comparisonOrderings_eq]
  unfold Relation.orderingBlock
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have exact := atom.evalFromTokenCounts_eq_eval tokens
  have valueEq :
      atom.relation.acceptsOrdering
          (compareNats
            (atom.difference.positiveCount (tokenFieldValue tokens))
            (atom.difference.negativeCount (tokenFieldValue tokens))) =
        atom.eval (tokenFieldValue tokens) := by
    simpa only [Atom.evalFromTokenCounts, Expression.tokenCounts] using exact
  exact congrArg (fun value => [value]) valueEq

/-- Interpreting orderings according to one fixed relation is a finite block
transduction. -/
def Relation.orderingBlockComputableInPolyTime
    (relation : Relation) :
    TM2ComputableInPolyTime id id
      (fun orderings => orderings.flatMap relation.orderingBlock) :=
  FiniteBlockTransducer.computableInPolyTime relation.orderingBlock

/-- Every fixed affine atom can be evaluated in polynomial time from the
tagged unary descriptor-pair stream. -/
def Atom.truthResultsComputableInPolyTime
    (atom : Atom) :
    TM2ComputableInPolyTime id id atom.truthResults := by
  let composed := TM2CompositionMachine.computableInPolyTime
    atom.difference.comparisonOrderingsComputableInPolyTime
    atom.relation.orderingBlockComputableInPolyTime
  unfold Atom.truthResults
  exact composed

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
