/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenData

/-! # Finite route tokens for source occurrences

The flat-formula parser retains binary atom and horizontal-offset fields.
Routes do not need the atom bits, and the forward-local promise reduces every
horizontal offset to the finite choice zero or one.  This transducer erases
the atom field and collapses each offset field to that one bit.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceRouteTokens

/-- Finite source-occurrence information needed by the route emitter. -/
inductive Token
  | clause (arity : Fin 4)
  | literal (index : Fin 3)
  | offsetNext (value : Bool)
  | literalEnd
  deriving DecidableEq, Fintype, Inhabited

/-- Select the unique header of each source clause. -/
def isClause : Token → Bool
  | .clause _ => true
  | _ => false

/-- Select the unique header of each literal occurrence. -/
def isLiteral : Token → Bool
  | .literal _ => true
  | _ => false

/-- The Boolean state records whether the current binary offset word contains
a one bit. -/
def transition : Bool → SourceOccurrenceTokens.Token → Bool × List Token
  | _, .clause arity => (false, [.clause arity])
  | _, .literal index => (false, [.literal index])
  | seen, .offsetBit value => (seen || value, [])
  | seen, .offsetEnd => (false, [.offsetNext seen])
  | _, .literalEnd => (false, [.literalEnd])
  | seen, _ => (seen, [])

def finish (_ : Bool) : List Token := []

/-- Total finite-state normalization of an occurrence-token word. -/
def normalize (tokens : List SourceOccurrenceTokens.Token) : List Token :=
  FiniteStateTransducer.output false transition finish tokens

end SourceOccurrenceRouteTokens
end PeriodicCNF
end LeanTrominoes
