/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinData
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Bounded cancellation in delimited direction words -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

abbrev Token := DelimitedRouteJoin.Token

/-- Bend/fan junctions can overlap by at most seven lane spacings of eight
unit directions each. -/
def bufferCapacity : Nat := 56

abbrev Count := Fin (bufferCapacity + 1)

/-- Only the most recent constant-direction run must be delayed. -/
inductive Control
  | empty
  | run (direction : AxisDirection) (count : Count)
  deriving DecidableEq, Fintype, Inhabited

def buffered (direction : AxisDirection) (count : Count) : List Token :=
  List.replicate count.val (.direction direction)

def one : Count := 1

/-- Delay at most 56 symbols of the final run.  Equal directions extend the
run, opposite directions cancel it, and perpendicular turns flush it. -/
def transition : Control → Token → Control × List Token
  | .empty, .routeEnd => (.empty, [.routeEnd])
  | .empty, .direction direction => (.run direction one, [])
  | .run direction count, .routeEnd =>
      (.empty, buffered direction count ++ [.routeEnd])
  | .run direction count, .direction next =>
      if count.val = 0 then
        (.run next one, [])
      else if next = direction then
        if count.val = bufferCapacity then
          (.run direction count, [.direction direction])
        else
          (.run direction (count + 1), [])
      else if next = direction.opposite then
        if count.val = 1 then
          (.empty, [])
        else
          (.run direction (count - 1), [])
      else
        (.run next one, buffered direction count)

def finish : Control → List Token
  | .empty => []
  | .run direction count => buffered direction count

/-- Cancel bounded immediate reversals independently within each delimited
direction word. -/
def output (tokens : List Token) : List Token :=
  FiniteStateTransducer.output .empty transition finish tokens

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
