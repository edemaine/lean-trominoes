/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableLocalGates
import LeanTrominoes.OrthogonalPolylineBoundingBox

/-!
# Coordinated variable-side outer ribbon fans

The connector-dependent routes end at standardized RGB gates along the top
of the variable gadget.  This file supplies the remaining finite routing
from those gates to the direction-dependent ribbon exits.

The safe routing region is the rectangular annulus outside
`[11, 109] × [48, 107]`, which contains the complete variable-site drawing.
Its lower detours lie at height at most `46`, leaving a full empty row before
the core.  A family exists
exactly when the one, two, or three active direction bundles occur in cyclic
clockwise order around the macrocell.  The table below enumerates the 28
possible direction lists: four singletons, twelve ordered pairs, and twelve
cyclically ordered triples.

The paths were synthesized simultaneously as vertex-disjoint paths in that
annulus.  All mathematical claims about the resulting data are checked here
by Lean; the synthesis program is not part of the trusted proof.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- One cyclic direction list and its three routes per active occurrence,
in occurrence-major RGB order. -/
structure VariableOuterFanTemplate where
  directions : List AxisDirection
  routes : List (List Cell)
  deriving DecidableEq, Repr, Inhabited

/-- Stable zero-based RGB order within one occurrence bundle. -/
def variableOuterFanColorIndex : WireColor → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

/-- Position of one slot/color strand in a template's route list. -/
def variableOuterFanRouteIndex
    (slot : VariableSiteSlot) (color : WireColor) : Nat :=
  3 * slot.index + variableOuterFanColorIndex color

/-- Select one route from a finite outer-fan template. -/
def VariableOuterFanTemplate.route
    (template : VariableOuterFanTemplate)
    (slot : VariableSiteSlot) (color : WireColor) : List Cell :=
  template.routes.getD
    (variableOuterFanRouteIndex slot color) []

/-! The following raw table is proof data.  The lower detour band is adjusted
below after the common table so it remains visibly uniform across every
cyclic direction family. -/
def rawStandardVariableOuterFanTemplates :
    List VariableOuterFanTemplate := [
  { directions := [.north]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (104, 110), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (108, 109), (108, 128)],
      [(28, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.south]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)]
    ] },
  { directions := [.west]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)]
    ] },
  { directions := [.north, .east]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (104, 113), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (108, 112), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (112, 111), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.north, .south]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (104, 113), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (108, 112), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (112, 111), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (112, 110), (112, 48), (24, 48), (24, 0)],
      [(56, 108), (59, 108), (59, 109), (111, 109), (111, 49), (20, 49), (20, 0)],
      [(60, 108), (110, 108), (110, 50), (16, 50), (16, 0)]
    ] },
  { directions := [.north, .west]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (104, 113), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (108, 112), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (112, 111), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (112, 110), (112, 48), (0, 48), (0, 104)],
      [(56, 108), (59, 108), (59, 109), (111, 109), (111, 49), (1, 49), (1, 105), (0, 105), (0, 108)],
      [(60, 108), (110, 108), (110, 50), (2, 50), (2, 106), (1, 106), (1, 109), (0, 109), (0, 112)]
    ] },
  { directions := [.east, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (104, 110), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (108, 109), (108, 128)],
      [(60, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.east, .south]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 46), (24, 46), (24, 0)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 45), (20, 45), (20, 0)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 44), (16, 44), (16, 0)]
    ] },
  { directions := [.east, .west]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 110), (0, 110), (0, 108)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 112), (0, 112)]
    ] },
  { directions := [.south, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (104, 110), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (108, 109), (108, 128)],
      [(60, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.south, .east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.south, .west]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 110), (0, 110), (0, 108)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 112), (0, 112)]
    ] },
  { directions := [.west, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (104, 110), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (108, 109), (108, 128)],
      [(60, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.west, .east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.west, .south]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (112, 110), (112, 48), (24, 48), (24, 0)],
      [(56, 108), (59, 108), (59, 109), (111, 109), (111, 49), (20, 49), (20, 0)],
      [(60, 108), (110, 108), (110, 50), (16, 50), (16, 0)]
    ] },
  { directions := [.north, .east, .south]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (78, 113), (78, 114), (81, 114), (81, 115), (84, 115), (84, 116), (104, 116), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (79, 112), (79, 113), (82, 113), (82, 114), (85, 114), (85, 115), (108, 115), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (80, 111), (80, 112), (83, 112), (83, 113), (86, 113), (86, 114), (112, 114), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (115, 113), (115, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (114, 112), (114, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (113, 111), (113, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (112, 110), (112, 48), (24, 48), (24, 0)],
      [(88, 108), (91, 108), (91, 109), (111, 109), (111, 49), (20, 49), (20, 0)],
      [(92, 108), (110, 108), (110, 50), (16, 50), (16, 0)]
    ] },
  { directions := [.north, .east, .west]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (78, 113), (78, 114), (81, 114), (81, 115), (84, 115), (84, 116), (104, 116), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (79, 112), (79, 113), (82, 113), (82, 114), (85, 114), (85, 115), (108, 115), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (80, 111), (80, 112), (83, 112), (83, 113), (86, 113), (86, 114), (112, 114), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (115, 113), (115, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (114, 112), (114, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (113, 111), (113, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (112, 110), (112, 48), (0, 48), (0, 104)],
      [(88, 108), (91, 108), (91, 109), (111, 109), (111, 49), (1, 49), (1, 105), (0, 105), (0, 108)],
      [(92, 108), (110, 108), (110, 50), (2, 50), (2, 106), (1, 106), (1, 109), (0, 109), (0, 112)]
    ] },
  { directions := [.north, .south, .west]
    routes := [
      [(20, 108), (23, 108), (23, 109), (26, 109), (26, 110), (49, 110), (49, 111), (52, 111), (52, 112), (55, 112), (55, 113), (78, 113), (78, 114), (81, 114), (81, 115), (84, 115), (84, 116), (104, 116), (104, 128)],
      [(24, 108), (27, 108), (27, 109), (50, 109), (50, 110), (53, 110), (53, 111), (56, 111), (56, 112), (79, 112), (79, 113), (82, 113), (82, 114), (85, 114), (85, 115), (108, 115), (108, 128)],
      [(28, 108), (51, 108), (51, 109), (54, 109), (54, 110), (57, 110), (57, 111), (80, 111), (80, 112), (83, 112), (83, 113), (86, 113), (86, 114), (112, 114), (112, 128)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (115, 113), (115, 45), (24, 45), (24, 0)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (114, 112), (114, 46), (20, 46), (20, 0)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (113, 111), (113, 47), (16, 47), (16, 0)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (112, 110), (112, 48), (0, 48), (0, 104)],
      [(88, 108), (91, 108), (91, 109), (111, 109), (111, 49), (1, 49), (1, 105), (0, 105), (0, 108)],
      [(92, 108), (110, 108), (110, 50), (2, 50), (2, 106), (1, 106), (1, 109), (0, 109), (0, 112)]
    ] },
  { directions := [.east, .south, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 46), (24, 46), (24, 0)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 45), (20, 45), (20, 0)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 44), (16, 44), (16, 0)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (104, 110), (104, 128)],
      [(88, 108), (91, 108), (91, 109), (108, 109), (108, 128)],
      [(92, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.east, .south, .west]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 46), (24, 46), (24, 0)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 45), (20, 45), (20, 0)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 44), (16, 44), (16, 0)],
      [(84, 108), (61, 108), (61, 109), (58, 109), (58, 110), (55, 110), (55, 111), (32, 111), (32, 112), (29, 112), (29, 113), (26, 113), (26, 114), (25, 114), (25, 115), (3, 115), (3, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(88, 108), (85, 108), (85, 109), (62, 109), (62, 110), (59, 110), (59, 111), (56, 111), (56, 112), (33, 112), (33, 113), (30, 113), (30, 114), (27, 114), (27, 115), (26, 115), (26, 116), (2, 116), (2, 110), (0, 110), (0, 108)],
      [(92, 108), (89, 108), (89, 109), (86, 109), (86, 110), (63, 110), (63, 111), (60, 111), (60, 112), (57, 112), (57, 113), (34, 113), (34, 114), (31, 114), (31, 115), (28, 115), (28, 116), (27, 116), (27, 117), (1, 117), (1, 112), (0, 112)]
    ] },
  { directions := [.east, .west, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (109, 49), (109, 27), (128, 27), (128, 24)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (108, 48), (108, 26), (127, 26), (127, 23), (128, 23), (128, 20)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (107, 47), (107, 25), (126, 25), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 110), (0, 110), (0, 108)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 112), (0, 112)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (104, 110), (104, 128)],
      [(88, 108), (91, 108), (91, 109), (108, 109), (108, 128)],
      [(92, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.south, .north, .east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (104, 113), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (108, 112), (108, 128)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (112, 111), (112, 128)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (128, 110), (128, 24)],
      [(88, 108), (91, 108), (91, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(92, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.south, .west, .north]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 110), (0, 110), (0, 108)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 112), (0, 112)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (104, 110), (104, 128)],
      [(88, 108), (91, 108), (91, 109), (108, 109), (108, 128)],
      [(92, 108), (112, 108), (112, 128)]
    ] },
  { directions := [.south, .west, .east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (9, 109), (9, 49), (24, 49), (24, 0)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (8, 110), (8, 48), (20, 48), (20, 0)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (7, 111), (7, 47), (16, 47), (16, 0)],
      [(52, 108), (29, 108), (29, 109), (26, 109), (26, 110), (23, 110), (23, 111), (22, 111), (22, 112), (6, 112), (6, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(56, 108), (53, 108), (53, 109), (30, 109), (30, 110), (27, 110), (27, 111), (24, 111), (24, 112), (23, 112), (23, 113), (5, 113), (5, 110), (0, 110), (0, 108)],
      [(60, 108), (57, 108), (57, 109), (54, 109), (54, 110), (31, 110), (31, 111), (28, 111), (28, 112), (25, 112), (25, 113), (24, 113), (24, 114), (4, 114), (4, 112), (0, 112)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (128, 110), (128, 24)],
      [(88, 108), (91, 108), (91, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(92, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.west, .north, .east]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (104, 113), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (108, 112), (108, 128)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (112, 111), (112, 128)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (128, 110), (128, 24)],
      [(88, 108), (91, 108), (91, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(92, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)]
    ] },
  { directions := [.west, .north, .south]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (104, 113), (104, 128)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (108, 112), (108, 128)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (112, 111), (112, 128)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (112, 110), (112, 48), (24, 48), (24, 0)],
      [(88, 108), (91, 108), (91, 109), (111, 109), (111, 49), (20, 49), (20, 0)],
      [(92, 108), (110, 108), (110, 50), (16, 50), (16, 0)]
    ] },
  { directions := [.west, .east, .south]
    routes := [
      [(20, 108), (19, 108), (19, 109), (1, 109), (1, 107), (0, 107), (0, 104)],
      [(24, 108), (21, 108), (21, 109), (20, 109), (20, 110), (0, 110), (0, 108)],
      [(28, 108), (25, 108), (25, 109), (22, 109), (22, 110), (21, 110), (21, 111), (0, 111), (0, 112)],
      [(52, 108), (55, 108), (55, 109), (58, 109), (58, 110), (81, 110), (81, 111), (84, 111), (84, 112), (87, 112), (87, 113), (115, 113), (115, 110), (128, 110), (128, 24)],
      [(56, 108), (59, 108), (59, 109), (82, 109), (82, 110), (85, 110), (85, 111), (88, 111), (88, 112), (114, 112), (114, 109), (127, 109), (127, 23), (128, 23), (128, 20)],
      [(60, 108), (83, 108), (83, 109), (86, 109), (86, 110), (89, 110), (89, 111), (113, 111), (113, 108), (126, 108), (126, 22), (127, 22), (127, 19), (128, 19), (128, 16)],
      [(84, 108), (87, 108), (87, 109), (90, 109), (90, 110), (112, 110), (112, 48), (24, 48), (24, 0)],
      [(88, 108), (91, 108), (91, 109), (111, 109), (111, 49), (20, 49), (20, 0)],
      [(92, 108), (110, 108), (110, 50), (16, 50), (16, 0)]
    ] }
]

/-- Move only the internal lower detour band below the variable-site core.
The standardized gates at height `108` and the boundary exits are fixed. -/
def lowerVariableOuterFanDetourPoint (point : Cell) : Cell :=
  if 40 ≤ point.2 ∧ point.2 ≤ 50 then
    (point.1, point.2 - 4)
  else point

/-- Apply the common lower-band correction to one raw fan template. -/
def lowerVariableOuterFanDetours
    (template : VariableOuterFanTemplate) : VariableOuterFanTemplate where
  directions := template.directions
  routes := template.routes.map fun route =>
    route.map lowerVariableOuterFanDetourPoint

/-- Corrected finite fan table.  All geometric properties of this transformed
table are checked independently below. -/
def standardVariableOuterFanTemplates :
    List VariableOuterFanTemplate :=
  rawStandardVariableOuterFanTemplates.map lowerVariableOuterFanDetours

/-- Finite direction data controlling one variable-side outer fan. -/
structure VariableOuterFanData where
  countPred : Fin 3
  direction : VariableSiteSlot → AxisDirection
  deriving DecidableEq, Fintype

namespace VariableOuterFanData

/-- Number of active occurrence bundles. -/
def count (data : VariableOuterFanData) : Nat :=
  data.countPred + 1

/-- Whether one of the three occurrence slots is active. -/
def SlotActive
    (data : VariableOuterFanData)
    (slot : VariableSiteSlot) : Prop :=
  slot.index < data.count

instance (data : VariableOuterFanData)
    (slot : VariableSiteSlot) :
    Decidable (data.SlotActive slot) := by
  unfold SlotActive
  infer_instance

/-- Active directions in physical left-to-right occurrence-slot order. -/
def activeDirections (data : VariableOuterFanData) :
    List AxisDirection :=
  match data.countPred.1 with
  | 0 => [data.direction .first]
  | 1 => [data.direction .first, data.direction .second]
  | _ =>
      [data.direction .first, data.direction .second,
        data.direction .third]

/-- The directions are genuine and pairwise distinct on active slots. -/
def IsValid (data : VariableOuterFanData) : Prop :=
  (∀ slot, data.SlotActive slot →
      (data.direction slot).IsGenuine) ∧
    ∀ firstSlot secondSlot,
      data.SlotActive firstSlot →
      data.SlotActive secondSlot →
      firstSlot ≠ secondSlot →
      data.direction firstSlot ≠ data.direction secondSlot

instance (data : VariableOuterFanData) :
    Decidable data.IsValid := by
  unfold IsValid
  infer_instance

/-- The active bundle order is one of the cyclic boundary orders covered by
the finite outer-fan table. -/
def IsClockwiseCompatible (data : VariableOuterFanData) : Prop :=
  data.activeDirections ∈
    standardVariableOuterFanTemplates.map
      VariableOuterFanTemplate.directions

instance (data : VariableOuterFanData) :
    Decidable data.IsClockwiseCompatible := by
  unfold IsClockwiseCompatible
  infer_instance

/-- Look up the unique template having the active direction list. -/
def selectedTemplate
    (data : VariableOuterFanData) : VariableOuterFanTemplate :=
  (standardVariableOuterFanTemplates.find?
    fun template =>
      decide (template.directions = data.activeDirections)).getD default

/-- The active-direction list has exactly one entry per active slot. -/
@[simp]
theorem activeDirections_length
    (data : VariableOuterFanData) :
    data.activeDirections.length = data.count := by
  native_decide +revert

/-- Looking up an active direction by its slot recovers the direction field. -/
theorem activeDirections_getD
    (data : VariableOuterFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot) :
    data.activeDirections.getD slot.index .invalid =
      data.direction slot := by
  native_decide +revert

/-- A compatible lookup selects one of the explicitly certified templates. -/
theorem selectedTemplate_mem
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible) :
    data.selectedTemplate ∈ standardVariableOuterFanTemplates := by
  unfold selectedTemplate
  generalize foundEq :
    standardVariableOuterFanTemplates.find?
      (fun template => decide
        (template.directions = data.activeDirections)) = found
  cases found with
  | none =>
      have none := List.find?_eq_none.mp foundEq
      unfold IsClockwiseCompatible at compatible
      rcases List.mem_map.mp compatible with
        ⟨template, templateMember, directionsEqual⟩
      have rejected := none template templateMember
      simp only [decide_eq_true_eq] at rejected
      exact (rejected directionsEqual).elim
  | some template =>
      simp only [Option.getD_some]
      exact List.mem_of_find?_eq_some foundEq

/-- A compatible lookup selects the template with the advertised active
direction list, not merely some member of the finite table. -/
theorem selectedTemplate_directions
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible) :
    data.selectedTemplate.directions = data.activeDirections := by
  unfold selectedTemplate
  generalize foundEq :
    standardVariableOuterFanTemplates.find?
      (fun template => decide
        (template.directions = data.activeDirections)) = found
  cases found with
  | none =>
      have none := List.find?_eq_none.mp foundEq
      unfold IsClockwiseCompatible at compatible
      rcases List.mem_map.mp compatible with
        ⟨template, templateMember, directionsEqual⟩
      have rejected := none template templateMember
      simp only [decide_eq_true_eq] at rejected
      exact (rejected directionsEqual).elim
  | some template =>
      simp only [Option.getD_some]
      simpa only [decide_eq_true_eq] using
        (List.find?_eq_some_iff_append.mp foundEq).1

/-- Coordinated route from one standardized gate to its ribbon exit. -/
def outerRoute
    (data : VariableOuterFanData)
    (slot : VariableSiteSlot) (color : WireColor) : List Cell :=
  data.selectedTemplate.route slot color

/-- The full finite variable configuration forgets its connector geometry
when selecting an outer-fan template. -/
def ofVariableRibbonFanData
    (data : VariableRibbonFanData) : VariableOuterFanData where
  countPred := data.countPred
  direction := data.direction

/-- The outer safe frame used by all generated routes. -/
def InOuterSafeFrame (point : Cell) : Prop :=
  InClosedGridRectangle (0, 108) (128, 128) point ∨
    InClosedGridRectangle (0, 0) (10, 128) point ∨
      InClosedGridRectangle (110, 0) (128, 128) point ∨
        InClosedGridRectangle (0, 0) (128, 46) point

instance (point : Cell) :
    Decidable (InOuterSafeFrame point) := by
  unfold InOuterSafeFrame
  infer_instance

/-- Both endpoints of a safe-frame segment lie in one common arm of the
frame, so the segment itself cannot cut across the protected center. -/
def OuterSafeFrameSegment (segment : GridSegment) : Prop :=
  (InClosedGridRectangle (0, 108) (128, 128) segment.start ∧
      InClosedGridRectangle (0, 108) (128, 128) segment.finish) ∨
    (InClosedGridRectangle (0, 0) (10, 128) segment.start ∧
      InClosedGridRectangle (0, 0) (10, 128) segment.finish) ∨
    (InClosedGridRectangle (110, 0) (128, 128) segment.start ∧
      InClosedGridRectangle (110, 0) (128, 128) segment.finish) ∨
    (InClosedGridRectangle (0, 0) (128, 46) segment.start ∧
      InClosedGridRectangle (0, 0) (128, 46) segment.finish)

instance (segment : GridSegment) :
    Decidable (OuterSafeFrameSegment segment) := by
  unfold OuterSafeFrameSegment
  infer_instance

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable (OrthogonalPolyline points) := by
  unfold OrthogonalPolyline
  infer_instance

/-- Every listed cyclic direction family is valid. -/
theorem isValid_of_isClockwiseCompatible :
    ∀ data : VariableOuterFanData,
      data.IsClockwiseCompatible → data.IsValid := by
  native_decide

/-- A selected route starts at its standardized RGB gate. -/
@[simp]
theorem outerRoute_head?
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (data.outerRoute slot color).head? =
      some (standardVariableOuterGate slot color) := by
  native_decide +revert

/-- A selected route ends at the matching direction-dependent ribbon exit. -/
@[simp]
theorem outerRoute_getLast?
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (data.outerRoute slot color).getLast? =
      some
        (standardRibbonMacrocellExit
          (data.direction slot) color) := by
  native_decide +revert

/-- Every selected outer route is rectilinear. -/
theorem outerRoute_orthogonal
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    OrthogonalPolyline (data.outerRoute slot color) := by
  native_decide +revert

/-- Every listed outer-route point remains inside the standard macrocell. -/
theorem outerRoute_points_bounded :
    ∀ (data : VariableOuterFanData),
      data.IsClockwiseCompatible →
      ∀ slot, data.SlotActive slot →
      ∀ color point,
        point ∈ data.outerRoute slot color →
        InStandardRibbonMacrocell point := by
  native_decide

/-- Every listed outer-route point stays outside the protected variable
gadget and local-gate rectangle. -/
theorem outerRoute_points_in_safeFrame :
    ∀ (data : VariableOuterFanData),
      data.IsClockwiseCompatible →
      ∀ slot, data.SlotActive slot →
      ∀ color point,
        point ∈ data.outerRoute slot color →
        InOuterSafeFrame point := by
  native_decide

/-- Every selected outer-route segment stays in one arm of the safe frame;
in particular, no segment shortcuts through the protected center. -/
theorem outerRoute_segments_in_safeFrame :
    ∀ (data : VariableOuterFanData),
      data.IsClockwiseCompatible →
      ∀ slot, data.SlotActive slot →
      ∀ color segment,
        segment ∈ gridPolylineSegments (data.outerRoute slot color) →
        OuterSafeFrameSegment segment := by
  native_decide

/-- Distinct active RGB strands in one selected outer fan have no continuous
or listed-point contact. -/
theorem outerRoutes_strictlyAvoidEachOther
    (data : VariableOuterFanData)
    (compatible : data.IsClockwiseCompatible)
    (firstSlot secondSlot : VariableSiteSlot)
    (firstActive : data.SlotActive firstSlot)
    (secondActive : data.SlotActive secondSlot)
    (firstColor secondColor : WireColor)
    (different :
      (firstSlot, firstColor) ≠ (secondSlot, secondColor)) :
    RoutesStrictlyAvoidEachOther
      (data.outerRoute firstSlot firstColor)
      (data.outerRoute secondSlot secondColor) := by
  native_decide +revert

end VariableOuterFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
