# Summary

Formal verification of Finite Affine Geometry $(AG(4,3))$ in Rocq, which is
used in turn to demo a small browser-based game based on the game Set(R). This
repository is not affiliated with Set Enterprises, Inc.

## Structure

There are two directories, theories/ and src/. The src/ directory contains a
"harness" written in OCaml, which imports generated code from the theories/
directory. The theories/ directory consists of verified Rocq code, which is
intended to drive the game logic and display logic as best it can.

A goal of this project is to eventually modularize the theory files a little
better. After all, there is this rough division, _with this approximate
topographical sort_:

### Game Logic
- Eqb.v
- Affine.v
- Deck.v
- Referee.v
- GameState.v

### UI Logic
- Display.v
- Geometry.v
- ClientState.v

There is also Extract.v, which serves as the "glue" or "bridge" to OCaml.

## Detailed Walkthrough
- Eqb.v is a utility that makes it easier to deal with the need
to reflect between boolean and propositional equalities often in Affine.v.

- Affine.v defines the F3 and the Point datatypes, and defines what it means
for a triple to be "valid". It also proves that the intuitive and algebraic
definitions of validity are "the same".

- Deck.v defines the deck of all cards and proves that the deck is 81 cards
long, and represents every single possible Point.

- Referee.v defines a method for checking whether, in some list Point, there
is or is not some valid triple of points.

- GameState.v helps describe the flow of logic during a game; when we deal,
how to select/deselect cards, how to tell a user their triple was valid.

- Display.v is largely concerned with representing the board as a grid of
cards, and ensuring that these cards don't get shuffled too much during the
removal of triples or the addition of new cards.

- Geometry.v is largely concerned with the Cartesian coordinate geometry of
said grid in Display.v.

- ClientState.v is designed to be a shim between GameState.v and the OCaml
harness. It uses logic from Geometry.v to convert click events with (x, y)
representation to something like "option Point" (where this represents a
card that may have been clicked).
