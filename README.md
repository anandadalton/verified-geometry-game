# Finite Affine Geometry

## Summary

A small browser-based game based on the game Set(R). This
repository is not affiliated with Set Enterprises, Inc. The main point of interest
is that we endeavor to verify as much code as possible; for example, it is verified
that the "deal" function will, if cards are available, place cards on the board
if and only if there are either fewer than 12 cards or there is not a valid triple
of cards in play.

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

## Building

We assume you have opam installed already; with that assumption, run:

```bash
opam switch create .
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install dune coq coq-stdlib js_of_ocaml-compiler js_of_ocaml-ppx brr
```

Then, from within the project directory, run

```
dune build
```

You should afterwards be able to open the file `src/index.html` and play the
game in your browser.

## License

Copyright 2025, Ananda Dalton

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
