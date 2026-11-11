/-!
# Othello (Reversi) on an `n × n` board — the specification

This file contains everything one has to read in order to understand what the
main theorems of this development say:

* the rules of the game (`flips`, `Legal`, `play`, `moves`, `margin`);
* what it means for a player to be able to force a result (`Secures`);
* the standard initial position (`initial`).

Nothing in this file mentions bitboards or search.
-/

namespace Othello

/-! ## Discs, squares, boards -/

inductive Color where
  | black
  | white
deriving DecidableEq, Repr

/-- The other player. -/
def Color.opponent : Color → Color
  | .black => .white
  | .white => .black

/-- A square is a pair `(column, row)` of integers. -/
abbrev Square := Int × Int

/-- A board tells which disc, if any, lies on each square. -/
abbrev Board := Square → Option Color

/-! ## The rules -/

section Rules

/- The board has `n` columns and `n` rows, both numbered `0, …, n-1`. -/
variable (n : Nat)

def OnBoard (s : Square) : Prop :=
  0 ≤ s.1 ∧ s.1 < n ∧ 0 ≤ s.2 ∧ s.2 < n

instance (s : Square) : Decidable (OnBoard n s) := by
  unfold OnBoard; infer_instance

/-- What lies on a square.  There is never anything outside the board. -/
def cell (b : Board) (s : Square) : Option Color :=
  if OnBoard n s then b s else none

/-- The eight directions. -/
def directions : List (Int × Int) :=
  [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]

/-- One step from `s` in direction `d`. -/
def step (d : Int × Int) (s : Square) : Square :=
  (s.1 + d.1, s.2 + d.2)

/-- `run n b c d k s acc` walks from square `s` in direction `d` and collects in
`acc` the discs of `c`'s opponent that it passes.  If the walk arrives at a
disc of colour `c`, the collected discs are outflanked and are returned.  If it
arrives at an empty square, or leaves the board, nothing is outflanked.
(`k` bounds the number of steps; `n` steps are always enough, see
`mem_flipsDir_iff` in `Othello/Lemmas.lean`.) -/
def run (b : Board) (c : Color) (d : Int × Int) :
    Nat → Square → List Square → List Square
  | 0, _, _ => []
  | k + 1, s, acc =>
    match cell n b s with
    | none => []
    | some c' => if c' = c then acc else run b c d k (step d s) (s :: acc)

/-- The discs flipped in direction `d` when `c` puts a disc on `s`. -/
def flipsDir (b : Board) (c : Color) (s : Square) (d : Int × Int) : List Square :=
  run n b c d n (step d s) []

/-- All discs flipped when `c` puts a disc on `s`. -/
def flips (b : Board) (c : Color) (s : Square) : List Square :=
  directions.flatMap (flipsDir n b c s)

/-- A move is legal iff it is made on an empty square of the board and flips
at least one disc. -/
def Legal (b : Board) (c : Color) (s : Square) : Prop :=
  OnBoard n s ∧ b s = none ∧ flips n b c s ≠ []

instance (b : Board) (c : Color) (s : Square) : Decidable (Legal n b c s) := by
  unfold Legal; infer_instance

/-- The board after `c` has played on `s`. -/
def play (b : Board) (c : Color) (s : Square) : Board :=
  fun q => if q = s ∨ q ∈ flips n b c s then some c else b q

/-- All squares of the board. -/
def squares : List Square :=
  (List.range n).flatMap fun (y : Nat) => (List.range n).map fun (x : Nat) => ((x : Int), (y : Int))

/-- The legal moves of `c`. -/
def moves (b : Board) (c : Color) : List Square :=
  (squares n).filter fun s => Legal n b c s

/-- The number of discs of colour `c`. -/
def count (b : Board) (c : Color) : Nat :=
  ((squares n).filter fun s => b s = some c).length

/-- The result of a finished game seen from `c`'s side: the number of `c`'s
discs minus the number of the opponent's discs. -/
def margin (b : Board) (c : Color) : Int :=
  (count n b c : Int) - (count n b c.opponent : Int)

/-! ## Optimal play

A player who has a legal move must make one; a player without a legal move
passes; the game is over when neither player has a legal move.

`Secures n p v b c` says: on board `b` with `c` to move, player `p` has a
strategy which guarantees — whatever the opponent does — that the game ends
with a margin of at least `v` for `p`.  A derivation of `Secures n p v b c`
is exactly such a strategy, written as a tree:

* `over`:   the game is over and `p`'s margin is at least `v`;
* `pass`:   the player to move has to pass;
* `choose`: it is `p`'s turn, and `p` picks a move after which `v` is still secured;
* `reply`:  it is the opponent's turn, and `v` stays secured after every legal move. -/
inductive Secures (p : Color) (v : Int) : Board → Color → Prop where
  | over {b c} :
      moves n b c = [] → moves n b c.opponent = [] →
      v ≤ margin n b p →
      Secures p v b c
  | pass {b c} :
      moves n b c = [] → moves n b c.opponent ≠ [] →
      Secures p v b c.opponent →
      Secures p v b c
  | choose {b c} (s : Square) :
      c = p → s ∈ moves n b c →
      Secures p v (play n b c s) c.opponent →
      Secures p v b c
  | reply {b c} :
      c ≠ p → moves n b c ≠ [] →
      (∀ s, s ∈ moves n b c → Secures p v (play n b c s) c.opponent) →
      Secures p v b c

/-- Under optimal play by both sides from board `b` with `c` to move, the game
ends with Black having exactly `v` more discs than White: Black can secure a
margin of at least `v`, and White can secure a margin of at least `-v`. -/
def OptimalResult (b : Board) (c : Color) (v : Int) : Prop :=
  Secures n .black v b c ∧ Secures n .white (-v) b c

end Rules

/-! ## The standard initial position -/

/-- The initial position on a board of size `2 * h`: White on the two central
squares of the main diagonal, Black on the other two central squares.  For
`h = 4` this is the usual start of Othello (White on d4 and e5, Black on e4
and d5).  Black moves first. -/
def initial (h : Nat) : Board := fun s =>
  if s = ((h : Int) - 1, (h : Int) - 1) ∨ s = ((h : Int), (h : Int)) then some .white
  else if s = ((h : Int), (h : Int) - 1) ∨ s = ((h : Int) - 1, (h : Int)) then some .black
  else none

end Othello
