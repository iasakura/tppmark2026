import Othello.Six.Black
import Othello.Six.White
import Othello.Six.Popcount

/-!
# Problem 2: 6 × 6 Othello

From the standard initial position of 6 × 6 Othello, White (the second
player) wins 20–16 under optimal play: White can secure a win by 4 discs, and
Black can make sure not to lose by more.

The two game-tree searches behind this theorem (`search_black6`,
`search_white6`) are far too large for the Lean kernel; they are run as
compiled code by `native_decide`.  Each of them is recorded by Lean as an
axiom stating exactly the computed fact; a third axiom of this kind comes
from `bv_decide` in `Othello/Six/Popcount.lean`.  Everything else is checked
by the kernel.
-/

namespace Othello

/-- Black can secure a loss by no more than 4 discs. -/
theorem black_secures_6x6 : Secures 6 .black (-4) (initial 3) .black :=
  (sec_sound (n := 6) (by decide) masks6_eq mem_mask6 true (fun _ => fast_margin6) 5 (-4) 80
    (parseHint hintBlack6) black6 white6 (initial 3) .black repr_initial6).1 search_black6

/-- White can secure a win by at least 4 discs. -/
theorem white_secures_6x6 : Secures 6 .white 4 (initial 3) .black :=
  (sec_sound (n := 6) (by decide) masks6_eq mem_mask6 true (fun _ => fast_margin6) 5 4 80
    (parseHint hintWhite6) black6 white6 (initial 3) .black repr_initial6).2 search_white6

/-- **Problem 2.**  The result of 6 × 6 Othello under optimal play: Black has
4 discs fewer than White (16–20). -/
theorem othello_6x6 : OptimalResult 6 (initial 3) .black (-4) :=
  ⟨black_secures_6x6, white_secures_6x6⟩

/-- In particular, White wins 6 × 6 Othello. -/
theorem white_wins_6x6 : Secures 6 .white 1 (initial 3) .black :=
  white_secures_6x6.mono (by decide)

end Othello
