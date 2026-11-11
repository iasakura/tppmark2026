import Othello.Four
import Othello.Six
import Othello.Eight
import Othello.Lines
import Othello.Determinacy

/-!
# The axioms behind the main theorems

Compiling this file prints, for each main theorem, the axioms it depends on.

* Problem 1 (4 × 4) and the general theory use only the three standard axioms
  `propext`, `Classical.choice`, `Quot.sound`: all computations are checked by
  the kernel.
* Problem 2 (6 × 6) additionally depends on `Lean.ofReduceBool` and
  `Lean.trustCompiler`: its game-tree searches are run as compiled code
  (`native_decide`), and so is the checker used by `bv_decide`.
-/

open Othello

-- Problem 1
#print axioms white_wins_4x4
#print axioms othello_4x4

-- Problem 2
#print axioms othello_6x6

-- General theory
#print axioms sec_sound
#print axioms OptimalResult.unique
#print axioms exists_optimalResult

-- Problem 3: what is proved
#print axioms othello8_draw_of_search
#print axioms perft8
#print axioms takizawa_line
#print axioms takizawa_line_tail
