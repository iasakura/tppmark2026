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
* Problem 2 (6 × 6) additionally depends on axioms recording the results of
  compiled computations: its two game-tree searches (`native_decide`) and the
  certificate check of `bv_decide`.
* Problem 3 (8 × 8) depends on the axiom `takizawa_results` — the table of
  2587 positions computed for "Othello is Solved", which Lean has not
  checked — and on two `native_decide` searches.
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
#print axioms secures_sym_iff

-- Problem 3: "if the published table is correct, 8 × 8 Othello is a draw"
#print axioms othello_8x8_of_table

-- Problem 3, relative to the published computation (axiom `takizawa_results`)
#print axioms othello_8x8

#print axioms takizawa_exact_row

-- Problem 3: what is proved without that axiom
#print axioms othello8_result_exists
#print axioms othello8_draw_of_search
#print axioms perft8
#print axioms takizawa_line
#print axioms takizawa_line_tail

-- Games realising the optimal results
#print axioms line4_finished
#print axioms line6_finished
