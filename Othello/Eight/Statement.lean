import Othello.Reference
import Othello.Determinacy

/-!
# Problem 3: 8 × 8 Othello — the statement, and what can be checked directly

**Statement.**  From the standard initial position of 8 × 8 Othello, the game
ends in a draw under optimal play (`Othello8Draw`).

This is the theorem of H. Takizawa, "Othello is Solved" (arXiv:2310.19387),
whose proof is a computer search of about 1.5 × 10¹⁸ positions.  A proof
assistant cannot replay a search of that size.  `Othello/Eight.lean` derives
`Othello8Draw` from an axiom which records the result of that computation.

This file contains what is proved about 8 × 8 Othello *without* that axiom:

* `othello8_result_exists`: the result of 8 × 8 Othello under optimal play is
  a well-defined number (Problem 3 says that this number is 0);
* `othello8_draw_of_search`: the statement is equivalent to a finite
  computation in the sense that it follows from two runs of the reference
  search of `Othello/Reference.lean` (which are far too large to carry out);
* `perft8`: the rules of the specification, instantiated at `n = 8`, produce
  the known numbers of games of length 1, …, 6 (4, 12, 56, 244, 1396, 8200),
  a standard test of Othello move generators;
* `takizawa_line`: the optimal line published in [1] is a complete legal game
  of the specification and ends 32–32;
* `takizawa_line_tail`: the last 14 moves of this line are optimal play —
  every position the line visits after its 46th move is a draw under optimal
  play.

The computations of this file are run with `native_decide`.
-/

namespace Othello

/-- **Problem 3 (statement).**  The result of 8 × 8 Othello under optimal play
is a draw: Black can secure at least a draw, and so can White. -/
def Othello8Draw : Prop := OptimalResult 8 (initial 4) .black 0

/-- The result of 8 × 8 Othello under optimal play exists and is unique, by
the general determinacy theorem.  Problem 3 claims that it is 0. -/
theorem othello8_result_exists :
    ∃ v, OptimalResult 8 (initial 4) .black v ∧
      ∀ w, OptimalResult 8 (initial 4) .black w → w = v :=
  existsUnique_optimalResult _ _

/-- Problem 3 is reduced to a finite computation: two runs of the reference
search.  (The computation is far too large to be carried out.) -/
theorem othello8_draw_of_search (fuel : Nat)
    (hb : refSecures 8 .black 0 fuel (tabulate 8 (initial 4)) .black = true)
    (hw : refSecures 8 .white 0 fuel (tabulate 8 (initial 4)) .black = true) :
    Othello8Draw :=
  ⟨refSecures_sound .black 0 fuel _ _ (clean_initial 4 (by decide)) hb,
   refSecures_sound .white 0 fuel _ _ (clean_initial 4 (by decide)) hw⟩

/-! ## A test of the rules: counting games -/

/-- The number of ways the game can go during `d` plies (a forced pass counts
as a ply; a finished game counts once). -/
def perft (n : Nat) : Nat → List (Square × Option Color) → Color → Nat
  | 0, _, _ => 1
  | d + 1, tbl, c =>
    let b := ofTable tbl
    match moves n b c with
    | [] => if moves n b c.opponent = [] then 1 else perft n d tbl c.opponent
    | s :: ss =>
      ((s :: ss).map fun s => perft n d (tabPlay n b c s) c.opponent).sum

/-- The specification generates the known numbers of 8 × 8 Othello games of
length 1 to 6. -/
theorem perft8 :
    (List.range 6).map (fun d => perft 8 (d + 1) (tabulate 8 (initial 4)) .black)
      = [4, 12, 56, 244, 1396, 8200] := by
  native_decide

/-! ## The optimal line of [1] -/

/-- The game record given in [1] as an optimal line (both sides play
perfectly and the game is drawn):

    F5 D6 C3 D3 C4 F4 F6 F3 E6 E7 D7 C5 B6 D8 C6 C7 D2 B5 A5 A6
    A7 G5 E3 B4 C8 G6 G4 C2 E8 D1 F7 E2 G3 H4 F1 E1 F2 G1 B1 F8
    G8 B3 H3 B2 H5 B7 A3 A4 A1 A2 C1 H2 H1 G2 B8 A8 G7 H8 H7 H6

Squares are written `(column, row)` with `A1 = (0, 0)` and `H8 = (7, 7)`. -/
def takizawaLine : List Square :=
  [(5, 4), (3, 5), (2, 2), (3, 2), (2, 3), (5, 3), (5, 5), (5, 2), (4, 5), (4, 6),
   (3, 6), (2, 4), (1, 5), (3, 7), (2, 5), (2, 6), (3, 1), (1, 4), (0, 4), (0, 5),
   (0, 6), (6, 4), (4, 2), (1, 3), (2, 7), (6, 5), (6, 3), (2, 1), (4, 7), (3, 0),
   (5, 6), (4, 1), (6, 2), (7, 3), (5, 0), (4, 0), (5, 1), (6, 0), (1, 0), (5, 7),
   (6, 7), (1, 2), (7, 2), (1, 1), (7, 4), (1, 6), (0, 2), (0, 3), (0, 0), (0, 1),
   (2, 0), (7, 1), (7, 0), (6, 1), (1, 7), (0, 7), (6, 6), (7, 7), (7, 6), (7, 5)]

/-- The optimal line of [1] is a complete legal game of the specification, and
it ends in a draw, 32–32. -/
theorem takizawa_line : FinishedGame 8 4 takizawaLine 32 32 :=
  checkRecord_sound (h := 4) (by decide) (by native_decide)

/-- Replay the first `k` moves of the line, then run the reference search for
both players (each trying to secure a draw). -/
def checkTail (k fuel : Nat) : Bool :=
  match replay 8 (2 * k + 2) (tabulate 8 (initial 4)) .black (takizawaLine.take k) with
  | none => false
  | some (tbl, c) => refSecures 8 .black 0 fuel tbl c && refSecures 8 .white 0 fuel tbl c

theorem checkTail_sound {k fuel : Nat} (h : checkTail k fuel = true) :
    ∃ b c, Record 8 (initial 4) .black (takizawaLine.take k) b c ∧ OptimalResult 8 b c 0 := by
  unfold checkTail at h
  split at h
  · cases h
  · rename_i tbl c hrep
    obtain ⟨b, hb, rfl, hrec⟩ := replay_sound _ _ _ _ _ _ (clean_initial 4 (by decide)) hrep
    rw [Bool.and_eq_true] at h
    exact ⟨b, c, hrec, refSecures_sound .black 0 fuel b c hb h.1,
      refSecures_sound .white 0 fuel b c hb h.2⟩

set_option maxHeartbeats 0 in
/-- The end of the optimal line of [1] is optimal play: every position the
line visits after its 46th move (from then on at most 14 squares are empty)
is a draw under optimal play.  In particular, each of the last 14 moves keeps
the draw. -/
theorem takizawa_line_tail (k : Nat) (h1 : 46 ≤ k) (h2 : k ≤ 60) :
    ∃ b c, Record 8 (initial 4) .black (takizawaLine.take k) b c ∧ OptimalResult 8 b c 0 := by
  have h : (List.range 15).all (fun i => checkTail (46 + i) 40) = true := by native_decide
  rw [List.all_eq_true] at h
  have h3 := h (k - 46) (by rw [List.mem_range]; omega)
  have e : 46 + (k - 46) = k := by omega
  rw [e] at h3
  exact checkTail_sound h3

end Othello
