import Othello.Eight.Statement
import Othello.Eight.Takizawa
import Othello.Eight.Hints

/-!
# Problem 3: 8 × 8 Othello is a draw — relative to the published computation

`othello_8x8 : Othello8Draw` is proved here **from the axiom
`takizawa_results`** (`Othello/Eight/Takizawa.lean`), which states that the
2587 positions with 50 empty squares solved for H. Takizawa's "Othello is
Solved" have the values that were computed for them.  The axiom is not
checked by Lean; replaying the computation behind it is out of reach.

What Lean does check is the rest of the argument: starting from the initial
position, a search of the first ten plies (`search8_black`, `search8_white`)
shows that

* Black has a strategy which leads, whatever White does, to positions of the
  table whose value is at least 0, and
* White has a strategy which leads, whatever Black does, to positions of the
  table whose value is at most 0,

so that both players can secure a draw.  The two strategy trees have about
2900 and 10600 nodes; positions are matched with the table up to the
symmetries of the board.  The searches are run with `native_decide`.
-/

namespace Othello

/-- From the initial position, Black can steer the game into positions of the
table in which Black secures a draw. -/
theorem search8_black :
    refSearch 8 tableOracle .black 0 40 (parseRHint hintBlack8)
      (encode 8 (initial 4) .black) (encode 8 (initial 4) .white) .black = true := by
  native_decide

/-- From the initial position, White can steer the game into positions of the
table in which White secures a draw. -/
theorem search8_white :
    refSearch 8 tableOracle .white 0 40 (parseRHint hintWhite8)
      (encode 8 (initial 4) .black) (encode 8 (initial 4) .white) .black = true := by
  native_decide

/-- **Problem 3, relative to the axiom `takizawa_results`.**  From the
standard initial position of 8 × 8 Othello, the game ends in a draw under
optimal play. -/
theorem othello_8x8 : Othello8Draw := by
  have hinit : decodeBoard 8 (encode 8 (initial 4) .black) (encode 8 (initial 4) .white)
      = initial 4 := decode_encode (by decide) (clean_initial 4 (by decide))
  have hb := refSearch_sound (n := 8) (by decide) (tableOracle_sound .black) _ _ _ _ _
    search8_black
  have hw := refSearch_sound (n := 8) (by decide) (tableOracle_sound .white) _ _ _ _ _
    search8_white
  rw [hinit] at hb hw
  exact ⟨hb, hw⟩

/-! ## A consistency check between the table and the published line -/

/-- The first row of the table — the only one whose value is stated to be
exactly 0. -/
def exactRow : String := "------------O------OOX-----XOX----XXOO----XO-O------------------"

/-- Replay the first ten moves of the optimal line of [1] and compare the
position, with its rows reversed, to `exactRow`. -/
def exactRowCheck : Bool :=
  match replay 8 30 (tabulate 8 (initial 4)) .black (takizawaLine.take 10) with
  | none => false
  | some (tbl, c) =>
    decide (c = .black) &&
      decide (tabulate 8 (flipY8.app (ofTable tbl)) = tabulate 8 (boardOfString exactRow))

/-- The position which the table states to be an exact draw is the position
reached by the first ten moves of the optimal line published in [1] (with
Black to move), up to a reflection of the board.  So the table and the line
refer to the same game, and are read here with the same conventions. -/
theorem takizawa_exact_row :
    ∃ b, Record 8 (initial 4) .black (takizawaLine.take 10) b .black ∧
      flipY8.app b = boardOfString exactRow := by
  have h : exactRowCheck = true := by native_decide
  unfold exactRowCheck at h
  split at h
  · cases h
  · rename_i tbl c hrep
    obtain ⟨b, hb, rfl, hrec⟩ := replay_sound _ _ _ _ _ _ (clean_initial 4 (by decide)) hrep
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, ofTable_tabulate hb] at h
    obtain ⟨rfl, htab⟩ := h
    refine ⟨b, hrec, ?_⟩
    have h1 := congrArg ofTable htab
    rwa [ofTable_tabulate (flipY8.clean_app hb),
      ofTable_tabulate (clean_boardOfString exactRow)] at h1

end Othello
