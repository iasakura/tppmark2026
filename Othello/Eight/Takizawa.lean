import Othello.Symmetry
import Othello.Encode
import Othello.Eight.Table

/-!
# The computational result of "Othello is Solved", as an axiom

H. Takizawa's proof that 8 × 8 Othello is a draw [1] has two parts.

1. A very large computation (about 1.5 × 10¹⁸ positions searched) which
   determines, for each of 2587 positions with 50 empty squares, a bound on
   its game-theoretic value: the value is at least 0, or at most 0, or — for
   one position — exactly 0.  These positions and the bounds that were
   needed for them are published as `empty50_tasklist_edax_knowledge.csv`;
   `Othello/Eight/Table.lean` reproduces that file.
2. A small search of the first ten plies of the game, which derives from
   these bounds that the initial position is a draw.

Part 1 cannot be replayed inside a proof assistant with today's means.  It
enters this development as the axiom `takizawa_results` below, which says:
*every row of the table is correct*.  This is the only place where the
development relies on something that Lean has not checked.  (The published
file lists the bounds that were *needed*; the paper reports that all of them
were established.  The individual computation results, which are available
separately, have not been examined here.)

Part 2 is checked: `Othello/Eight.lean` derives the draw from the axiom by a
verified search.

The rest of this file makes the table usable by that search
(`tableOracle`, `tableOracle_sound`); positions are matched up to the eight
symmetries of the board, which is justified by `secures_sym_iff`.
-/

namespace Othello

/-- The board written as 64 characters, row by row starting from A1:
`X` is a black disc, `O` a white disc, anything else an empty square. -/
def boardOfString (str : String) : Board := fun s =>
  if OnBoard 8 s then
    match str.toList[bitIdx s]? with
    | some 'X' => some .black
    | some 'O' => some .white
    | _ => none
  else none

/-- What the computation of [1] established for a row of the table.  The row
gives a position with Black to move, the score `score` predicted for it, and
the window `(alpha, beta)` in which it had to be solved:

* if the prediction is inside the window, the value was determined exactly,
  and it is the predicted one;
* if the prediction is at least `beta`, the value was shown to be at least
  `beta`: Black can secure a margin of `beta`;
* if the prediction is at most `alpha`, the value was shown to be at most
  `alpha`: White can secure a margin of `-alpha`.

(In the table, `alpha` and `beta` are always `0` in the last two cases and
the score is `0` in the first, see `takizawaTable_shapes`.  So every row is a
statement about who can secure a draw, and does not depend on how the discs
are counted when a game ends with empty squares.) -/
def Entry.Holds (e : Entry) : Prop :=
  if e.alpha < e.score ∧ e.score < e.beta then
    OptimalResult 8 (boardOfString e.board) .black e.score
  else if e.beta ≤ e.score then
    Secures 8 .black e.beta (boardOfString e.board) .black
  else
    Secures 8 .white (-e.alpha) (boardOfString e.board) .black

/-! ## The table, checked for shape -/

theorem takizawaTable_length : takizawaTable.length = 2587 := by decide +kernel

/-- Every row asks for "at least a draw" (1639 rows), "at most a draw" (947
rows) or "exactly a draw" (1 row). -/
theorem takizawaTable_shapes : ∀ e, e ∈ takizawaTable →
    (e.alpha = -64 ∧ e.beta = 0 ∧ 0 ≤ e.score) ∨
    (e.alpha = 0 ∧ e.beta = 64 ∧ e.score ≤ 0) ∨
    (e.alpha = -64 ∧ e.beta = 64 ∧ e.score = 0) := by
  decide +kernel

/-! ## The symmetries of the 8 × 8 board -/

def transpose8 : BoardSym 8 := transposeSym 8 (by decide +kernel)
def flipX8 : BoardSym 8 := flipXSym 8 (by decide +kernel)
def flipY8 : BoardSym 8 := flipYSym 8 (by decide +kernel)

/-- The eight symmetries of the board: transpose if `k.1`, then reverse the
columns if `k.2.1`, then reverse the rows if `k.2.2`. -/
def sym8 (k : Bool × Bool × Bool) (brd : Board) : Board :=
  let b1 := if k.1 then transpose8.app brd else brd
  let b2 := if k.2.1 then flipX8.app b1 else b1
  if k.2.2 then flipY8.app b2 else b2

def allSyms : List (Bool × Bool × Bool) :=
  [(false, false, false), (true, false, false), (false, true, false), (true, true, false),
   (false, false, true), (true, false, true), (false, true, true), (true, true, true)]

theorem secures_sym8 (k : Bool × Bool × Bool) {p : Color} {v : Int} {brd : Board} {c : Color} :
    Secures 8 p v (sym8 k brd) c ↔ Secures 8 p v brd c := by
  obtain ⟨a, b, c'⟩ := k
  cases a <;> cases b <;> cases c' <;> simp [sym8, secures_sym_iff]

theorem BoardSym.clean_app {n : Nat} (σ : BoardSym n) {b : Board} (h : Clean n b) :
    Clean n (σ.app b) := by
  intro s hs
  exact h (σ.f s) (fun h' => hs ((σ.onBoard s).1 h'))

theorem clean_sym8 (k : Bool × Bool × Bool) {brd : Board} (h : Clean 8 brd) :
    Clean 8 (sym8 k brd) := by
  obtain ⟨a, b, c'⟩ := k
  cases a <;> cases b <;> cases c' <;> simp only [sym8, Bool.false_eq_true, ↓reduceIte] <;>
    first
    | exact h
    | exact BoardSym.clean_app _ h
    | exact BoardSym.clean_app _ (BoardSym.clean_app _ h)
    | exact BoardSym.clean_app _ (BoardSym.clean_app _ (BoardSym.clean_app _ h))

/-! ## The table as an oracle -/

/-- Does the row say that `p` can secure a draw? -/
def Entry.supports (e : Entry) (p : Color) : Bool :=
  if e.alpha < e.score ∧ e.score < e.beta then
    match p with
    | .black => decide (0 ≤ e.score)
    | .white => decide (e.score ≤ 0)
  else if e.beta ≤ e.score then
    match p with
    | .black => decide (0 ≤ e.beta)
    | .white => false
  else
    match p with
    | .black => false
    | .white => decide (e.alpha ≤ 0)

theorem Entry.secures_of_supports {e : Entry} (h : e.Holds) {p : Color}
    (hp : e.supports p = true) : Secures 8 p 0 (boardOfString e.board) .black := by
  unfold Entry.Holds at h
  unfold Entry.supports at hp
  split at h
  · rename_i hex
    simp only [hex, and_self, ↓reduceIte] at hp
    cases p with
    | black => exact h.1.mono (of_decide_eq_true hp)
    | white => exact h.2.mono (by have := of_decide_eq_true hp; omega)
  · rename_i hex
    simp only [hex, ↓reduceIte] at hp
    split at h
    · rename_i hb
      simp only [hb, ↓reduceIte] at hp
      cases p with
      | black => exact h.mono (of_decide_eq_true hp)
      | white => cases hp
    · rename_i hb
      simp only [hb, ↓reduceIte] at hp
      cases p with
      | black => cases hp
      | white => exact h.mono (by have := of_decide_eq_true hp; omega)

theorem clean_boardOfString (str : String) : Clean 8 (boardOfString str) := by
  intro s hs
  simp [boardOfString, hs]

/-- The rows of the table as pairs of bit sets, with what they say about
Black and about White. -/
def takizawaEncoded : List (Nat × Nat × Bool × Bool) :=
  takizawaTable.map fun e =>
    (encode 8 (boardOfString e.board) .black, encode 8 (boardOfString e.board) .white,
      e.supports .black, e.supports .white)

/-- `tableOracle p bl wh c`: the position (Black to move, 14 discs) is, up to
a symmetry of the board, a row of the table which says that `p` can secure a
draw. -/
def tableOracle (p : Color) (bl wh : Nat) (c : Color) : Bool :=
  let brd := decodeBoard 8 bl wh
  decide (c = .black) && decide (count 8 brd .black + count 8 brd .white = 14) &&
  allSyms.any fun k =>
    let brd' := sym8 k brd
    let bl' := encode 8 brd' .black
    let wh' := encode 8 brd' .white
    takizawaEncoded.any fun x =>
      x.1 == bl' && x.2.1 == wh' &&
        (match p with
         | .black => x.2.2.1
         | .white => x.2.2.2)

/-- If the table is correct, the oracle only accepts positions in which `p`
can secure a draw. -/
theorem tableOracle_sound (htable : ∀ e, e ∈ takizawaTable → e.Holds)
    (p : Color) (bl wh : Nat) (c : Color)
    (h : tableOracle p bl wh c = true) : Secures 8 p 0 (decodeBoard 8 bl wh) c := by
  unfold tableOracle at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, _⟩, k, _, x, hx, ⟨hbl, hwh⟩, hsup⟩ := h
  subst hc
  unfold takizawaEncoded at hx
  rw [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  simp only at hbl hwh hsup
  have h1 : decodeBoard 8 (encode 8 (boardOfString e.board) .black)
      (encode 8 (boardOfString e.board) .white) = boardOfString e.board :=
    decode_encode (by decide) (clean_boardOfString _)
  have h2 : decodeBoard 8 (encode 8 (sym8 k (decodeBoard 8 bl wh)) .black)
      (encode 8 (sym8 k (decodeBoard 8 bl wh)) .white) = sym8 k (decodeBoard 8 bl wh) :=
    decode_encode (by decide) (clean_sym8 k (clean_decodeBoard bl wh))
  rw [hbl, hwh, h2] at h1
  have hsup' : e.supports p = true := by
    cases p <;> exact hsup
  have h3 := Entry.secures_of_supports (htable e he) hsup'
  rw [← h1] at h3
  exact (secures_sym8 k).1 h3

/-! ## The axiom -/

/-- **Axiom: the computational result of H. Takizawa, "Othello is Solved"
(arXiv:2310.19387).**  Every row of the published table of 2587 positions
with 50 empty squares is correct.

This statement has *not* been checked by Lean.  It records the outcome of a
computation of about 1.5 × 10¹⁸ search nodes carried out for [1]. -/
axiom takizawa_results : ∀ e, e ∈ takizawaTable → e.Holds

end Othello
