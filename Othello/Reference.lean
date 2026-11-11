import Othello.Lemmas

/-!
# A reference search, directly on the specification

`refSecures` searches the game tree using nothing but the functions of the
specification (`moves`, `play`, `margin`), for any board size.  Its soundness
proof (`refSecures_sound`) is a few lines, because there is no change of
representation to justify.

It is slow — far too slow for 6 × 6 — but it works for 8 × 8, where the
bitboards of `Othello/Bitboard.lean` do not apply.  It is used to state the
reduction of Problem 3 to a finite computation, and to check small facts
about the 8 × 8 game.

To keep evaluation feasible, a board is re-tabulated after every move
(`tabulate` / `ofTable`): otherwise looking up a square would replay the whole
history of the game.
-/

namespace Othello

variable {n : Nat}

/-! ## Boards as tables -/

/-- A board with nothing outside the `n × n` squares. -/
def Clean (n : Nat) (b : Board) : Prop := ∀ s, ¬ OnBoard n s → b s = none

/-- The contents of all squares of the board, as an association list. -/
def tabulate (n : Nat) (b : Board) : List (Square × Option Color) :=
  (squares n).map fun s => (s, b s)

/-- The board described by an association list. -/
def ofTable (t : List (Square × Option Color)) : Board :=
  fun s => (t.lookup s).getD none

theorem lookup_map_self (f : Square → Option Color) (s : Square) :
    ∀ l : List Square,
      (l.map fun q => (q, f q)).lookup s = if s ∈ l then some (f s) else none := by
  intro l
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.lookup_cons, List.mem_cons]
    by_cases h : s = q
    · subst h
      simp
    · have h' : (s == q) = false := by simpa using h
      rw [h', ih]
      simp [h]

/-- Tabulating a clean board and reading the table back gives the same board. -/
theorem ofTable_tabulate {b : Board} (hb : Clean n b) : ofTable (tabulate n b) = b := by
  funext s
  unfold ofTable tabulate
  rw [lookup_map_self]
  by_cases hs : OnBoard n s
  · simp [mem_squares.2 hs]
  · have : s ∉ squares n := fun h => hs (mem_squares.1 h)
    simp [this, hb s hs]

theorem clean_play {b : Board} {c : Color} {s : Square} (hb : Clean n b)
    (hs : OnBoard n s) : Clean n (play n b c s) := by
  intro q hq
  unfold play
  have h1 : q ≠ s := fun h => hq (h ▸ hs)
  have h2 : q ∉ flips n b c s := fun h => hq (by
    rw [mem_flips_iff hs] at h
    obtain ⟨d, _, m, ⟨hop, _⟩, i, hi1, hi2, rfl⟩ := h
    exact (cell_eq_some (hop i hi1 hi2)).1)
  simp [h1, h2, hb q hq]

theorem clean_initial (h : Nat) (hh : 1 ≤ h) : Clean (2 * h) (initial h) := by
  intro s hs
  unfold initial
  unfold OnBoard at hs
  have e1 : ¬ (s = ((h : Int) - 1, (h : Int) - 1) ∨ s = ((h : Int), (h : Int))) := by
    rintro (rfl | rfl) <;> simp only at hs <;> omega
  have e2 : ¬ (s = ((h : Int), (h : Int) - 1) ∨ s = ((h : Int) - 1, (h : Int))) := by
    rintro (rfl | rfl) <;> simp only at hs <;> omega
  simp [e1, e2]

/-- The table of the board after `c` has played on `s`.  (Same as
`tabulate n (play n b c s)`, but the flipped discs are computed only once.) -/
def tabPlay (n : Nat) (b : Board) (c : Color) (s : Square) : List (Square × Option Color) :=
  let fl := flips n b c s
  (squares n).map fun q => (q, if q = s ∨ q ∈ fl then some c else b q)

theorem tabPlay_eq (b : Board) (c : Color) (s : Square) :
    tabPlay n b c s = tabulate n (play n b c s) := rfl

/-! ## The reference search -/

/-- `refSecures n p t fuel tbl c = true` only if, on the board with table
`tbl` and `c` to move, player `p` can secure a margin of at least `t`. -/
def refSecures (n : Nat) (p : Color) (t : Int) :
    Nat → List (Square × Option Color) → Color → Bool
  | 0, _, _ => false
  | fuel + 1, tbl, c =>
    let b := ofTable tbl
    match moves n b c with
    | [] =>
      if moves n b c.opponent = [] then decide (t ≤ margin n b p)
      else refSecures n p t fuel tbl c.opponent
    | s :: ss =>
      if c = p then
        (s :: ss).any fun s => refSecures n p t fuel (tabPlay n b c s) c.opponent
      else
        (s :: ss).all fun s => refSecures n p t fuel (tabPlay n b c s) c.opponent

/-- A successful reference search is a strategy. -/
theorem refSecures_sound (p : Color) (t : Int) :
    ∀ (fuel : Nat) (b : Board) (c : Color), Clean n b →
      refSecures n p t fuel (tabulate n b) c = true → Secures n p t b c := by
  intro fuel
  induction fuel with
  | zero =>
    intro b c _ h
    simp [refSecures] at h
  | succ fuel ih =>
    intro b c hb h
    simp only [refSecures, ofTable_tabulate hb, tabPlay_eq] at h
    split at h
    · rename_i hm
      split at h
      · rename_i ho
        exact .over hm ho (of_decide_eq_true h)
      · rename_i ho
        exact .pass hm ho (ih b c.opponent hb h)
    · rename_i s ss hm
      have hne : moves n b c ≠ [] := by rw [hm]; exact List.cons_ne_nil _ _
      split at h
      · rename_i hc
        rw [List.any_eq_true] at h
        obtain ⟨s', hs', h'⟩ := h
        rw [← hm] at hs'
        have hlegal := mem_moves.1 hs'
        exact .choose s' hc hs' (ih _ _ (clean_play hb hlegal.1) h')
      · rename_i hc
        rw [List.all_eq_true] at h
        refine .reply hc hne ?_
        intro s' hs'
        have hlegal := mem_moves.1 hs'
        exact ih _ _ (clean_play hb hlegal.1) (h s' (by rw [← hm]; exact hs'))

/-! ## Game records -/

/-- `Record n b c ms b' c'`: starting from board `b` with `c` to move, the
moves `ms` can be played in this order according to the rules (a player
without a legal move passes), and lead to the board `b'` with `c'` to move. -/
inductive Record (n : Nat) : Board → Color → List Square → Board → Color → Prop where
  | done {b c} : Record n b c [] b c
  | move {b c s ms b' c'} :
      s ∈ moves n b c → Record n (play n b c s) c.opponent ms b' c' →
      Record n b c (s :: ms) b' c'
  | pass {b c ms b' c'} :
      moves n b c = [] → moves n b c.opponent ≠ [] → Record n b c.opponent ms b' c' →
      Record n b c ms b' c'

/-- Replay a game record; returns the table of the final board and the player
to move. -/
def replay (n : Nat) : Nat → List (Square × Option Color) → Color → List Square →
    Option (List (Square × Option Color) × Color)
  | 0, _, _, _ => none
  | _ + 1, tbl, c, [] => some (tbl, c)
  | fuel + 1, tbl, c, s :: ms =>
    let b := ofTable tbl
    if Legal n b c s then replay n fuel (tabPlay n b c s) c.opponent ms
    else if moves n b c = [] ∧ moves n b c.opponent ≠ [] then
      replay n fuel tbl c.opponent (s :: ms)
    else none

theorem replay_sound :
    ∀ (fuel : Nat) (b : Board) (c : Color) (ms : List Square)
      (tbl' : List (Square × Option Color)) (c' : Color), Clean n b →
      replay n fuel (tabulate n b) c ms = some (tbl', c') →
      ∃ b', Clean n b' ∧ tbl' = tabulate n b' ∧ Record n b c ms b' c' := by
  intro fuel
  induction fuel with
  | zero =>
    intro b c ms tbl' c' _ h
    simp [replay] at h
  | succ fuel ih =>
    intro b c ms tbl' c' hb h
    cases ms with
    | nil =>
      simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact ⟨b, hb, h1.symm, .done⟩
    | cons s ms =>
      simp only [replay, ofTable_tabulate hb, tabPlay_eq] at h
      split at h
      · rename_i hlegal
        obtain ⟨b', hb', e, hrec⟩ := ih _ _ _ _ _ (clean_play hb hlegal.1) h
        exact ⟨b', hb', e, .move (mem_moves.2 hlegal) hrec⟩
      · split at h
        · rename_i hpass
          obtain ⟨b', hb', e, hrec⟩ := ih _ _ _ _ _ hb h
          exact ⟨b', hb', e, .pass hpass.1 hpass.2 hrec⟩
        · cases h

/-- Replay a record from the initial position and check that the game is
then over with the given numbers of discs. -/
def checkRecord (n h : Nat) (ms : List Square) (kb kw : Nat) : Bool :=
  match replay n (2 * ms.length + 2) (tabulate n (initial h)) .black ms with
  | none => false
  | some (tbl, _) =>
    let b := ofTable tbl
    decide (moves n b .black = []) && decide (moves n b .white = []) &&
    decide (count n b .black = kb) && decide (count n b .white = kw)

/-- `FinishedGame n h ms kb kw`: the moves `ms` form a complete legal game on
the `n × n` board from the initial position, ending with `kb` black and `kw`
white discs. -/
def FinishedGame (n h : Nat) (ms : List Square) (kb kw : Nat) : Prop :=
  ∃ b' c', Record n (initial h) .black ms b' c' ∧
    moves n b' .black = [] ∧ moves n b' .white = [] ∧
    count n b' .black = kb ∧ count n b' .white = kw

theorem checkRecord_sound {h : Nat} (hh : 1 ≤ h) {ms : List Square} {kb kw : Nat}
    (hc : checkRecord (2 * h) h ms kb kw = true) : FinishedGame (2 * h) h ms kb kw := by
  unfold checkRecord at hc
  split at hc
  · cases hc
  · rename_i tbl c' hrep
    obtain ⟨b', hb', rfl, hrec⟩ := replay_sound _ _ _ _ _ _ (clean_initial h hh) hrep
    simp only [ofTable_tabulate hb', Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨b', c', hrec, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

end Othello
