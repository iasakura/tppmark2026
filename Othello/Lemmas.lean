import Othello.Spec

/-!
# Basic facts about the rules

* `Secures.consistent`: the two players cannot both secure more than a
  zero-sum game allows; hence the result under optimal play is unique
  (`OptimalResult.unique`).
* `mem_flipsDir_iff`, `mem_flips_iff`: a declarative ("rule book") description
  of the discs flipped by a move.  It shows that the executable definition
  `flipsDir` of the specification says what the rules of Othello say.
-/

namespace Othello

theorem Color.opponent_opponent (c : Color) : c.opponent.opponent = c := by
  cases c <;> rfl

theorem Color.opponent_ne (c : Color) : c.opponent ≠ c := by
  cases c <;> simp [Color.opponent]

theorem Color.ne_opponent (c : Color) : c ≠ c.opponent := by
  cases c <;> simp [Color.opponent]

theorem Color.eq_opponent_of_ne {c d : Color} (h : c ≠ d) : c = d.opponent := by
  cases c <;> cases d <;> simp_all [Color.opponent]

variable {n : Nat}

theorem margin_opponent (b : Board) (p : Color) :
    margin n b p.opponent = - margin n b p := by
  unfold margin
  rw [Color.opponent_opponent]
  omega

/-! ## Consistency of `Secures` -/

/-- If `p` can secure a margin of `v` and the opponent of `p` can secure a
margin of `w` (for themselves), then `v + w ≤ 0`. -/
theorem Secures.consistent {p : Color} {v w : Int} {b : Board} {c : Color}
    (h₁ : Secures n p v b c) (h₂ : Secures n p.opponent w b c) : v + w ≤ 0 := by
  induction h₁ with
  | over hm ho hv =>
    cases h₂ with
    | over _ _ hw => rw [margin_opponent] at hw; omega
    | pass _ ho' _ => exact absurd ho ho'
    | choose s _ hs _ => rw [hm] at hs; cases hs
    | reply _ hm' _ => exact absurd hm hm'
  | pass hm ho _ ih =>
    cases h₂ with
    | over _ ho' _ => exact absurd ho' ho
    | pass _ _ h => exact ih h
    | choose s _ hs _ => rw [hm] at hs; cases hs
    | reply _ hm' _ => exact absurd hm hm'
  | choose s hc hs _ ih =>
    cases h₂ with
    | over hm' _ _ => rw [hm'] at hs; cases hs
    | pass hm' _ _ => rw [hm'] at hs; cases hs
    | choose s' hc' _ _ => rw [hc] at hc'; exact absurd hc' (Color.ne_opponent _)
    | reply _ _ h => exact ih (h s hs)
  | reply hc hm _ ih =>
    cases h₂ with
    | over hm' _ _ => exact absurd hm' hm
    | pass hm' _ _ => exact absurd hm' hm
    | choose s' _ hs' h => exact ih s' hs' h
    | reply hc' _ _ => exact absurd (Color.eq_opponent_of_ne hc) hc'

/-- The result of a position under optimal play is unique. -/
theorem OptimalResult.unique {b : Board} {c : Color} {v w : Int}
    (hv : OptimalResult n b c v) (hw : OptimalResult n b c w) : v = w := by
  have h₁ := Secures.consistent hv.1 hw.2
  have h₂ := Secures.consistent hw.1 hv.2
  omega

/-- A weaker guarantee is easier to secure. -/
theorem Secures.mono {p : Color} {v v' : Int} {b : Board} {c : Color}
    (h : Secures n p v b c) (hv : v' ≤ v) : Secures n p v' b c := by
  induction h with
  | over hm ho hle => exact .over hm ho (by omega)
  | pass hm ho _ ih => exact .pass hm ho ih
  | choose s hc hs _ ih => exact .choose s hc hs ih
  | reply hc hm _ ih => exact .reply hc hm ih

/-! ## Squares, moves, cells -/

theorem mem_squares {s : Square} : s ∈ squares n ↔ OnBoard n s := by
  unfold squares OnBoard
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, hy, x, hx, rfl⟩
    simp only
    omega
  · intro h
    refine ⟨s.2.toNat, by omega, s.1.toNat, by omega, ?_⟩
    apply Prod.ext <;> simp only <;> omega

theorem mem_moves {b : Board} {c : Color} {s : Square} :
    s ∈ moves n b c ↔ Legal n b c s := by
  unfold moves
  simp only [List.mem_filter, mem_squares, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem cell_eq_some {b : Board} {s : Square} {c : Color}
    (h : cell n b s = some c) : OnBoard n s ∧ b s = some c := by
  unfold cell at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

theorem cell_of_onBoard {b : Board} {s : Square} (h : OnBoard n s) :
    cell n b s = b s := by
  simp [cell, h]

/-! ## The discs flipped by a move, declaratively -/

/-- The square reached from `s` by `j` steps in direction `d`. -/
def far (s : Square) (d : Int × Int) (j : Int) : Square :=
  (s.1 + j * d.1, s.2 + j * d.2)

theorem far_zero (s : Square) (d : Int × Int) : far s d 0 = s := by
  simp [far]

theorem far_one (s : Square) (d : Int × Int) : far s d 1 = step d s := by
  simp [far, step]

theorem step_far (s : Square) (d : Int × Int) (j : Int) :
    step d (far s d j) = far s d (j + 1) := by
  simp only [step, far, Int.add_mul, Int.one_mul, Int.add_assoc]

/-- A straight line of `m + 1` squares fits on the board only if `m < n`. -/
theorem line_fits {s : Square} {d : Int × Int} {m : Int}
    (hd : d ∈ directions) (hs : OnBoard n s) (hm : OnBoard n (far s d m))
    (_h0 : 0 ≤ m) : m < n := by
  simp only [directions, List.mem_cons, List.mem_nil_iff, or_false] at hd
  unfold OnBoard far at *
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only at hm <;> omega

/-- `Outflank n b c s d m`: in direction `d` from `s`, the squares at
distances `1, …, m-1` hold discs of the opponent of `c`, and the square at
distance `m` holds a disc of `c`. -/
def Outflank (n : Nat) (b : Board) (c : Color) (s : Square) (d : Int × Int) (m : Int) : Prop :=
  (∀ j, 1 ≤ j → j < m → cell n b (far s d j) = some c.opponent) ∧
  cell n b (far s d m) = some c

theorem mem_run_iff {b : Board} {c : Color} {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s) :
    ∀ (k : Nat) (j0 : Int) (acc : List Square),
      1 ≤ j0 → (n : Int) ≤ j0 + k →
      (∀ j, 1 ≤ j → j < j0 → cell n b (far s d j) = some c.opponent) →
      (∀ q, q ∈ acc ↔ ∃ i, 1 ≤ i ∧ i < j0 ∧ q = far s d i) →
      ∀ q, q ∈ run n b c d k (far s d j0) acc ↔
        ∃ m, j0 ≤ m ∧ Outflank n b c s d m ∧ ∃ i, 1 ≤ i ∧ i < m ∧ q = far s d i := by
  intro k
  induction k with
  | zero =>
    intro j0 acc hj0 hfuel hpre hacc q
    simp only [run, List.not_mem_nil, false_iff]
    rintro ⟨m, hm, ⟨_, hc⟩, _⟩
    have h1 := line_fits hd hs (cell_eq_some hc).1 (by omega)
    omega
  | succ k ih =>
    intro j0 acc hj0 hfuel hpre hacc q
    simp only [run]
    cases hcell : cell n b (far s d j0) with
    | none =>
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨m, hm, ⟨hop, hc⟩, _⟩
      by_cases hmj : m = j0
      · subst hmj; rw [hc] at hcell; cases hcell
      · rw [hop j0 hj0 (by omega)] at hcell; cases hcell
    | some c' =>
      by_cases hcc : c' = c
      · subst hcc
        simp only [↓reduceIte]
        rw [hacc]
        constructor
        · rintro ⟨i, hi1, hi2, rfl⟩
          exact ⟨j0, Int.le_refl _, ⟨hpre, hcell⟩, i, hi1, hi2, rfl⟩
        · rintro ⟨m, hm, ⟨hop, hc⟩, i, hi1, hi2, rfl⟩
          have hmj : m = j0 := by
            apply Classical.byContradiction
            intro hne
            rw [hop j0 hj0 (by omega)] at hcell
            exact absurd (Option.some.inj hcell) (Color.opponent_ne _)
          subst hmj
          exact ⟨i, hi1, hi2, rfl⟩
      · have hc' : c' = c.opponent := Color.eq_opponent_of_ne hcc
        subst hc'
        simp only [hcc, ↓reduceIte]
        rw [step_far]
        rw [ih (j0 + 1) (far s d j0 :: acc) (by omega) (by omega)]
        · constructor
          · rintro ⟨m, hm, r⟩
            exact ⟨m, by omega, r⟩
          · rintro ⟨m, hm, ⟨hop, hc⟩, r⟩
            refine ⟨m, ?_, ⟨hop, hc⟩, r⟩
            apply Classical.byContradiction
            intro hlt
            have hmj : m = j0 := by omega
            subst hmj
            rw [hc] at hcell
            exact absurd (Option.some.inj hcell) (Color.ne_opponent _)
        · intro j hj1 hj2
          by_cases hjj : j = j0
          · subst hjj; exact hcell
          · exact hpre j hj1 (by omega)
        · intro q'
          simp only [List.mem_cons, hacc]
          constructor
          · rintro (rfl | ⟨i, hi1, hi2, rfl⟩)
            · exact ⟨j0, hj0, by omega, rfl⟩
            · exact ⟨i, hi1, by omega, rfl⟩
          · rintro ⟨i, hi1, hi2, rfl⟩
            by_cases hij : i = j0
            · subst hij; exact Or.inl rfl
            · exact Or.inr ⟨i, hi1, by omega, rfl⟩

/-- The rule of the game: a disc is flipped by `c`'s move on `s` in direction
`d` iff it lies strictly between `s` and a disc of `c` on a straight line in
direction `d`, all of whose intermediate squares hold discs of the opponent. -/
theorem mem_flipsDir_iff {b : Board} {c : Color} {s : Square} {d : Int × Int}
    (hd : d ∈ directions) (hs : OnBoard n s) (q : Square) :
    q ∈ flipsDir n b c s d ↔
      ∃ m, Outflank n b c s d m ∧ ∃ i, 1 ≤ i ∧ i < m ∧ q = far s d i := by
  unfold flipsDir
  rw [← far_one]
  have hn : (0 : Int) < n := by unfold OnBoard at hs; omega
  rw [mem_run_iff hd hs n 1 [] (by omega) (by omega)]
  · constructor
    · rintro ⟨m, _, r⟩
      exact ⟨m, r⟩
    · rintro ⟨m, ho, i, hi1, hi2, rfl⟩
      exact ⟨m, by omega, ho, i, hi1, hi2, rfl⟩
  · intro j h1 h2
    omega
  · intro q'
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨i, h1, h2, _⟩
    omega

theorem mem_flips_iff {b : Board} {c : Color} {s : Square}
    (hs : OnBoard n s) (q : Square) :
    q ∈ flips n b c s ↔
      ∃ d, d ∈ directions ∧
        ∃ m, Outflank n b c s d m ∧ ∃ i, 1 ≤ i ∧ i < m ∧ q = far s d i := by
  unfold flips
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨d, hd, hq⟩
    exact ⟨d, hd, (mem_flipsDir_iff hd hs q).1 hq⟩
  · rintro ⟨d, hd, r⟩
    exact ⟨d, hd, (mem_flipsDir_iff hd hs q).2 r⟩

end Othello
