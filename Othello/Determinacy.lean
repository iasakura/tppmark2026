import Othello.Lemmas

/-!
# Every position has a result under optimal play

`exists_optimalResult`: for every board and every player to move there is a
`v` with `OptimalResult n b c v`.  Together with `OptimalResult.unique` this
shows that "the result under optimal play" is a well-defined number
(`existsUnique_optimalResult`), for every board size — in particular for
8 × 8, where this development does not determine it.

The proof is the usual backward induction; the game is finite because every
move fills an empty square, and two passes in a row end the game.
-/

namespace Othello

variable {n : Nat}

/-- The number of empty squares of the board. -/
def emptyCount (n : Nat) (b : Board) : Nat :=
  ((squares n).filter fun s => b s = none).length

theorem length_filter_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hp : p a with
    | true =>
      have hq : q a = true := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      simp only [List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q a with
      | true =>
        rw [List.filter_cons_of_pos hq]
        simp only [List.length_cons]
        omega
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact ih'

theorem length_filter_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = true → q x = true) →
      (∃ x, x ∈ l ∧ q x = true ∧ p x = false) →
      (l.filter p).length < (l.filter q).length := by
  intro l
  induction l with
  | nil =>
    rintro _ ⟨x, hx, _⟩
    cases hx
  | cons a l ih =>
    intro h hex
    have himp : ∀ x, x ∈ l → p x = true → q x = true :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases hp : p a with
    | true =>
      have hq : q a = true := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      simp only [List.length_cons]
      obtain ⟨x, hx, hqx, hpx⟩ := hex
      rcases List.mem_cons.1 hx with rfl | hx'
      · rw [hp] at hpx; cases hpx
      · have := ih himp ⟨x, hx', hqx, hpx⟩
        omega
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q a with
      | true =>
        rw [List.filter_cons_of_pos hq]
        simp only [List.length_cons]
        have := length_filter_le_of_imp p q l himp
        omega
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        obtain ⟨x, hx, hqx, hpx⟩ := hex
        rcases List.mem_cons.1 hx with rfl | hx'
        · rw [hq] at hqx; cases hqx
        · exact ih himp ⟨x, hx', hqx, hpx⟩

/-- A move fills an empty square. -/
theorem emptyCount_play_lt {b : Board} {c : Color} {s : Square} (h : Legal n b c s) :
    emptyCount n (play n b c s) < emptyCount n b := by
  unfold emptyCount
  apply length_filter_lt_of_imp
  · intro q _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    unfold play at hq
    split at hq
    · cases hq
    · exact hq
  · refine ⟨s, mem_squares.2 h.1, by simpa using h.2.1, ?_⟩
    simp [play]

/-- Among finitely many alternatives each of which has a value, one has the
largest value. -/
theorem exists_max {α : Type} (R : α → Int → Prop) :
    ∀ (l : List α), l ≠ [] → (∀ x, x ∈ l → ∃ v, R x v) →
      ∃ x0 v0, x0 ∈ l ∧ R x0 v0 ∧ ∀ x, x ∈ l → ∃ v, R x v ∧ v ≤ v0 := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _ hall
    obtain ⟨va, hva⟩ := hall a List.mem_cons_self
    by_cases hl : l = []
    · subst hl
      refine ⟨a, va, List.mem_cons_self, hva, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨va, hva, Int.le_refl _⟩
      · cases hx'
    · obtain ⟨x0, v0, hx0, hR0, hmax⟩ := ih hl (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      by_cases hle : va ≤ v0
      · refine ⟨x0, v0, List.mem_cons_of_mem _ hx0, hR0, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨va, hva, hle⟩
        · exact hmax x hx'
      · refine ⟨a, va, List.mem_cons_self, hva, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨va, hva, Int.le_refl _⟩
        · obtain ⟨v, hv, hvle⟩ := hmax x hx'
          exact ⟨v, hv, by omega⟩

/-- … and one has the smallest value. -/
theorem exists_min {α : Type} (R : α → Int → Prop) (l : List α) (hl : l ≠ [])
    (hall : ∀ x, x ∈ l → ∃ v, R x v) :
    ∃ x0 v0, x0 ∈ l ∧ R x0 v0 ∧ ∀ x, x ∈ l → ∃ v, R x v ∧ v0 ≤ v := by
  obtain ⟨x0, w0, hx0, hR0, hmax⟩ :=
    exists_max (fun x w => R x (-w)) l hl (fun x hx => by
      obtain ⟨v, hv⟩ := hall x hx
      exact ⟨-v, by simpa using hv⟩)
  refine ⟨x0, -w0, hx0, hR0, ?_⟩
  intro x hx
  obtain ⟨w, hw, hle⟩ := hmax x hx
  exact ⟨-w, hw, by omega⟩

/-- **Determinacy.**  Every position has a result under optimal play. -/
theorem exists_optimalResult (b : Board) (c : Color) : ∃ v, OptimalResult n b c v := by
  -- induction on twice the number of empty squares, plus one if the player to move must pass
  have key : ∀ (m : Nat) (b : Board) (c : Color),
      2 * emptyCount n b + (if moves n b c = [] then 1 else 0) ≤ m →
      ∃ v, OptimalResult n b c v := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro b c hm
      by_cases hmv : moves n b c = []
      · by_cases hop : moves n b c.opponent = []
        · -- the game is over
          refine ⟨margin n b .black, .over hmv hop (Int.le_refl _), .over hmv hop ?_⟩
          have := margin_opponent (n := n) b .black
          simp only [Color.opponent] at this
          omega
        · -- pass
          simp only [hmv, ↓reduceIte] at hm
          obtain ⟨v, hv⟩ := ih (2 * emptyCount n b) (by omega) b c.opponent (by simp [hop])
          exact ⟨v, .pass hmv hop hv.1, .pass hmv hop hv.2⟩
      · -- the player to move has moves; all of them lead to positions with a result
        simp only [hmv, ↓reduceIte] at hm
        have hchild : ∀ s, s ∈ moves n b c →
            ∃ v, OptimalResult n (play n b c s) c.opponent v := by
          intro s hs
          have hlt := emptyCount_play_lt (mem_moves.1 hs)
          apply ih (2 * emptyCount n (play n b c s) + 1) (by omega)
          split <;> omega
        cases c with
        | black =>
          obtain ⟨s0, v0, hs0, hR0, hmax⟩ := exists_max _ _ hmv hchild
          refine ⟨v0, .choose s0 rfl hs0 hR0.1, .reply (by decide) hmv ?_⟩
          intro s hs
          obtain ⟨v, hv, hle⟩ := hmax s hs
          exact hv.2.mono (by omega)
        | white =>
          obtain ⟨s0, v0, hs0, hR0, hmin⟩ := exists_min _ _ hmv hchild
          refine ⟨v0, .reply (by decide) hmv ?_, .choose s0 rfl hs0 hR0.2⟩
          intro s hs
          obtain ⟨v, hv, hle⟩ := hmin s hs
          exact hv.1.mono hle
  exact key _ b c (Nat.le_refl _)

/-- The result under optimal play exists and is unique. -/
theorem existsUnique_optimalResult (b : Board) (c : Color) :
    ∃ v, OptimalResult n b c v ∧ ∀ w, OptimalResult n b c w → w = v := by
  obtain ⟨v, hv⟩ := exists_optimalResult (n := n) b c
  exact ⟨v, hv, fun w hw => hw.unique hv⟩

end Othello
