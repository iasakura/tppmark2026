import Othello.Lemmas

/-!
# Symmetries of the board

Reflecting the board does not change the game: if a player can secure a
margin on a board, the same player can secure it on the reflected board
(`secures_sym_iff`).  This is used for 8 × 8 Othello, where a table of
positions is given up to the eight symmetries of the square.
-/

namespace Othello

variable {n : Nat}

/-- A symmetry of the `n × n` board: an involution `f` of the squares which
maps the board to itself, together with its action `g` on directions. -/
structure BoardSym (n : Nat) where
  f : Square → Square
  g : Int × Int → Int × Int
  f_invol : ∀ s, f (f s) = s
  g_invol : ∀ d, g (g d) = d
  onBoard : ∀ s, OnBoard n (f s) ↔ OnBoard n s
  step_eq : ∀ d s, f (step d s) = step (g d) (f s)
  g_mem : ∀ d, d ∈ directions → g d ∈ directions
  perm : ((squares n).map f).Perm (squares n)

/-- The board `b` seen through the symmetry `σ`. -/
def BoardSym.app (σ : BoardSym n) (b : Board) : Board := fun s => b (σ.f s)

namespace BoardSym

variable (σ : BoardSym n)

theorem f_inj {s t : Square} (h : σ.f s = σ.f t) : s = t := by
  have := congrArg σ.f h
  rwa [σ.f_invol, σ.f_invol] at this

theorem app_app (b : Board) : σ.app (σ.app b) = b := by
  funext s
  simp [app, σ.f_invol]

theorem cell_app (b : Board) (s : Square) : cell n (σ.app b) s = cell n b (σ.f s) := by
  unfold cell app
  by_cases h : OnBoard n s
  · simp [h, (σ.onBoard s).2 h]
  · have h' : ¬ OnBoard n (σ.f s) := fun h' => h ((σ.onBoard s).1 h')
    simp [h, h']

theorem run_app (b : Board) (c : Color) (d : Int × Int) :
    ∀ (k : Nat) (s : Square) (acc : List Square),
      run n (σ.app b) c d k s acc = (run n b c (σ.g d) k (σ.f s) (acc.map σ.f)).map σ.f := by
  intro k
  induction k with
  | zero => intro s acc; simp [run]
  | succ k ih =>
    intro s acc
    simp only [run, σ.cell_app]
    cases hc : cell n b (σ.f s) with
    | none => simp
    | some c' =>
      by_cases hcc : c' = c
      · simp only [hcc, ↓reduceIte, List.map_map]
        rw [List.map_id'' (fun x => by simp [σ.f_invol])]
      · simp only [hcc, ↓reduceIte]
        rw [ih, σ.step_eq, List.map_cons]

theorem flipsDir_app (b : Board) (c : Color) (s : Square) (d : Int × Int) :
    flipsDir n (σ.app b) c s d = (flipsDir n b c (σ.f s) (σ.g d)).map σ.f := by
  unfold flipsDir
  rw [σ.run_app, σ.step_eq]
  simp

theorem mem_flips_app (b : Board) (c : Color) (s q : Square) :
    q ∈ flips n (σ.app b) c s ↔ σ.f q ∈ flips n b c (σ.f s) := by
  unfold flips
  simp only [List.mem_flatMap, σ.flipsDir_app, List.mem_map]
  constructor
  · rintro ⟨d, hd, q', hq', rfl⟩
    rw [σ.f_invol]
    exact ⟨σ.g d, σ.g_mem d hd, hq'⟩
  · rintro ⟨d, hd, hq⟩
    refine ⟨σ.g d, σ.g_mem d hd, σ.f q, ?_, σ.f_invol q⟩
    rw [σ.g_invol]
    exact hq

theorem legal_app (b : Board) (c : Color) (s : Square) :
    Legal n (σ.app b) c s ↔ Legal n b c (σ.f s) := by
  have hne : flips n (σ.app b) c s ≠ [] ↔ flips n b c (σ.f s) ≠ [] := by
    constructor
    · intro h
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
      exact List.ne_nil_of_mem ((σ.mem_flips_app b c s q).1 hq)
    · intro h
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
      apply List.ne_nil_of_mem (a := σ.f q)
      rw [σ.mem_flips_app, σ.f_invol]
      exact hq
  unfold Legal
  rw [hne, ← σ.onBoard s]
  rfl

theorem mem_moves_app (b : Board) (c : Color) (s : Square) :
    s ∈ moves n (σ.app b) c ↔ σ.f s ∈ moves n b c := by
  rw [mem_moves, mem_moves, σ.legal_app]

theorem moves_app_eq_nil (b : Board) (c : Color) :
    moves n (σ.app b) c = [] ↔ moves n b c = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h s hs
    apply h (σ.f s)
    rw [σ.mem_moves_app, σ.f_invol]
    exact hs
  · intro h s hs
    exact h (σ.f s) ((σ.mem_moves_app b c s).1 hs)

theorem play_app (b : Board) (c : Color) (s : Square) :
    play n (σ.app b) c s = σ.app (play n b c (σ.f s)) := by
  funext q
  unfold play app
  have h1 : (q = s) ↔ (σ.f q = σ.f s) := ⟨fun h => by rw [h], fun h => σ.f_inj h⟩
  have h2 := σ.mem_flips_app b c s q
  by_cases hc : q = s ∨ q ∈ flips n (fun s => b (σ.f s)) c s
  · have hc' : σ.f q = σ.f s ∨ σ.f q ∈ flips n b c (σ.f s) := by
      rcases hc with h | h
      · exact Or.inl (h1.1 h)
      · exact Or.inr (h2.1 h)
    simp [hc, hc']
  · have hc' : ¬ (σ.f q = σ.f s ∨ σ.f q ∈ flips n b c (σ.f s)) := by
      rintro (h | h)
      · exact hc (Or.inl (h1.2 h))
      · exact hc (Or.inr (h2.2 h))
    simp [hc, hc']

theorem count_app (b : Board) (c : Color) : count n (σ.app b) c = count n b c := by
  unfold count app
  have h1 : ((squares n).filter fun s => b (σ.f s) = some c).length
      = (((squares n).map σ.f).filter fun s => b s = some c).length := by
    rw [List.filter_map, List.length_map]
    rfl
  rw [h1]
  exact (σ.perm.filter _).length_eq

theorem margin_app (b : Board) (c : Color) : margin n (σ.app b) c = margin n b c := by
  unfold margin
  rw [σ.count_app, σ.count_app]

end BoardSym

/-- A strategy on a board gives a strategy on the reflected board. -/
theorem Secures.sym (σ : BoardSym n) {p : Color} {v : Int} {b : Board} {c : Color}
    (h : Secures n p v b c) : Secures n p v (σ.app b) c := by
  induction h with
  | over hm ho hv =>
    exact .over ((σ.moves_app_eq_nil _ _).2 hm) ((σ.moves_app_eq_nil _ _).2 ho)
      (by rw [σ.margin_app]; exact hv)
  | pass hm ho _ ih =>
    exact .pass ((σ.moves_app_eq_nil _ _).2 hm)
      (fun h => ho ((σ.moves_app_eq_nil _ _).1 h)) ih
  | choose s hc hs _ ih =>
    refine .choose (σ.f s) hc ?_ ?_
    · rw [σ.mem_moves_app, σ.f_invol]; exact hs
    · rw [σ.play_app, σ.f_invol]; exact ih
  | reply hc hm _ ih =>
    refine .reply hc (fun h => hm ((σ.moves_app_eq_nil _ _).1 h)) ?_
    intro s hs
    rw [σ.play_app]
    exact ih (σ.f s) ((σ.mem_moves_app _ _ s).1 hs)

/-- The game is invariant under the symmetries of the board. -/
theorem secures_sym_iff (σ : BoardSym n) {p : Color} {v : Int} {b : Board} {c : Color} :
    Secures n p v (σ.app b) c ↔ Secures n p v b c := by
  constructor
  · intro h
    have := h.sym σ
    rwa [σ.app_app] at this
  · exact Secures.sym σ

/-! ## The reflections -/

/-- Exchanging columns and rows: `(x, y) ↦ (y, x)`. -/
def transposeSym (n : Nat) (h : ((squares n).map fun s : Square => (s.2, s.1)).Perm (squares n)) :
    BoardSym n where
  f := fun s => (s.2, s.1)
  g := fun d => (d.2, d.1)
  f_invol := fun s => rfl
  g_invol := fun d => rfl
  onBoard := fun s => by unfold OnBoard; simp only; omega
  step_eq := fun d s => rfl
  g_mem := fun d hd => by
    simp only [directions, List.mem_cons, List.mem_nil_iff, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  perm := h

/-- Reversing the columns: `(x, y) ↦ (n - 1 - x, y)`. -/
def flipXSym (n : Nat)
    (h : ((squares n).map fun s : Square => ((n : Int) - 1 - s.1, s.2)).Perm (squares n)) :
    BoardSym n where
  f := fun s => ((n : Int) - 1 - s.1, s.2)
  g := fun d => (-d.1, d.2)
  f_invol := fun s => by apply Prod.ext <;> simp only <;> omega
  g_invol := fun d => by apply Prod.ext <;> simp only <;> omega
  onBoard := fun s => by unfold OnBoard; simp only; omega
  step_eq := fun d s => by unfold step; apply Prod.ext <;> simp only <;> omega
  g_mem := fun d hd => by
    simp only [directions, List.mem_cons, List.mem_nil_iff, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  perm := h

/-- Reversing the rows: `(x, y) ↦ (x, n - 1 - y)`. -/
def flipYSym (n : Nat)
    (h : ((squares n).map fun s : Square => (s.1, (n : Int) - 1 - s.2)).Perm (squares n)) :
    BoardSym n where
  f := fun s => (s.1, (n : Int) - 1 - s.2)
  g := fun d => (d.1, -d.2)
  f_invol := fun s => by apply Prod.ext <;> simp only <;> omega
  g_invol := fun d => by apply Prod.ext <;> simp only <;> omega
  onBoard := fun s => by unfold OnBoard; simp only; omega
  step_eq := fun d s => by unfold step; apply Prod.ext <;> simp only <;> omega
  g_mem := fun d hd => by
    simp only [directions, List.mem_cons, List.mem_nil_iff, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  perm := h

end Othello
