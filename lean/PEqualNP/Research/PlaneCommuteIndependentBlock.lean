import Init

/-- Move a gate across independent writes while preserving the whole suffix state. -/
theorem PEqualNP.Research.PlaneCommuteIndependentBlock :
  ∀ (left right : Nat → Nat) (gate : Nat → Bool → Bool → Bool)
    (j : Nat) (block suffix : List Nat),
    (∀ i ∈ block, i ≠ j ∧ left i ≠ j ∧ right i ≠ j ∧ left j ≠ i ∧ right j ≠ i) →
    let step := fun (s : Nat → Bool) (i : Nat) (w : Nat) =>
      if w = i then gate i (s (left i)) (s (right i)) else s w
    ∀ s : Nat → Bool,
      (block ++ j :: suffix).foldl step s = (j :: (block ++ suffix)).foldl step s := by
  intro left right gate j block suffix
  induction block with
  | nil => intro _ step s; rfl
  | cons i rest ih =>
    intro independent step s
    obtain ⟨hij, hli, hri, hlj, hrj⟩ := independent i (by simp)
    have tailOk : ∀ n ∈ rest, n ≠ j ∧ left n ≠ j ∧ right n ≠ j ∧ left j ≠ n ∧ right j ≠ n := by
      intro n hn
      exact independent n (List.mem_cons_of_mem _ hn)
    have swap : step (step s i) j = step (step s j) i := by
      funext w
      by_cases wi : w = i
      · subst w
        simp [step,hij,hli,hri]
      · by_cases wj : w = j
        · subst w
          simp [step,wi,hlj,hrj]
        · simp [step,wi,wj]
    change (rest ++ j :: suffix).foldl step (step s i) =
      (rest ++ suffix).foldl step (step (step s j) i)
    exact (ih tailOk (step s i)).trans (congrArg ((rest ++ suffix).foldl step) swap)
