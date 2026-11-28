import Init

/-- Filtering a predecessor-closed set of gate labels preserves its truth values. -/
theorem PEqualNP.Research.PlaneClosedGateProjection :
  ∀ (keep : Nat → Bool) (left right : Nat → Nat) (gate : Nat → Bool → Bool → Bool)
    (order : List Nat),
    (∀ i ∈ order, keep i = true → keep (left i) = true ∧ keep (right i) = true) →
    let step := fun (s : Nat → Bool) (i : Nat) (j : Nat) =>
      if j = i then gate i (s (left i)) (s (right i)) else s j
    ∀ s t : Nat → Bool, (∀ j, keep j = true → s j = t j) →
      ∀ j, keep j = true →
        order.foldl step s j = (order.filter keep).foldl step t j := by
  intro keep left right gate order
  induction order with
  | nil =>
    intro _ step s t agree j hj
    exact agree j hj
  | cons i rest ih =>
    intro closed step s t agree j hj
    have tailClosed : ∀ n ∈ rest, keep n = true →
        keep (left n) = true ∧ keep (right n) = true := by
      intro n hn
      exact closed n (List.mem_cons_of_mem _ hn)
    cases hi : keep i with
    | false =>
      simp only [List.foldl_cons, List.filter_cons, hi, Bool.false_eq_true, ite_false]
      apply ih tailClosed (step s i) t _ j hj
      intro n hn
      have hne : n ≠ i := by
        intro e
        subst n
        simp [hi] at hn
      simpa [step,hne] using agree n hn
    | true =>
      simp only [List.foldl_cons, List.filter_cons, hi, ite_true]
      apply ih tailClosed (step s i) (step t i) _ j hj
      intro n hn
      by_cases e : n = i
      · obtain ⟨hl,hr⟩ := closed i (by simp) hi
        simp [step,e,agree _ hl,agree _ hr]
      · simpa [step,e] using agree n hn
