import Init

/-- An OR and shared-guard schedule uses at most one more tagged root than OR gates. -/
theorem PEqualNP.Research.PlaneLinearGuardedOrSupport :
  ∀ (isOr : Nat → Bool) (dst left right : Nat → Nat) (gates : List Nat) (out : Nat),
    let step := fun (g : Bool) (s : Nat → Bool) (i w : Nat) =>
      if w = dst i then
        if isOr i then s (left i) || s (right i) else s (left i) && g
      else s w
    ∃ leaves : List (Nat × Bool), leaves.length ≤ gates.countP isOr + 1 ∧
      ∀ (g : Bool) (inputs : Nat → Bool),
        gates.foldl (step g) inputs out =
          leaves.any (fun t => inputs t.1 && (!t.2 || g)) := by
  intro isOr dst left right gates out step
  let live := fun (xs : List (Nat × Bool)) (g : Bool) (s : Nat → Bool) =>
    ∃ t ∈ xs, s t.1 = true ∧ (t.2 = false ∨ g = true)
  have consLive (t : Nat × Bool) (xs : List (Nat × Bool)) (g : Bool) (s : Nat → Bool) :
      live (t :: xs) g s ↔ (s t.1 = true ∧ (t.2 = false ∨ g = true)) ∨ live xs g s := by
    constructor
    · rintro ⟨u, hu, hv, ha⟩
      rcases List.mem_cons.mp hu with rfl | hm
      · exact Or.inl ⟨hv, ha⟩
      · exact Or.inr ⟨u, hm, hv, ha⟩
    · rintro (⟨hv, ha⟩ | ⟨u, hm, hv, ha⟩)
      · exact ⟨t, by simp, hv, ha⟩
      · exact ⟨u, List.mem_cons_of_mem t hm, hv, ha⟩
  have pull (xs : List (Nat × Bool)) (i : Nat) :
      ∃ ys : List (Nat × Bool), ys.length ≤ xs.length + (if isOr i then 1 else 0) ∧
        ∀ g s, live xs g (step g s i) ↔ live ys g s := by
    by_cases used : ∃ b, (dst i, b) ∈ xs
    · let old := xs.filter fun t => decide (t.1 ≠ dst i)
      let tag := decide ((dst i, false) ∉ xs)
      have shorter : old.length < xs.length := by
        obtain ⟨b, hb⟩ := used
        exact List.length_filter_lt_length_iff_exists.mpr ⟨(dst i, b), hb, by simp⟩
      have split (g : Bool) (s : Nat → Bool) :
          live xs g (step g s i) ↔ live old g s ∨
            ((if isOr i then s (left i) || s (right i) else s (left i) && g) = true ∧
             (tag = false ∨ g = true)) := by
        constructor
        · rintro ⟨⟨w, b⟩, hm, hv, ht⟩
          by_cases hw : w = dst i
          · subst w
            refine Or.inr ⟨by simpa [step] using hv, ?_⟩
            rcases ht with hb | hg
            · change b = false at hb
              subst b
              exact Or.inl (by simp [tag, hm])
            · exact Or.inr hg
          · exact Or.inl ⟨(w, b), List.mem_filter.mpr ⟨hm, by simpa using hw⟩,
                          by simpa [step, hw] using hv, ht⟩
        · rintro (⟨t, hm, hv, ht⟩ | ⟨hv, ht⟩)
          · obtain ⟨hin, hw⟩ := List.mem_filter.mp hm
            have hne : t.1 ≠ dst i := of_decide_eq_true hw
            exact ⟨t, hin, by simpa [step, hne] using hv, ht⟩
          · rcases ht with hraw | hg
            · have mem : (dst i, false) ∈ xs := by simpa [tag] using hraw
              exact ⟨(dst i, false), mem, by simpa [step] using hv, Or.inl rfl⟩
            · obtain ⟨b, mem⟩ := used
              exact ⟨(dst i, b), mem, by simpa [step] using hv, Or.inr hg⟩
      cases op : isOr i with
      | true =>
        refine ⟨(left i, tag) :: (right i, tag) :: old, ?_, ?_⟩
        · simp; omega
        · intro g s
          rw [split, consLive, consLive]
          simp only [op, ↓reduceIte, Bool.or_eq_true]
          grind
      | false =>
        refine ⟨(left i, true) :: old, ?_, ?_⟩
        · simp; omega
        · intro g s
          rw [split, consLive]
          simp only [op, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
          grind
    · refine ⟨xs, by omega, ?_⟩
      intro g s
      have same (t : Nat × Bool) (hm : t ∈ xs) : step g s i t.1 = s t.1 := by
        have ne : t.1 ≠ dst i := by
          intro he
          exact used ⟨t.2, by simpa [← he] using hm⟩
        simp [step, ne]
      constructor <;> rintro ⟨t, hm, hv, ht⟩ <;>
        exact ⟨t, hm, by simpa [same t hm] using hv, ht⟩
  have back (gs : List Nat) (xs : List (Nat × Bool)) :
      ∃ ys : List (Nat × Bool), ys.length ≤ xs.length + gs.countP isOr ∧
        ∀ g s, live xs g (gs.foldl (step g) s) ↔ live ys g s := by
    induction gs generalizing xs with
    | nil => exact ⟨xs, by simp, by simp⟩
    | cons i gs ih =>
      obtain ⟨mid, hm, em⟩ := ih xs
      obtain ⟨ys, hy, ey⟩ := pull mid i
      refine ⟨ys, ?_, fun g s => (em g (step g s i)).trans (ey g s)⟩
      cases op : isOr i <;> simp [op] at hy ⊢ <;> omega
  obtain ⟨ys, hy, ey⟩ := back gates [(out, false)]
  refine ⟨ys, by simpa [Nat.add_comm] using hy, ?_⟩
  intro g s
  apply Bool.eq_iff_iff.mpr
  simpa [live, List.any_eq_true] using ey g s
