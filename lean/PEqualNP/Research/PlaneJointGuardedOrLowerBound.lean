import Init

/-- Jointly observing several outputs costs one OR for each essential root beyond their count. -/
theorem PEqualNP.Research.PlaneJointGuardedOrLowerBound :
∀ (isOr : Nat → Bool) (dst left right : Nat → Nat) (gates outs essential : List Nat),
    let step := fun (g : Bool) (s : Nat → Bool) (i w : Nat) =>
      if w = dst i then
        if isOr i then s (left i) || s (right i) else s (left i) && g
      else s w
    essential.Nodup →
    (∀ w ∈ essential, ∃ (g : Bool) (s t : Nat → Bool) (v : Nat), v ∈ outs ∧
      (∀ j, j ≠ w → s j = t j) ∧
      gates.foldl (step g) s v ≠ gates.foldl (step g) t v) →
    essential.length ≤ gates.countP isOr + outs.length := by
  intro isOr dst left right gates outs essential step nodup sensitive
  let agree := fun (xs : List Nat) (s t : Nat → Bool) => ∀ w ∈ xs, s w = t w
  have pull (xs : List Nat) (i : Nat) :
      ∃ ys : List Nat, ys.length ≤ xs.length + (if isOr i then 1 else 0) ∧
        ∀ g s t, agree ys s t → agree xs (step g s i) (step g t i) := by
    by_cases used : dst i ∈ xs
    · let rest := xs.filter fun w => decide (w ≠ dst i)
      have shorter : rest.length < xs.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨dst i, used, by simp⟩
      cases op : isOr i with
      | true =>
        refine ⟨left i :: right i :: rest, ?_, ?_⟩
        · simp; omega
        · intro g s t h w hw
          by_cases eq : w = dst i
          · simp [step, eq, op, h (left i) (by simp), h (right i) (by simp)]
          · have mem : w ∈ rest := List.mem_filter.mpr ⟨hw, by simpa using eq⟩
            simpa [step, eq] using h w (by simp [mem])
      | false =>
        refine ⟨left i :: rest, ?_, ?_⟩
        · simp; omega
        · intro g s t h w hw
          by_cases eq : w = dst i
          · simp [step, eq, op, h (left i) (by simp)]
          · have mem : w ∈ rest := List.mem_filter.mpr ⟨hw, by simpa using eq⟩
            simpa [step, eq] using h w (by simp [mem])
    · refine ⟨xs, by omega, ?_⟩
      intro g s t h w hw
      have ne : w ≠ dst i := fun e => used (e ▸ hw)
      simpa [step, ne] using h w hw
  have trace (gs xs : List Nat) :
      ∃ ys : List Nat, ys.length ≤ xs.length + gs.countP isOr ∧
        ∀ g s t, agree ys s t → agree xs (gs.foldl (step g) s) (gs.foldl (step g) t) := by
    induction gs generalizing xs with
    | nil => exact ⟨xs, by simp, by simp⟩
    | cons i gs ih =>
      obtain ⟨mid, hm, em⟩ := ih xs
      obtain ⟨ys, hy, ey⟩ := pull mid i
      refine ⟨ys, ?_, fun g s t h => em g _ _ (ey g s t h)⟩
      cases op : isOr i <;> simp [op] at hy ⊢ <;> omega
  obtain ⟨roots, bound, same⟩ := trace gates outs
  have sub : essential ⊆ roots := by
    intro w hw
    apply Classical.byContradiction
    intro missing
    obtain ⟨g, s, t, v, hv, off, diff⟩ := sensitive w hw
    exact diff (same g s t (fun j hj => off j (fun eq => missing (eq ▸ hj))) v hv)
  have := nodup.length_le_of_subset sub
  omega
