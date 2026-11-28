import Init

/-- Least signed preload supplying a family of columns, where each column may
be read directly or through a shared guard. Mask choices are per column. -/
theorem PEqualNP.Research.PlaneLeastGuardPreload :
  ∀ (R I : Type) (pos guard : R → Prop) (v : I → R → Prop),
    let le := fun (a b : R → Prop) =>
      ∀ r, (pos r → a r → b r) ∧ (¬ pos r → b r → a r)
    let safe := fun i => ∀ r, pos r → v i r → guard r
    let supplies := fun (c : R → Prop) (m : I → Prop) =>
      ∀ i, le (v i) (fun r => c r ∧ (m i → guard r))
    let least := fun r => (pos r ∧ ∃ i, v i r) ∨
      (¬ pos r ∧ ∀ i, (safe i → guard r) → v i r)
    supplies least safe ∧
    (∀ c m, supplies c m → le least c) ∧
    ∀ (feasible : (R → Prop) → Prop),
      (∀ a b, le a b → feasible a → feasible b) →
      ((∃ c m, supplies c m ∧ ¬ feasible c) ↔ ¬ feasible least) := by
  intro R I pos guard v le safe supplies least
  have covers : supplies least safe := by
    intro i r
    constructor
    · intro hp hv
      exact ⟨Or.inl ⟨hp, i, hv⟩, fun hs => hs r hp hv⟩
    · rintro hn ⟨hl, active⟩
      rcases hl with ⟨hp, _⟩ | ⟨_, all⟩
      · exact (hn hp).elim
      · exact all i active
  have minimal : ∀ c m, supplies c m → le least c := by
    intro c m cover
    have valid : ∀ i, m i → safe i := by
      intro i hm r hp hv
      exact ((cover i r).1 hp hv).2 hm
    intro r
    constructor
    · intro hp hl
      rcases hl with ⟨_, i, hv⟩ | ⟨hn, _⟩
      · exact ((cover i r).1 hp hv).1
      · exact (hn hp).elim
    · intro hn hc
      refine Or.inr ⟨hn, ?_⟩
      intro i active
      exact (cover i r).2 hn ⟨hc, fun hm => active (valid i hm)⟩
  refine ⟨covers, minimal, ?_⟩
  intro feasible mono
  constructor
  · rintro ⟨c, m, supply, no⟩ h
    exact no (mono least c (minimal c m supply) h)
  · intro no
    exact ⟨least, safe, covers, no⟩
