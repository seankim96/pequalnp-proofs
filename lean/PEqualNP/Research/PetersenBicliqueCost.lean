import PEqualNP.Defs

/-! Exact binary-gate cost for an OR of unshared biclique formulas on the
nine-vertex graph in L-meta-2159. A term is the AND of two nonempty
disjunctions of variables. Each term is built independently. -/
namespace PEqualNP.Research.PetersenBicliqueCost

abbrev V := Fin 9
abbrev Edge := V × V
abbrev Term := Finset V × Finset V

def edges : Finset Edge := {(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),
  (3,8),(5,7),(6,8),(5,8)}

def ordered (a b : V) : Edge := (min a b, max a b)

def support (t : Term) : Finset Edge :=
  (t.1 ×ˢ t.2).image fun p => ordered p.1 p.2

private theorem edge_count : edges.card = 12 := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem no_square : ∀ a b c d : V, a ≠ b → c ≠ d →
    ordered a c ∈ edges → ordered a d ∈ edges → ordered b c ∈ edges →
    ordered b d ∉ edges := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem cover_size : ∀ T : Finset V,
    (∀ e ∈ edges, e.1 ∈ T ∨ e.2 ∈ T) → 5 ≤ T.card := by decide +kernel

private theorem singleton_side (t : Term) (left : t.1.Nonempty) (right : t.2.Nonempty)
    (valid : support t ⊆ edges) : t.1.card = 1 ∨ t.2.card = 1 := by
  have mem (a b : V) (ha : a ∈ t.1) (hb : b ∈ t.2) : ordered a b ∈ edges :=
    valid (Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩)
  by_contra! h
  have hl := Finset.card_pos.mpr left
  have hr := Finset.card_pos.mpr right
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < t.1.card by omega)
  obtain ⟨c,hc,d,hd,hcd⟩ := Finset.one_lt_card.mp (show 1 < t.2.card by omega)
  exact no_square a b c d hab hcd (mem _ _ ha hc) (mem _ _ ha hd)
    (mem _ _ hb hc) (mem _ _ hb hd)

private theorem center (t : Term) (h : t.1.card = 1 ∨ t.2.card = 1) :
    ∃ v : V, ∀ e ∈ support t, e.1 = v ∨ e.2 = v := by
  rcases h with h|h
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
    refine ⟨v, ?_⟩
    intro e he
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp he
    have ha := (Finset.mem_product.mp hp).1
    have av : a = v := by simpa [hv] using ha
    subst a
    rcases le_total v b with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (max_eq_left h)
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
    refine ⟨v, ?_⟩
    intro e he
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp he
    have hb := (Finset.mem_product.mp hp).2
    have bv : b = v := by simpa [hv] using hb
    subst b
    rcases le_total a v with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (min_eq_right h)

/-- Two nonempty input trees with l and r leaves take l+r-1 gates including
their AND. Combining k terms with k-1 OR gates costs the total leaves minus one. -/
def gateCost {k : ℕ} (t : Fin k → Term) :=
  (∑ i, ((t i).1.card + (t i).2.card)) - 1

theorem lower {k : ℕ} (t : Fin k → Term)
    (sides : ∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty)
    (covers : Finset.univ.biUnion (fun i => support (t i)) = edges) : 16 ≤ gateCost t := by
  have one (i : Fin k) : (t i).1.card = 1 ∨ (t i).2.card = 1 := by
    apply singleton_side _ (sides i).1 (sides i).2
    intro e he
    rw [← covers]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,he⟩
  choose v hv using fun i => center (t i) (one i)
  have cover : ∀ e ∈ edges, e.1 ∈ Finset.univ.image v ∨ e.2 ∈ Finset.univ.image v := by
    intro e he
    rw [← covers] at he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    have vi : v i ∈ Finset.univ.image v := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rcases hv i e hi with h|h
    · exact Or.inl (h ▸ vi)
    · exact Or.inr (h ▸ vi)
  have hk : 5 ≤ k := by
    have h := (cover_size _ cover).trans (Finset.card_image_le (s := Finset.univ) (f := v))
    simpa using h
  have leaves (i : Fin k) : (support (t i)).card + 1 ≤ (t i).1.card + (t i).2.card := by
    have bound : (support (t i)).card ≤ (t i).1.card * (t i).2.card := by
      simpa [support,Finset.card_product] using
        (Finset.card_image_le (s := (t i).1 ×ˢ (t i).2) (f := fun p => ordered p.1 p.2))
    rcases one i with h|h <;> simp [h] at bound ⊢ <;> omega
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => leaves i)
  have count := Finset.card_biUnion_le (s := Finset.univ) (t := fun i => support (t i))
  rw [covers,edge_count] at count
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at total
  unfold gateCost
  rw [Finset.sum_add_distrib]
  omega

def exampleTerms : Fin 5 → Term :=
  ![({1},{0,2,6}), ({0},{4,5}), ({3},{2,4,8}), ({7},{2,5}), ({8},{5,6})]

theorem attained : (∀ i, (exampleTerms i).1.Nonempty ∧ (exampleTerms i).2.Nonempty) ∧
    Finset.univ.biUnion (fun i => support (exampleTerms i)) = edges ∧
    gateCost exampleTerms = 16 := by decide +kernel

def fires (t : Term) (X : Finset V) : Prop :=
  (∃ a ∈ t.1, a ∈ X) ∧ ∃ b ∈ t.2, b ∈ X

def edgeFunction (X : Finset V) : Prop :=
  ∃ e ∈ edges, e.1 ∈ X ∧ e.2 ∈ X

private theorem two_vertex_test : ∀ a b : V,
    edgeFunction {a,b} ↔ ordered a b ∈ edges := by
  unfold edgeFunction
  decide +kernel

private theorem diagonal : ∀ a : V, ordered a a ∉ edges := by decide +kernel

private theorem sorted_edges : ∀ e ∈ edges, ordered e.1 e.2 = e := by decide +kernel

/-- Semantic form. Agreement on just the singleton and two-vertex tests already
forces the cost bound, even when repeated terms or overlapping sides are allowed. -/
theorem lower_of_tests {k : ℕ} (t : Fin k → Term)
    (sides : ∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty)
    (correct : ∀ a b : V, (∃ i, fires (t i) {a,b}) ↔ edgeFunction {a,b}) :
    16 ≤ gateCost t := by
  have valid (i : Fin k) (a b : V) (ha : a ∈ (t i).1) (hb : b ∈ (t i).2) :
      ordered a b ∈ edges :=
    (two_vertex_test a b).mp ((correct a b).mp ⟨i, ⟨a,ha,by simp⟩, ⟨b,hb,by simp⟩⟩)
  apply lower t sides
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨a,b⟩,hm,rfl⟩ := Finset.mem_image.mp hi
    exact valid i a b (Finset.mem_product.mp hm).1 (Finset.mem_product.mp hm).2
  · intro e he
    have test : edgeFunction {e.1,e.2} := ⟨e,he,by simp,by simp⟩
    obtain ⟨i,⟨a,ha,ha'⟩,⟨b,hb,hb'⟩⟩ := (correct e.1 e.2).mpr test
    have ne : a ≠ b := by
      intro eq
      subst b
      exact diagonal a (valid i a a ha hb)
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha' hb'
    have orientation : (a=e.1 ∧ b=e.2) ∨ (a=e.2 ∧ b=e.1) := by grind
    have eq : ordered a b = e := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact sorted_edges _ he
      · simpa only [ordered,min_comm,max_comm] using sorted_edges _ he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,eq⟩⟩

end PEqualNP.Research.PetersenBicliqueCost
