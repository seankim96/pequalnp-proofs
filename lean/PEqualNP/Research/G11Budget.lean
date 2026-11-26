import PEqualNP.Research.G11Exchange
open PEqualNP.Research.G11Rare in
theorem PEqualNP.Research.G11Budget :
    let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ (U : Finset (Sym2 (Fin 11))) (b : Nat),
      (∃ K X : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
        G.IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ b) ↔
      (∃ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
        (if ({0,1,2} : Finset (Fin 11)) ⊆ K then 8 else 7) ≤ K.card + b) := by
  intro G U b
  have sevenBits : ∀ m : M, covers 0 m = true → 7#4 ≤ count m := by
    suffices h : ∀ a : Fin 32, ∀ b : Fin 64,
        let m := BitVec.ofNat 11 (64*a.val+b.val)
        covers 0 m = true → 7#4 ≤ count m by
      intro m
      have eq : BitVec.ofNat 11 (64*(m.toNat/64)+m.toNat%64) = m := by rw [Nat.div_add_mod]; simp
      rw [←eq]
      exact h ⟨_,by have := m.isLt; omega⟩ ⟨_,Nat.mod_lt _ (by decide)⟩
    intro a
    fin_cases a <;> as_aux_lemma => decide +kernel
  constructor
  · rintro ⟨K,X,best,full,bound⟩
    refine ⟨K,best,?_⟩
    obtain ⟨m,eq⟩ := represents (K ∪ X)
    have ok : covers 0 m = true := (corr 0 m).mp (eq.symm ▸ full)
    have total := Finset.card_union_le K X
    by_cases hc : ({0,1,2} : Finset (Fin 11)) ⊆ K
    · have raw (a : V) (ha : a ∈ ({0,1,2} : Finset V)) : m.getLsbD a.val = true := by
        have member : a ∈ vertices m := by rw [eq]; exact Finset.mem_union_left _ (hc ha)
        exact (Finset.mem_filter.mp member).2
      have low := fullBits m ok ((coreEq _).mpr ⟨raw 0 (by simp),raw 1 (by simp),raw 2 (by simp)⟩)
      change 8 ≤ (count m).toNat at low
      rw [count_eq,eq] at low
      rw [if_pos hc]
      omega
    · have low := sevenBits m ok
      change 7 ≤ (count m).toNat at low
      rw [count_eq,eq] at low
      rw [if_neg hc]
      omega
  · rintro ⟨K,best,budget⟩
    obtain ⟨J,T,jc,keep,jt,tc,cap⟩ := PEqualNP.Research.G11Exchange K
    have hj : (G.deleteEdges ↑U).IsVertexCover ↑J := by
      intro a b hab
      exact keep a b (SimpleGraph.deleteEdges_adj.mp hab).1 (best.1 hab)
    have eq := Nat.le_antisymm jc (best.2 _ hj)
    refine ⟨J,T \ J,⟨hj,fun W hw => jc.trans (best.2 W hw)⟩,?_,?_⟩
    · rw [Finset.union_sdiff_of_subset jt]; exact tc
    · rw [Finset.card_sdiff_of_subset jt,eq]
      exact Nat.sub_le_of_le_add (by rw [Nat.add_comm]; exact cap.trans budget)
