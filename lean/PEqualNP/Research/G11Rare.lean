import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.EdgeOwnership
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace PEqualNP.Research.G11Rare
abbrev V := Fin 11
abbrev M := BitVec 11
def vertices (m : M) := Finset.univ.filter fun v : V => m.getLsbD v.val
theorem represents (K : Finset V) : ∃ m, vertices m = K := by
  induction K using Finset.induction_on with
  | empty => exact ⟨0, by ext v; simp [vertices]⟩
  | @insert a K ha ih =>
    obtain ⟨m,rfl⟩ := ih
    refine ⟨m ||| BitVec.ofNat 11 (2^a.val), ?_⟩
    ext v
    simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, decide_eq_true v.isLt, Bool.true_and, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert, Fin.ext_iff]
    grind
def edges : List (V × V) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
def covers (u : Nat) (m : M) : Bool := (edges.zipIdx).all fun (e,i) =>
  u.testBit i || m.getLsbD e.1.val || m.getLsbD e.2.val
def rare : Array (Nat × Nat × Nat × Nat) := #[(36608, 5, 199, 503), (44800, 5, 143, 1455), (44864, 4, 135, 503), (44992, 4, 135, 503), (48960, 4, 135, 503), (52992, 5, 79, 639), (53120, 4, 71, 503), (53184, 4, 71, 503), (57216, 4, 71, 503), (61184, 5, 79, 639), (61248, 4, 135, 503), (61312, 4, 71, 503), (61376, 4, 71, 503), (65280, 4, 15, 639), (65344, 4, 15, 639), (65408, 4, 15, 639), (65472, 3, 7, 503)]
def row (i : Fin 17) := rare[i.val]!
def u (i : Fin 17) := (row i).1
def n (i : Fin 17) := (row i).2.1
def k (i : Fin 17) : M := BitVec.ofNat 11 (row i).2.2.1
def t (i : Fin 17) : M := BitVec.ofNat 11 (row i).2.2.2
theorem witnesses : ∀ i : Fin 17, covers (u i) (k i) = true ∧ covers 0 (t i) = true ∧
    vertices (k i) ⊆ vertices (t i) ∧ (vertices (k i)).card = n i ∧ (vertices (t i)).card = 8 := by decide +kernel
def count (m : M) : BitVec 4 := (if m.getLsbD 0 then 1 else 0) + (if m.getLsbD 1 then 1 else 0) + (if m.getLsbD 2 then 1 else 0) + (if m.getLsbD 3 then 1 else 0) + (if m.getLsbD 4 then 1 else 0) + (if m.getLsbD 5 then 1 else 0) + (if m.getLsbD 6 then 1 else 0) + (if m.getLsbD 7 then 1 else 0) + (if m.getLsbD 8 then 1 else 0) + (if m.getLsbD 9 then 1 else 0) + (if m.getLsbD 10 then 1 else 0)
theorem count_eq : ∀ m : M, (count m).toNat = (vertices m).card := by
  intro m
  suffices h : ∀ a : Fin 32, ∀ b : Fin 64, (count (BitVec.ofNat 11 (64*a.val+b.val))).toNat = (vertices (BitVec.ofNat 11 (64*a.val+b.val))).card by
    have eq : BitVec.ofNat 11 (64 * (m.toNat / 64) + m.toNat % 64) = m := by rw [Nat.div_add_mod]; simp
    rw [←eq]
    exact h ⟨_, by have := m.isLt; omega⟩ ⟨_,Nat.mod_lt _ (by decide)⟩
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
private theorem allMasks (P : M → Prop) (h : ∀ a : Fin 32, ∀ b : Fin 64, P (BitVec.ofNat 11 (64*a.val+b.val))) (m : M) : P m := by
  have eq : BitVec.ofNat 11 (64 * (m.toNat/64) + m.toNat%64) = m := by rw [Nat.div_add_mod]; simp
  rw [←eq]
  exact h ⟨_,by have := m.isLt; omega⟩ ⟨_,Nat.mod_lt _ (by decide)⟩

theorem coreEq (m : M) : (7 : M) &&& m = 7 ↔ m.getLsbD 0 = true ∧ m.getLsbD 1 = true ∧ m.getLsbD 2 = true := by
  apply allMasks _ _ m
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel

theorem minBits (i : Fin 17) (m : M) : covers (u i) m = true →
    BitVec.ofNat 4 (n i) ≤ count m ∧ (count m = BitVec.ofNat 4 (n i) → (7 : M) &&& m = 7) := by
  suffices all : ∀ m : M, ∀ i : Fin 17, covers (u i) m = true →
      BitVec.ofNat 4 (n i) ≤ count m ∧ (count m = BitVec.ofNat 4 (n i) → (7 : M) &&& m = 7) from all m i
  intro x
  apply allMasks _ _ x
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel

theorem fullBits (m : M) : covers 0 m = true → (7 : M) &&& m = 7 → 8#4 ≤ count m := by
  apply allMasks _ _ m
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
def live (u : Nat) := ((edges.zipIdx).filter (fun p => !u.testBit p.2)).map Prod.fst
def graph (u : Nat) := PEqualNP.EdgeOwnership.edgeGraph 11 ((live u).map (fun e => (e.1.val,e.2.val)))
theorem corr (u : Nat) (m : M) : (graph u).IsVertexCover (vertices m : Set V) ↔ covers u m = true := by
  have equiv : covers u m = true ↔ ∀ e ∈ live u, e.1 ∈ vertices m ∨ e.2 ∈ vertices m := by
    simp only [covers,List.all_eq_true,Bool.or_eq_true,live,List.mem_map,List.mem_filter]
    constructor
    · intro h e he
      obtain ⟨p,⟨hp,off⟩,rfl⟩ := he
      have hh := h p hp
      simp only [Bool.not_eq_true'] at off
      simpa [vertices,off] using hh
    · intro h p hp
      cases off : u.testBit p.2 with
      | true => simp
      | false =>
        have he := h p.1 ⟨p,⟨hp,by simp [off]⟩,rfl⟩
        simpa [vertices,off] using he
  rw [equiv]
  constructor
  · intro hc e he
    have ne : e.1 ≠ e.2 := by
      have distinct : ∀ p ∈ edges.zipIdx, p.1.1 ≠ p.1.2 := by decide +kernel
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact distinct p (List.mem_filter.mp hp).1
    exact hc (show (graph u).Adj e.1 e.2 from ⟨ne, Or.inl (List.mem_map.mpr ⟨e,he,rfl⟩)⟩)
  · intro hc a b hab
    rcases hab.2 with pos | neg
    · obtain ⟨⟨x,y⟩,hm,eq⟩ := List.mem_map.mp pos
      obtain ⟨rfl,rfl⟩ : x = a ∧ y = b := ⟨Fin.ext (Prod.mk.inj eq).1,Fin.ext (Prod.mk.inj eq).2⟩
      exact hc _ hm
    · obtain ⟨⟨x,y⟩,hm,eq⟩ := List.mem_map.mp neg
      obtain ⟨rfl,rfl⟩ : x = b ∧ y = a := ⟨Fin.ext (Prod.mk.inj eq).1,Fin.ext (Prod.mk.inj eq).2⟩
      exact (hc _ hm).symm

open PEqualNP.MetaComplexity.NestedCover in
theorem exactCost (i : Fin 17) (b : Nat) :
    (∃ K X : Finset V, IsMinCover (graph (u i)) K ∧ (graph 0).IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ b) ↔ 8 - n i ≤ b := by
  have small : ∀ i : Fin 17, n i < 16 := by decide +kernel
  have mincard (m : M) (h : covers (u i) m = true) : n i ≤ (vertices m).card := by
    have ht := (minBits i m h).1
    change (BitVec.ofNat 4 (n i)).toNat ≤ (count m).toNat at ht
    simpa [count_eq, Nat.mod_eq_of_lt (small i)] using ht
  obtain ⟨hk,ht,sub,ks,ts⟩ := witnesses i
  have best : IsMinCover (graph (u i)) (vertices (k i)) := by
    refine ⟨(corr _ _).mpr hk,?_⟩
    intro T h
    obtain ⟨m,rfl⟩ := represents T
    exact ks.trans_le (mincard m ((corr _ _).mp h))
  constructor
  · rintro ⟨K,X,hm,ok,bd⟩
    obtain ⟨m,rfl⟩ := represents K
    have eq := Nat.le_antisymm (hm.2 _ best.1) (best.2 _ hm.1)
    have card := eq.trans ks
    have bits : count m = BitVec.ofNat 4 (n i) := by
      apply BitVec.eq_of_toNat_eq
      simp [count_eq,card,Nat.mod_eq_of_lt (small i)]
    have core := (minBits i m ((corr _ _).mp hm.1)).2 bits
    obtain ⟨q,hq⟩ := represents (vertices m ∪ X)
    have incl (j : Nat) (hj : j < 11) (on : m.getLsbD j = true) : q.getLsbD j = true := by
      have hh : (⟨j,hj⟩ : V) ∈ vertices q := by rw [hq]; exact Finset.mem_union_left _ (by simpa only [vertices,Finset.mem_filter,Finset.mem_univ,true_and] using on)
      simpa only [vertices,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    have qcore : (7 : M) &&& q = 7 := by
      obtain ⟨a,b,c⟩ := (coreEq m).mp core
      exact (coreEq q).mpr ⟨incl 0 (by decide) a,incl 1 (by decide) b,incl 2 (by decide) c⟩
    rw [←hq] at ok
    have lower := fullBits q ((corr _ _).mp ok) qcore
    change 8 ≤ (count q).toNat at lower
    rw [count_eq,hq] at lower
    have ub := Finset.card_union_le (vertices m) X
    omega
  · intro budget
    refine ⟨vertices (k i), vertices (t i) \ vertices (k i),best,?_,?_⟩
    · rw [Finset.union_sdiff_of_subset sub]
      exact (corr _ _).mpr ht
    · simpa [Finset.card_sdiff_of_subset sub,ks,ts] using budget
end PEqualNP.Research.G11Rare

open PEqualNP.Research.G11Rare PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Research.G11Rare : ∀ (i : Fin 17) (b : Nat), (∃ K X : Finset V, IsMinCover (graph (u i)) K ∧ (graph 0).IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ b) ↔ 8 - n i ≤ b := exactCost
