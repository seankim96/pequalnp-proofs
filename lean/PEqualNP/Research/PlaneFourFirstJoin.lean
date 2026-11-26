import PEqualNP.Research.PlaneFourCoverCount

namespace PEqualNP.Research.PlaneFourFirstJoin
open PlaneFourCoverCount
abbrev T := Fin 7
def z (t : T) (v : V) : Bool := (#[0x35e7ffffe7a, 0x2f3ffdff3d7, 0x39ffebf9ebf, 0xfff5fcf5ff, 0x3ffaf27afff, 0x3fd79fd7ff9, 0x3ebcfebffcf] : Array Nat)[t.val]!.testBit v.val
private def word (t : T) (i : Fin 34) := ((#[0x1487c04c5d0a497228e1c8b681c282068b493e0d61a80ab6d68ac6d77ac552c9ad24a183da70ccf91c1e23204e851, 0x4a8e814e7d4e51f33903ccf709d38426cf51bf1d83ac4b07c07e055b834662ebb15aa994dc9111019d2e45248f0bd, 0x8b16922698525a744925d13791e48647135a402da5b08b8e81802583504004cdb59b31a5deb154621e3e6728cf93e, 0xcb9ea328b895bae056a7d57819f588675762c13dc7b4cc16928245c758c114e1f0228296e0d1986a9f4e892d101bf, 0x10c26b42ad8d9c36166c985b8a2068a879b6b424de9b90c9ea384660b61422263a0630950d41000e30b5c0add46240, 0x14caec52c1c82387008ab8835a8c07ea7c3e0515e0bbd4d26b486864f69c33285a4a39161d63044e81a6c2ce186ac1, 0x18d36d62e3cc640f118cd8c7630d180c2c740bd6e2dc18daec588a693724442a7a8e41972d85088f09b0e011c0e342] : Array Nat)[t.val]! >>> (11*i.val)) &&& 2047
def f (t : T) (i : Fin 34) : Pair := (Fin.ofNat 42 (word t i / 42),Fin.ofNat 42 (word t i % 42))
private def owner (t : T) (v : V) := ((#[0x86001f01e75c6c001a6585d65544d24503ce34c2ca2481c61400040c2040000, 0x7c079d71b00069961759551349186000d30b2892071850001030810000103ce, 0x75c6c001a6585d65544d24618007c078a2481c61400040c204000040f38d30b, 0x69961759551349186001f01e75c6c71850001030810000103ce34c2ca248, 0x6585d65544d24618007c079d71b0006800040c204000040f38d30b289207185, 0x59551349186001f01e75c6c001a6585c30810000103ce34c2ca2481c6140004, 0x4d24618007c079d71b00069961759550000040f38d30b289207185000103081] : Array Nat)[t.val]! >>> (6*v.val)) &&& 63
private theorem owners : ∀ (t : T) (i : Fin 34),
    (z t (f t i).1 = true → owner t (f t i).1 = i.val) ∧
    (z t (f t i).2 = true → owner t (f t i).2 = i.val) := by decide +kernel
theorem uniq (t : T) (v : V) (hv : z t v = true) (i j : Fin 34)
    (a : (f t i).1 = v ∨ (f t i).2 = v) (b : (f t j).1 = v ∨ (f t j).2 = v) : i = j := by
  have key (k : Fin 34) (h : (f t k).1 = v ∨ (f t k).2 = v) : owner t v = k.val := by
    rcases h with e | e
    · rw [← e] at hv ⊢
      exact (owners t k).1 hv
    · rw [← e] at hv ⊢
      exact (owners t k).2 hv
  exact Fin.ext ((key i a).symm.trans (key j b))
theorem occurs : ∀ (t : T) (i : Fin 34), incident (f t i) := by decide +kernel
theorem omits : ∀ v : V, ∃ t : T, z t v = false := by decide +kernel
set_option maxHeartbeats 0 in
private theorem coverRows (t : T) (a : V) : ∀ b : V, incident (a,b) → z t a = true ∨ z t b = true := by
  fin_cases t <;> fin_cases a <;> as_aux_lemma => decide +kernel
private theorem covers (t : T) (e : Pair) : incident e → z t e.1 = true ∨ z t e.2 = true := coverRows t e.1 e.2

set_option maxHeartbeats 0 in
private theorem avoids (e : Pair) : incident e → ∃ t : T, ∀ i : Fin 34, f t i ≠ e := by
  suffices h : ∀ x y : V, incident (x,y) → ∃ t : T, ∀ i : Fin 34, f t i ≠ (x,y) from h e.1 e.2
  intro x
  fin_cases x <;> as_aux_lemma => decide +kernel

def Z (t : T) : Set V := {v | z t v = true}
def E : Set Pair := {e | incident e}

-- If a set is initially available under every cover, it contains at most one incidence.
private theorem single {S : Set Pair} (h : ∀ t, S ∈ startF (Z t)) (a b : Pair)
    (ae : a ∈ E) (be : b ∈ E) (as' : a ∈ S) (bs : b ∈ S) : a = b := by
  have common (t : T) : ∃ v, z t v = true ∧ (a.1 = v ∨ a.2 = v) ∧ (b.1 = v ∨ b.2 = v) := by
    rcases h t with empty | ⟨v,hv,all⟩
    · rw [empty] at bs; exact False.elim bs
    · exact ⟨v,hv,all _ as',all _ bs⟩
  change incident a at ae
  change incident b at be
  have ap := ae.1
  have al := ae.2.1
  have bp := be.1
  have bl := be.2.1
  apply Prod.ext
  · obtain ⟨t,off⟩ := omits a.2
    obtain ⟨v,on,ha,hb⟩ := common t
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ha.trans hb.symm
    · have eq := congrArg Fin.val (ha.trans hb.symm); omega
    all_goals rw [ha,on] at off; contradiction
  · obtain ⟨t,off⟩ := omits a.1
    obtain ⟨v,on,ha,hb⟩ := common t
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha,on] at off; contradiction
    · rw [ha,on] at off; contradiction
    · have eq := congrArg Fin.val (ha.trans hb.symm); omega
    · exact ha.trans hb.symm

private theorem neutral (r : Set Pair × Set Pair) :
    ∃ t, Budget (f t) (stepF (startF (Z t)) r) 0 := by
  classical
  by_cases active : ∀ t, r.1 ∈ startF (Z t) ∧ r.2 ∈ startF (Z t)
  · have small (t : T) (S : Set Pair) (h : ∀ t, S ∈ startF (Z t)) :
        ((hits (f t) S).card ≤ 1) := by
      have h0 := initial (f t) (Z t) (uniq t) {S} (by intro a ha; obtain rfl := Finset.mem_singleton.mp ha; exact h t)
      simpa using h0
    have avoid : ∃ t, ∀ i, f t i ∉ r.1 := by
      by_cases existsEdge : ∃ e ∈ E, e ∈ r.1
      · obtain ⟨e,he,mem⟩ := existsEdge
        obtain ⟨t,off⟩ := avoids e he
        exact ⟨t,fun i hi => off i (single (fun t => (active t).1) _ _ (occurs t i) he hi mem)⟩
      · exact ⟨0,fun i hi => existsEdge ⟨_,occurs 0 i,hi⟩⟩
    obtain ⟨t,off⟩ := avoid
    refine ⟨t,?_⟩
    intro A hA
    have card (S) (hs : S ∈ A) : (hits (f t) S).card ≤ 1 := by
      rcases hA S hs with old | ⟨_,_,sub⟩
      · have h0 := initial (f t) (Z t) (uniq t) {S} (by intro x hx; obtain rfl := Finset.mem_singleton.mp hx; exact old)
        simpa using h0
      · have incl : hits (f t) S ⊆ hits (f t) r.2 := by
          intro i hi
          exact (hit _).mpr ((sub ((hit _).mp hi)).resolve_left (off i))
        exact (Finset.card_le_card incl).trans (small t _ (fun j => (active j).2))
    exact Finset.card_biUnion_le.trans (by simpa using Finset.sum_le_sum card)
  · push Not at active
    obtain ⟨t,bad⟩ := active
    refine ⟨t,?_⟩
    intro A ready
    apply initial (f t) (Z t) (uniq t) A
    intro S hs
    rcases ready S hs with old | ⟨a,b,_⟩
    · exact old
    · exact (bad a b).elim
end PEqualNP.Research.PlaneFourFirstJoin

open PEqualNP.Research.PlaneFourCoverCount PEqualNP.Research.PlaneFourFirstJoin in
theorem PEqualNP.Research.PlaneFourFirstJoin : ∀ rs : List (Set Pair × Set Pair),
    (∀ Z : Set V, (∀ e : Pair, incident e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e : Pair | incident e} ∈ rs.foldl stepF (startF Z)) → 34 ≤ rs.length := by
  intro rs works
  classical
  have finish (t : T) : hits (f t) E = Finset.univ := Finset.eq_univ_of_forall (fun i => (hit _).mpr (occurs t i))
  cases rs with
  | nil =>
    have av := works (Z 0) (covers 0)
    have h := initial (f 0) (Z 0) (uniq 0) {E} (by intro s hs; obtain rfl := Finset.mem_singleton.mp hs; exact av)
    simp [finish] at h
  | cons r rs =>
    obtain ⟨t,b⟩ := neutral r
    have av := works (Z t) (covers t)
    have h := iterate (f t) rs _ 0 b {E} (by intro s hs; obtain rfl := Finset.mem_singleton.mp hs; exact av)
    simp [finish] at h
    simp only [List.length_cons]
    omega
