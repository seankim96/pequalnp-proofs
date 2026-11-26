import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose

namespace PEqualNP.Research.PlaneFourSharedStars
abbrev V := Fin 42
abbrev Pair := V × V
abbrev Mask := Finset V
abbrev Join := Mask × Mask
def ordered (a b : V) : Pair := (min a b,max a b)
def edges := Finset.univ.filter fun e : Pair => decide (e.1.val < 21 ∧ 21 ≤ e.2.val ∧ (e.2.val+21-e.1.val)%21 ∈ ([0,5,7,17,20] : List Nat))
def output (g : Join) := g.1 ∪ g.2
def Available (gs : List Join) (s : Mask) : Prop := s.card ≤ 1 ∨ ∃ g ∈ gs, output g = s
def support (t : Mask × Mask) : Finset Pair := (t.1 ×ˢ t.2).image fun p => ordered p.1 p.2
abbrev Term := Mask × Mask
private def maskOf (v : V) := (#[0x24014200000, 0x8028600000, 0x10050c00000, 0x200a1800000, 0x143200000, 0x286400000, 0x50c800000, 0xa19000000, 0x1432000000, 0x2864000000, 0x50c8000000, 0xa190000000, 0x14320000000, 0x28640000000, 0x10c80200000, 0x21900400000, 0x3200a00000, 0x6401400000, 0xc802800000, 0x19005000000, 0x3200a000000, 0x14013, 0x28026, 0x5004c, 0xa0098, 0x140130, 0x80261, 0x1004c2, 0x985, 0x130a, 0x2614, 0x4c28, 0x9850, 0x130a0, 0x26140, 0x4c280, 0x98500, 0x130a00, 0x61401, 0xc2802, 0x185004, 0x10a009] : Array Nat)[v.val]!
private theorem bits : ∀ a b : V, (maskOf a).testBit b.val = decide (
    (ordered a b).1.val < 21 ∧ 21 ≤ (ordered a b).2.val ∧
    ((ordered a b).2.val+21-(ordered a b).1.val)%21 ∈ ([0,5,7,17,20] : List Nat)) := by
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
private theorem geometry : ∀ a b : V, a ≠ b →
    let m := maskOf a &&& maskOf b
    m = 0 ∨ m = 2^m.log2 := by
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
private theorem no_square (a b c d : V) (ab : a ≠ b) (cd : c ≠ d)
    (ac : ordered a c ∈ edges) (ad : ordered a d ∈ edges)
    (bc : ordered b c ∈ edges) (bd : ordered b d ∈ edges) : False := by
  let m := maskOf a &&& maskOf b
  have on (x : V) (ax : ordered a x ∈ edges) (bx : ordered b x ∈ edges) : m.testBit x.val = true := by
    simp only [m,Nat.testBit_and,bits,Bool.and_eq_true]
    exact ⟨Finset.mem_filter.mp ax |>.2,Finset.mem_filter.mp bx |>.2⟩
  have onC := on c ac bc
  have onD := on d ad bd
  rcases geometry a b ab with h | h
  · change m = 0 at h
    simp [h] at onC
  · change m = 2^m.log2 at h
    have e1 := congrArg (fun y : Nat => y.testBit c.val) h
    have e2 := congrArg (fun y : Nat => y.testBit d.val) h
    simp only [Nat.testBit_two_pow] at e1 e2
    exact cd (Fin.ext ((of_decide_eq_true (e1.symm.trans onC)).symm.trans (of_decide_eq_true (e2.symm.trans onD))))
private def flag (i : Fin 105) : Pair :=
  let p := i.val / 5
  let diff := (#[0,5,7,17,20] : Array Nat)[i.val % 5]!
  (Fin.ofNat 42 p,Fin.ofNat 42 (21 + (p+diff)%21))
private def recover (e : Pair) := 5*e.1.val + ([0,5,7,17,20] : List Nat).idxOf ((e.2.val+21-e.1.val)%21)
private theorem decode : ∀ i : Fin 105, recover (flag i) = i.val := by decide +kernel
private theorem validFlag : ∀ i : Fin 105,
    let e := flag i
    e.1.val < 21 ∧ 21 ≤ e.2.val ∧ (e.2.val+21-e.1.val)%21 ∈ ([0,5,7,17,20] : List Nat) := by decide +kernel
private theorem edge_count : 105 ≤ edges.card := by
  have inj : Function.Injective flag := by
    intro i j eq
    exact Fin.ext ((decode i).symm.trans ((congrArg recover eq).trans (decode j)))
  have incl : Finset.univ.image flag ⊆ edges := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using validFlag i⟩
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card incl
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

def Legal : List Join → Prop
  | [] => True
  | g :: gs => Legal gs ∧ Available gs g.1 ∧ Available gs g.2

abbrev Charged (T : Mask) (g : Join) := 2 ≤ (output g).card ∧ output g ⊆ T

def chargeCount (T : Mask) : List Join → ℕ
  | [] => 0
  | g :: gs => (if Charged T g then 1 else 0) + chargeCount T gs

/-- Reading a circuit backwards, expanding a needed gate introduces at most
two masks in place of one. A singleton can be retained as a terminal. -/
private theorem account (T : Mask) (gs : List Join) (legal : Legal gs)
    (needed : Finset Mask) (present : ∀ s ∈ needed, Available gs s)
    (inside : ∀ s ∈ needed, s ⊆ T) :
    (needed.biUnion id).card ≤ needed.card + chargeCount T gs := by
  induction gs generalizing needed with
  | nil =>
    have small (s : Mask) (hs : s ∈ needed) : s.card ≤ 1 := by
      simpa [Available] using present s hs
    have ub := Finset.card_biUnion_le (s := needed) (t := id)
    have sumBound := Finset.sum_le_sum (s := needed) (g := fun _ => (1 : ℕ)) small
    simp [chargeCount] at ub sumBound ⊢
    exact ub.trans sumBound
  | cons g gs ih =>
    have older (s : Mask) (hs : s ∈ needed) (ne : s ≠ output g) : Available gs s := by
      rcases present s hs with h | ⟨j,hj,he⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact (ne he.symm).elim
        · exact Or.inr ⟨j,hj,he⟩
    by_cases used : output g ∈ needed
    · by_cases charge : Charged T g
      · let rest := needed.erase (output g)
        let next := insert g.1 (insert g.2 rest)
        have ready (s : Mask) (hs : s ∈ next) : Available gs s := by
          rcases Finset.mem_insert.mp hs with rfl|hs
          · exact legal.2.1
          rcases Finset.mem_insert.mp hs with rfl|hs
          · exact legal.2.2
          exact older s (Finset.mem_erase.mp hs).2 (Finset.mem_erase.mp hs).1
        have within (s : Mask) (hs : s ∈ next) : s ⊆ T := by
          rcases Finset.mem_insert.mp hs with rfl|hs
          · exact Finset.Subset.trans Finset.subset_union_left charge.2
          rcases Finset.mem_insert.mp hs with rfl|hs
          · exact Finset.Subset.trans Finset.subset_union_right charge.2
          exact inside s (Finset.mem_erase.mp hs).2
        have covered : needed.biUnion id ⊆ next.biUnion id := by
          intro p hp
          obtain ⟨s,hs,hp⟩ := Finset.mem_biUnion.mp hp
          by_cases eq : s = output g
          · subst s
            rcases Finset.mem_union.mp hp with hl|hr
            · exact Finset.mem_biUnion.mpr ⟨g.1,by simp [next],hl⟩
            · exact Finset.mem_biUnion.mpr ⟨g.2,by simp [next],hr⟩
          · exact Finset.mem_biUnion.mpr ⟨s,by
              apply Finset.mem_insert_of_mem
              apply Finset.mem_insert_of_mem
              exact Finset.mem_erase.mpr ⟨eq,hs⟩,hp⟩
        have linear : next.card ≤ needed.card+1 := by
          have a := Finset.card_insert_le g.1 (insert g.2 rest)
          have b := Finset.card_insert_le g.2 rest
          have e : rest.card = needed.card-1 := Finset.card_erase_of_mem used
          have pos := Finset.card_pos.mpr ⟨output g,used⟩
          change (insert g.1 (insert g.2 rest)).card ≤ _
          omega
        have bound := (Finset.card_le_card covered).trans (ih legal.1 next ready within)
        simp only [chargeCount,ite_eq_left charge]
        omega
      · have tiny : (output g).card ≤ 1 := by
          by_contra! large
          exact charge ⟨large,inside _ used⟩
        have ready (s : Mask) (hs : s ∈ needed) : Available gs s := by
          by_cases ne : s = output g
          · exact Or.inl (ne ▸ tiny)
          · exact older s hs ne
        simpa [chargeCount,charge] using ih legal.1 needed ready inside
    · have ready (s : Mask) (hs : s ∈ needed) : Available gs s :=
        older s hs (fun eq => used (eq ▸ hs))
      have bound := ih legal.1 needed ready inside
      by_cases charge : Charged T g <;> simp [chargeCount,charge] <;> omega

theorem leaves_bound (T : Mask) (gs : List Join) (valid : Legal gs)
    (available : Available gs T) : T.card ≤ chargeCount T gs + 1 := by
  have bound := account T gs valid {T} (by simpa) (by simp)
  simpa [Nat.add_comm] using bound

/-- A genuine union of at least two variables can be charged to at most one
distinct star center: two centers and two common leaves would form a square. -/
private theorem unique_charge {k : ℕ} (center : Fin k → V) (distinct : Function.Injective center)
    (leaf : Fin k → Mask) (valid : ∀ i, ∀ p ∈ leaf i, ordered (center i) p ∈ edges)
    (g : Join) {i j : Fin k} (hi : Charged (leaf i) g) (hj : Charged (leaf j) g) : i = j := by
  by_contra ne
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp hi.1
  exact no_square _ _ _ _ (fun eq => ne (distinct eq)) ab
    (valid i a (hi.2 ha)) (valid i b (hi.2 hb)) (valid j a (hj.2 ha)) (valid j b (hj.2 hb))

theorem total_charge {k : ℕ} (center : Fin k → V) (distinct : Function.Injective center)
    (leaf : Fin k → Mask) (valid : ∀ i, ∀ p ∈ leaf i, ordered (center i) p ∈ edges)
    (gs : List Join) : (∑ i, chargeCount (leaf i) gs) ≤ gs.length := by
  induction gs with
  | nil => simp [chargeCount]
  | cons g gs ih =>
    let used := Finset.univ.filter fun i => Charged (leaf i) g
    have one : used.card ≤ 1 := Finset.card_le_one_iff.mpr (fun hi hj =>
      unique_charge center distinct leaf valid g (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    have indicators : (∑ i, if Charged (leaf i) g then 1 else 0) = used.card := by
      simp [used,Finset.sum_boole]
    simp only [chargeCount, Finset.sum_add_distrib, indicators, List.length_cons]
    omega


/-- Multiple terms may have the same center. Accounting for all their leaf
sets together charges a shared OR only once. -/
theorem lower_stars {k : ℕ} (center : Fin k → V) (leaf : Fin k → Mask)
    (valid : ∀ i, ∀ p ∈ leaf i, ordered (center i) p ∈ edges)
    (covers : Finset.univ.biUnion (fun i => support ({center i},leaf i)) = edges)
    (gs : List Join) (legal : Legal gs) (built : ∀ i, Available gs (leaf i)) :
    104 ≤ gs.length + k - 1 := by
  let terms (c : V) := Finset.univ.filter (fun i => center i = c)
  let sets (c : V) := (terms c).image leaf
  let served (c : V) := (sets c).biUnion id
  let neighbors (c : V) := Finset.univ.filter fun p => ordered c p ∈ edges
  have byCenter (c : V) : (served c).card ≤ (terms c).card + chargeCount (neighbors c) gs := by
    have ready (s : Mask) (hs : s ∈ sets c) : Available gs s := by
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
      exact built i
    have within (s : Mask) (hs : s ∈ sets c) : s ⊆ neighbors c := by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
      intro p hp
      have eq := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ valid i p hp⟩
    exact (account _ gs legal (sets c) ready within).trans
      (Nat.add_le_add_right Finset.card_image_le _)
  have reach (e : Pair) (h : e ∈ edges) : ∃ c ∈ Finset.univ.image center, ∃ p ∈ served c,
      ordered c p = e := by
    rw [← covers] at h
    obtain ⟨i,_,hm⟩ := Finset.mem_biUnion.mp h
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp hm
    have ha : a = center i := by simpa using (Finset.mem_product.mp hp).1
    have hb := (Finset.mem_product.mp hp).2
    exact ⟨center i,Finset.mem_image_of_mem _ (Finset.mem_univ i),b,
      Finset.mem_biUnion.mpr ⟨leaf i, Finset.mem_image_of_mem leaf
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩),hb⟩,by rw [ha]⟩
  have sub : edges ⊆ Finset.univ.biUnion (fun c => (served c).image (ordered c)) := by
    intro e he
    obtain ⟨c,_,p,hp,eq⟩ := reach e he
    exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hp,eq⟩⟩
  have edgeBound : 105 ≤ ∑ c, (served c).card := by
    apply edge_count.trans
    exact ((Finset.card_le_card sub).trans Finset.card_biUnion_le).trans
      (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
  have fiber : (∑ c, (terms c).card) = k := by
    simpa [terms] using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ center
  have total := Finset.sum_le_sum (s := Finset.univ) (fun c _ => byCenter c)
  rw [Finset.sum_add_distrib,fiber] at total
  have budget := total_charge (fun c : V => c) (fun _ _ h => h) neighbors
    (fun _ _ h => (Finset.mem_filter.mp h).2) gs
  have combined : 105 ≤ k + gs.length := edgeBound.trans (total.trans (Nat.add_le_add_left budget k))
  omega

/-- One common OR network can supply both inputs of every AND. The AND terms
may overlap, repeat or choose the same star center. Only the final OR of the
terms and the k ANDs are charged separately. -/
theorem lower_bicliques {k : ℕ} (t : Fin k → Term) (gs : List Join) (legal : Legal gs)
    (nonempty : ∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty)
    (built : ∀ i, Available gs (t i).1 ∧ Available gs (t i).2)
    (covers : Finset.univ.biUnion (fun i => support (t i)) = edges) :
    104 ≤ gs.length + k - 1 := by
  have sub (i : Fin k) : support (t i) ⊆ edges := by
    rw [← covers]
    exact fun _ h => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩
  have data (i : Fin k) : ∃ c : V, ∃ L : Mask, Available gs L ∧
      support ({c},L) = support (t i) ∧ ∀ p ∈ L, ordered c p ∈ edges := by
    rcases singleton_side (t i) (nonempty i).1 (nonempty i).2 (sub i) with hl|hr
    · obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hl
      refine ⟨c,(t i).2,(built i).2,by simp [support,hc],?_⟩
      intro p hp
      exact sub i (Finset.mem_image.mpr ⟨(c,p),Finset.mem_product.mpr ⟨by simp [hc],hp⟩,rfl⟩)
    · obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hr
      have swap (p : V) : ordered c p = ordered p c := by simp [ordered,min_comm,max_comm]
      refine ⟨c,(t i).1,(built i).1,?_,?_⟩
      · ext e
        simp [support,hc,swap]
      · intro p hp
        rw [swap]
        exact sub i (Finset.mem_image.mpr ⟨(p,c),Finset.mem_product.mpr ⟨hp,by simp [hc]⟩,rfl⟩)
  choose center leaf available same valid using data
  exact lower_stars center leaf valid (by simpa only [same] using covers) gs legal available

private theorem legalFrom (gs : List Join)
    (h : ∀ pre g rest, gs = pre ++ g :: rest → Available rest g.1 ∧ Available rest g.2) : Legal gs := by
  induction gs with
  | nil => trivial
  | cons g tail ih =>
    refine ⟨ih (fun pre j rest eq => h (g :: pre) j rest (by simp [eq])),h [] g tail rfl⟩
end PEqualNP.Research.PlaneFourSharedStars

open PEqualNP.Research.PlaneFourSharedStars in
theorem PEqualNP.Research.PlaneFourSharedStars : ∀ (k : Nat) (terms : Fin k → Mask × Mask) (gs : List Join),
    (∀ pre g rest, gs = pre ++ g :: rest → Available rest g.1 ∧ Available rest g.2) →
    (∀ i, (terms i).1.Nonempty ∧ (terms i).2.Nonempty) →
    (∀ i, Available gs (terms i).1 ∧ Available gs (terms i).2) →
    Finset.univ.biUnion (fun i => support (terms i)) = edges →
    104 ≤ gs.length + k - 1 := by
  intro k terms gs h ne avail cov
  exact lower_bicliques terms gs (legalFrom gs h) ne avail cov
