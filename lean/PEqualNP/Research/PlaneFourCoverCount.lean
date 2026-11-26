import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose

namespace PEqualNP.Research.PlaneFourCoverCount
abbrev V := Fin 42
abbrev Pair := V × V
def incident (e : Pair) : Prop := e.1.val < 21 ∧ 21 ≤ e.2.val ∧
    (e.2.val + 21 - e.1.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
instance (e : Pair) : Decidable (incident e) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def inside (v : V) := (0x35e7ffffe7a : Nat).testBit v.val
private def samples : Array (Nat × Nat) := #[(1, 39), (3, 31), (4, 32), (5, 31), (6, 32), (9, 37), (10, 31), (11, 31), (12, 32), (13, 39), (14, 31), (15, 32), (16, 37), (17, 37), (18, 39), (19, 39), (20, 37), (0, 21), (2, 22), (2, 23), (7, 24), (8, 25), (0, 26), (7, 27), (0, 28), (8, 29), (2, 30), (7, 33), (8, 34), (7, 35), (8, 36), (0, 38), (2, 40), (0, 41)]
def sample (i : Fin 34) : Pair :=
  (Fin.ofNat 42 (samples[i.val]!).1, Fin.ofNat 42 (samples[i.val]!).2)
theorem sampleEdge : ∀ i, incident (sample i) := by decide +kernel
set_option maxHeartbeats 0 in
private theorem coverRows : ∀ a b : V, incident (a,b) → inside a = true ∨ inside b = true := by
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
theorem vertexCover (e : Pair) : incident e → inside e.1 = true ∨ inside e.2 = true := coverRows e.1 e.2
private def owner (v : V) := (0x86001f01e75c6c001a6585d65544d24503ce34c2ca2481c61400040c2040000 >>> (6*v.val)) &&& 63
private theorem owners : ∀ i : Fin 34,
    (inside (sample i).1 = true → owner (sample i).1 = i.val) ∧
    (inside (sample i).2 = true → owner (sample i).2 = i.val) := by decide +kernel
theorem exclusive (v : V) (hv : inside v = true) (i j : Fin 34)
    (a : (sample i).1 = v ∨ (sample i).2 = v) (b : (sample j).1 = v ∨ (sample j).2 = v) : i = j := by
  have key (k : Fin 34) (h : (sample k).1 = v ∨ (sample k).2 = v) : owner v = k.val := by
    rcases h with e | e
    · rw [← e] at hv ⊢
      exact (owners k).1 hv
    · rw [← e] at hv ⊢
      exact (owners k).2 hv
  exact Fin.ext ((key i a).symm.trans (key j b))

abbrev Family := Set (Set Pair)
def stepF (F : Family) (r : Set Pair × Set Pair) : Family :=
  {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
def startF (Z : Set V) : Family :=
  {s | s = ∅ ∨ ∃ v ∈ Z, ∀ e ∈ s, e.1 = v ∨ e.2 = v}
section
variable (f : Fin 34 → Pair)
noncomputable def hits (s : Set Pair) : Finset (Fin 34) := by
  classical
  exact Finset.univ.filter (fun i => f i ∈ s)
theorem hit {s : Set Pair} {i : Fin 34} : i ∈ hits f s ↔ f i ∈ s := by classical simp [hits]

def Budget (F : Family) (k : Nat) := ∀ T : Finset (Set Pair), (∀ s ∈ T, s ∈ F) →
    (T.biUnion (hits f)).card ≤ T.card + k

theorem initial (Z : Set V) (uniq : ∀ v ∈ Z, ∀ i j, ((f i).1 = v ∨ (f i).2 = v) → ((f j).1 = v ∨ (f j).2 = v) → i = j) : Budget f (startF Z) 0 := by
  classical
  intro T ht
  have small (s) (hs : s ∈ T) : (hits f s).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases ht s hs with rfl | ⟨v,hv,h⟩
    · exact False.elim ((hit f).mp hi)
    · exact uniq v hv i j (h _ ((hit f).mp hi)) (h _ ((hit f).mp hj))
  exact (Finset.card_biUnion_le).trans (by simpa using Finset.sum_le_sum small)

theorem advance (F : Family) (k : Nat) (r : Set Pair × Set Pair) (h : Budget f F k) :
    Budget f (stepF F r) (k+1) := by
  classical
  intro T ht
  by_cases allOld : ∀ s ∈ T, s ∈ F
  · exact (h T allOld).trans (by omega)
  push Not at allOld
  obtain ⟨s,hs,hn⟩ := allOld
  obtain ⟨left,right,_⟩ := (ht s hs).resolve_left hn
  let old := T.filter (fun a => a ∈ F)
  let need := insert r.1 (insert r.2 old)
  have built : ∀ a ∈ need, a ∈ F := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact left
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact right
    exact (Finset.mem_filter.mp ha).2
  have incl : T.biUnion (hits f) ⊆ need.biUnion (hits f) := by
    intro i hi
    obtain ⟨a,ha,on⟩ := Finset.mem_biUnion.mp hi
    by_cases ok : a ∈ F
    · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha,ok⟩)),on⟩
    obtain ⟨_,_,sub⟩ := (ht a ha).resolve_left ok
    rcases sub ((hit f).mp on) with x | x
    · exact Finset.mem_biUnion.mpr ⟨r.1,Finset.mem_insert_self _ _,(hit f).mpr x⟩
    · exact Finset.mem_biUnion.mpr ⟨r.2,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),(hit f).mpr x⟩
  have le := (Finset.card_le_card incl).trans (h need built)
  have less : old.card < T.card := Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨s,hs,by simp [old,hn]⟩)
  have h1 := Finset.card_insert_le r.1 (insert r.2 old)
  have h2 := Finset.card_insert_le r.2 old
  dsimp only [need] at le
  omega

theorem iterate (rs : List (Set Pair × Set Pair)) (F : Family) (k : Nat) (h : Budget f F k) :
    Budget f (rs.foldl stepF F) (k + rs.length) := by
  induction rs generalizing F k with
  | nil => simpa using h
  | cons r rs ih =>
    simpa [List.foldl_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih _ _ (advance f F k r h)

end
end PEqualNP.Research.PlaneFourCoverCount

open PEqualNP.Research.PlaneFourCoverCount in
theorem PEqualNP.Research.PlaneFourCoverCount : ∀ rs : List (Set Pair × Set Pair),
    (∀ Z : Set V, (∀ e : Pair, incident e → e.1 ∈ Z ∨ e.2 ∈ Z) →
      {e : Pair | incident e} ∈ rs.foldl stepF (startF Z)) → 33 ≤ rs.length := by
  intro rs works
  let E : Set Pair := {e | incident e}
  have avail := works {v | inside v = true} vertexCover
  classical
  have h := iterate sample rs _ 0 (initial sample _ exclusive) {E} (by intro s hs; obtain rfl := Finset.mem_singleton.mp hs; exact avail)
  have full : hits sample E = Finset.univ := Finset.eq_univ_of_forall (fun i => (hit sample).mpr (sampleEdge i))
  simp [full] at h
  omega
