import PEqualNP.Research.SharedNeighborhoodOr

/-! Prune OR gates that cannot feed either side of a productive biclique.
This charges the two fixed free OR seeds only when a vertex can use both
endpoints as neighbors. -/

namespace PEqualNP.Research.PetersenSeededBicliques

open PEqualNP.Research.PetersenBicliqueCost PEqualNP.Research.SharedNeighborhoodOr

def useful (s : Mask) : Bool := decide (∃ c : V, ∀ v ∈ s, ordered c v ∈ edges)
def keep (g : Join) : Bool := useful (output g)

private theorem down {s t : Mask} (st : s ⊆ t) (h : useful t = true) : useful s = true := by
  obtain ⟨c,hc⟩ := of_decide_eq_true h
  exact decide_eq_true ⟨c,fun v hv => hc v (st hv)⟩

private theorem still_available {gs : List Join} {s : Mask} (hs : Available gs s)
    (good : useful s = true) : Available (gs.filter keep) s := by
  rcases hs with tiny | ⟨g,hg,rfl⟩
  · exact Or.inl tiny
  · exact Or.inr ⟨g,List.mem_filter.mpr ⟨hg,good⟩,rfl⟩

private theorem still_legal {gs : List Join} (h : Legal gs) : Legal (gs.filter keep) := by
  induction gs with
  | nil => trivial
  | cons g gs ih =>
    by_cases hk : keep g = true
    · simp only [List.filter_cons_of_pos hk]
      exact ⟨ih h.1, still_available h.2.1 (down Finset.subset_union_left hk),
        still_available h.2.2 (down Finset.subset_union_right hk)⟩
    · simpa [List.filter_cons,hk] using ih h.1

theorem useful_gate_bound {k : Nat} (t : Fin k → Term) (gs : List Join)
    (legal : Legal gs) (nonempty : ∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty)
    (built : ∀ i, Available gs (t i).1 ∧ Available gs (t i).2)
    (covers : Finset.univ.biUnion (fun i => support (t i)) = edges) :
    16 ≤ (gs.filter keep).length + 2*k - 1 := by
  apply lower_bicliques t _ (still_legal legal) nonempty _ covers
  intro i
  have sub (a b : V) (ha : a ∈ (t i).1) (hb : b ∈ (t i).2) : ordered a b ∈ edges := by
    rw [← covers]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _, Finset.mem_image.mpr
      ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩⟩
  obtain ⟨a,ha⟩ := (nonempty i).1
  obtain ⟨b,hb⟩ := (nonempty i).2
  refine ⟨still_available (built i).1 (decide_eq_true ⟨b,?_⟩),
    still_available (built i).2 (decide_eq_true ⟨a,fun v hv => sub a v ha hv⟩)⟩
  intro v hv
  simpa only [ordered,min_comm b v,max_comm b v] using sub v b hv hb

def firstSeed : Join := ({0},{4})

theorem first_seed_unusable : keep firstSeed = false := by decide +kernel

/-- Tail cost counts the input OR gates after the two free wires, all k
AND gates, and k-1 final OR gates. -/
theorem seeded_floor {k : Nat} (t : Fin k → Term) (tail : List Join) (second : Join)
    (legal : Legal (tail ++ [second,firstSeed]))
    (nonempty : ∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty)
    (built : ∀ i, Available (tail ++ [second,firstSeed]) (t i).1 ∧
      Available (tail ++ [second,firstSeed]) (t i).2)
    (covers : Finset.univ.biUnion (fun i => support (t i)) = edges) :
    (if keep second then 15 else 16) ≤ tail.length + 2*k - 1 := by
  have h := useful_gate_bound t _ legal nonempty built covers
  have len := List.length_filter_le keep tail
  cases h2 : keep second <;>
    simp [List.filter_append,first_seed_unusable,h2] at h ⊢ <;> omega

/-- The seed, paid input joins (newest first), and five bicliques for each
of the twenty masks in the order of the assignment. -/
private def examples : List (Join × List Join × List Term) := [
  (({0},{1}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({0},{2}),[({3},{6}),({0,7},{8}),({0},{7}),({0},{3}),({3},{7}),({0,2},{6})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7,8}),({8},{3,6})]),
  (({1},{2}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({0},{3}),[({3},{6}),({0,7},{8}),({0},{7}),({3},{7}),({0,2},{6}),({0},{2})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7,8}),({8},{3,6})]),
  (({1},{3}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({2},{3}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({1},{4}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({2},{4}),[({1},{8}),({7},{8}),({2,4},{8}),({1},{7}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,7}),({3},{2,4,8}),({5},{7,8}),({6},{1,8})]),
  (({3},{4}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({1},{5}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,5},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({2},{5}),[({5},{6}),({2,4},{8}),({2},{4}),({2},{6}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({1},{2,6}),({3},{2,4,8}),({7},{2,5}),({8},{5,6})]),
  (({0},{6}),[({3},{6}),({0,7},{8}),({0},{7}),({0},{3}),({3},{7}),({0,6},{2})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7,8}),({8},{3,6})]),
  (({1},{6}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({2},{6}),[({3},{6}),({0,7},{8}),({0},{7}),({0},{3}),({3},{7}),({2,6},{0})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7,8}),({8},{3,6})]),
  (({3},{6}),[({0,7},{8}),({0},{7}),({0},{3}),({3},{7}),({0,2},{6}),({0},{2})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7,8}),({8},{3,6})]),
  (({4},{6}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({5},{6}),[({5,6},{3}),({0},{7}),({0},{3}),({3},{7}),({0,2},{6}),({0},{2})],[({1},{0,2,6}),({2},{3,7}),({4},{0,3}),({5},{0,7}),({8},{3,5,6})]),
  (({2},{7}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({6},{7}),[({1},{8}),({7},{8}),({4},{8}),({1,3},{7}),({1},{3}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,3,7}),({3},{4,8}),({5},{7,8}),({6},{1,8})]),
  (({2},{8}),[({1},{8}),({7},{8}),({2,8},{4}),({1},{7}),({1,4},{5}),({1},{4})],[({0},{1,4,5}),({2},{1,7}),({3},{2,4,8}),({5},{7,8}),({6},{1,8})])]

def exampleSeed (a : Fin 20) : Join := (examples[a.val]!).1
private def exampleTail (a : Fin 20) : List Join := (examples[a.val]!).2.1
private def exampleTerm (a : Fin 20) (i : Fin 5) : Term := ((examples[a.val]!).2.2)[i.val]!

private def ready (gs : List Join) (s : Mask) := decide (s.card ≤ 1) || gs.any (fun g => output g == s)
private theorem ready_iff (gs : List Join) (s : Mask) : ready gs s = true ↔ Available gs s := by
  simp [ready,Available,List.any_eq_true]

private def legalB : List Join → Bool
  | [] => true
  | g :: gs => legalB gs && (ready gs g.1 && ready gs g.2)

private theorem legalB_iff (gs : List Join) : legalB gs = true ↔ Legal gs := by
  induction gs with
  | nil => simp [Legal,legalB]
  | cons g gs ih => simp [legalB,Legal,ih,ready_iff]

private def cert (a : Fin 20) : Bool :=
  let tail := exampleTail a
  let second := exampleSeed a
  let t := exampleTerm a
  let net := tail ++ [second,firstSeed]
  legalB net && ((List.finRange 5).all fun i => decide ((t i).1.Nonempty ∧ (t i).2.Nonempty) &&
    (ready net (t i).1 && ready net (t i).2)) &&
    decide (Finset.univ.biUnion (fun i => support (t i)) = edges) &&
    decide (tail.length + 2*5 - 1 = (if keep second then 15 else 16))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem all_cert : ∀ a : Fin 20, cert a = true := by decide +kernel

def seedMasks : List Nat := [3,5,6,9,10,12,18,20,24,34,36,65,66,68,72,80,96,132,192,260]
def inputMask (g : Join) : Nat := (output g).sum fun v => 2^v.val

theorem masks_match : ∀ a : Fin 20, inputMask (exampleSeed a) = seedMasks[a.val]! := by decide +kernel

theorem singleton_inputs : ∀ a : Fin 20, (exampleSeed a).1.card = 1 ∧
    (exampleSeed a).2.card = 1 ∧ Disjoint (exampleSeed a).1 (exampleSeed a).2 := by decide +kernel

/-- The lower bound is attained by a five-term network in every listed case. -/
theorem sharp_for_every_seed (a : Fin 20) : ∃ second : Join, inputMask second = seedMasks[a.val]! ∧
    ∃ (tail : List Join) (t : Fin 5 → Term), Legal (tail ++ [second,firstSeed]) ∧
    (∀ i, (t i).1.Nonempty ∧ (t i).2.Nonempty) ∧
    (∀ i, Available (tail ++ [second,firstSeed]) (t i).1 ∧
      Available (tail ++ [second,firstSeed]) (t i).2) ∧
    Finset.univ.biUnion (fun i => support (t i)) = edges ∧
    tail.length + 2*5 - 1 = (if keep second then 15 else 16) := by
  have h := all_cert a
  simp only [cert,Bool.and_eq_true,decide_eq_true_eq,legalB_iff,List.all_eq_true,ready_iff] at h
  refine ⟨exampleSeed a,masks_match a,exampleTail a,exampleTerm a,h.1.1.1,?_,?_,h.1.2,h.2⟩
  · exact fun i => (h.1.1.2 i (List.mem_finRange _)).1
  · exact fun i => (h.1.1.2 i (List.mem_finRange _)).2

theorem tally : ((List.finRange 20).filter fun a => keep (exampleSeed a)).length = 12 := by
  decide +kernel

end PEqualNP.Research.PetersenSeededBicliques
