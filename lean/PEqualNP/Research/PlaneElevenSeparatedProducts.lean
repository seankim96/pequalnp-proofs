import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Choose

/-! A 21-row witness for the cost of an independent AND layer after the
fixed 17-gate prefix in case 35 of L-meta-2625. The low 43 bits of a
signature are the inputs and prefix wires; its high 43 bits are the same
wires gated by wire 32. Each side of a product can OR any subset. -/
namespace PEqualNP.Research.PlaneElevenSeparatedProducts.Core
def pos (i : Fin 11) : Nat := (#[
  16386, 32772, 65600, 131104, 262400, 524800, 1048584, 2097168, 8389632, 16779264, 33558528
] : Array Nat)[i.val]!
def neg (i : Fin 10) : Nat := (#[
  1325076, 2266178, 9634310, 16975620, 20980052, 25183016, 33966600, 34636370, 44564522,
  51119128
] : Array Nat)[i.val]!
def sig (r : Nat) : Nat :=
  let wires := ([(false,0,1), (false,3,9), (true,15,27), (true,17,26), (true,13,26), (true,13,27), (false,2,6), (true,1,24), (true,15,32), (true,25,32), (true,0,17), (true,0,23), (true,0,25), (false,17,19), (false,20,24), (false,39,40), (true,7,41)] : List (Bool × Nat × Nat)).foldl
    (fun (z : Nat × Nat) g =>
      let a := z.1.testBit g.2.1
      let b := z.1.testBit g.2.2
      (z.1 ||| ((if g.1 then a && b else a || b).toNat <<< z.2), z.2 + 1)) (r,26)
  wires.1 ||| ((if wires.1.testBit 32 then wires.1 else 0) <<< 43)
abbrev Side := Finset (Fin 86)
def hit (A : Side) (r : Nat) : Prop := ∃ k ∈ A, r.testBit k.val = true
def term (T : Side × Side) (r : Nat) : Prop := hit T.1 r ∧ hit T.2 r
def pm (i : Fin 11) : Nat := (#[
  67125250, 188894947580367807217668, 37779508886663713587264, 2748779200544, 262400,
  2748913811968, 3298670149640, 2097168, 8389632, 3298551662592, 33558528
] : Array Nat)[i.val]!
def nm (i : Fin 10) : Nat := (#[
  29052010258109117681121300, 24372743647415861394969666, 33894279879277337937904134,
  33889031791829773856212740, 29052183145106362966483284, 3298694284072, 2748947253768,
  29509782520377880723096146, 2749024960554, 3848476034072
] : Array Nat)[i.val]!
-- Row-major table of local negative indices for the 11 × 11 positive pairs.
def triple (i j : Fin 11) : Fin 10 × Fin 10 × Fin 10 := (#[
  (0,0,0), (1, 2, 5), (1, 2, 5), (1, 5, 6), (1, 5, 6), (2, 5, 8), (0, 5, 8), (1, 5, 7), (1, 2, 5), (1, 5, 6), (0, 6, 7),
  (1, 2, 5), (0,0,0), (1, 2, 4), (1, 2, 5), (0, 1, 3), (2, 7, 8), (0, 5, 7), (0, 1, 7), (1, 2, 3), (0, 1, 3), (0, 1, 6),
  (1, 2, 5), (1, 2, 4), (0,0,0), (1, 2, 5), (0, 3, 4), (2, 7, 8), (2, 5, 7), (1, 2, 4), (1, 2, 3), (0, 3, 4), (1, 2, 7),
  (1, 5, 6), (1, 2, 5), (1, 2, 5), (0,0,0), (0, 3, 5), (1, 5, 8), (0, 5, 6), (0, 1, 8), (1, 2, 5), (0, 3, 5), (0, 6, 8),
  (1, 5, 6), (0, 1, 3), (0, 3, 4), (0, 3, 5), (0,0,0), (3, 6, 8), (0, 3, 6), (0, 1, 4), (0, 3, 5), (0, 3, 9), (0, 3, 6),
  (2, 5, 8), (2, 7, 8), (2, 7, 8), (1, 5, 8), (3, 6, 8), (0,0,0), (0, 5, 8), (1, 7, 9), (1, 2, 8), (0, 3, 9), (0, 6, 8),
  (0, 5, 8), (0, 5, 7), (2, 5, 7), (0, 5, 6), (0, 3, 6), (0, 5, 8), (0,0,0), (0, 1, 9), (0, 5, 9), (0, 3, 6), (0, 5, 7),
  (1, 5, 7), (0, 1, 7), (1, 2, 4), (0, 1, 8), (0, 1, 4), (1, 7, 9), (0, 1, 9), (0,0,0), (0, 1, 8), (0, 1, 4), (0, 1, 6),
  (1, 2, 5), (1, 2, 3), (1, 2, 3), (1, 2, 5), (0, 3, 5), (1, 2, 8), (0, 5, 9), (0, 1, 8), (0,0,0), (0, 3, 5), (0, 8, 9),
  (1, 5, 6), (0, 1, 3), (0, 3, 4), (0, 3, 5), (0, 3, 9), (0, 3, 9), (0, 3, 6), (0, 1, 4), (0, 3, 5), (0,0,0), (0, 3, 6),
  (0, 6, 7), (0, 1, 6), (1, 2, 7), (0, 6, 8), (0, 3, 6), (0, 6, 8), (0, 5, 7), (0, 1, 6), (0, 8, 9), (0, 3, 6), (0,0,0)
] : Array (Fin 10 × Fin 10 × Fin 10))[11*i.val+j.val]!

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem pos_ok : ∀ i, sig (pos i) = pm i := by decide
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem neg_ok : ∀ i, sig (neg i) = nm i := by decide
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem single_ok : ∀ (i : Fin 11) (k : Fin 86), (pm i).testBit k.val = true →
    ∃ j : Fin 10, (nm j).testBit k.val = true := by decide
private def covers (v a b : Nat) := v &&& (a ||| b) == v
private def edge (i j : Fin 11) (a b : Fin 10) :=
  covers (pm i) (nm a) (nm b) || covers (pm j) (nm a) (nm b)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem pair_ok : ∀ (i j : Fin 11), i ≠ j →
    let (a,b,c) := triple i j
    edge i j a b && edge i j b c && edge i j a c = true := by decide
-- A side hit survives in one of two negative rows whose union covers it.
private theorem splitHit {A : Side} {v a b : Nat} (h : covers v a b = true)
    (hv : hit A v) : hit A a ∨ hit A b := by
  obtain ⟨k,hk,hv⟩ := hv
  have e := congrArg (fun n : Nat => n.testBit k.val) (beq_iff_eq.mp h)
  simp [Nat.testBit_and,Nat.testBit_or,hv] at e
  rcases e with ha | hb
  · exact Or.inl ⟨k,hk,ha⟩
  · exact Or.inr ⟨k,hk,hb⟩
private theorem edgeHit {A : Side} {i j : Fin 11} {a b : Fin 10} (h : edge i j a b = true)
    (hi : hit A (pm i)) (hj : hit A (pm j)) : hit A (nm a) ∨ hit A (nm b) := by
  rcases Bool.or_eq_true_iff.mp h with ha | hb
  · exact splitHit ha hi
  · exact splitHit hb hj

-- Each of the two sides hits a majority of the same three negative rows.
set_option maxRecDepth 20000 in
private theorem separate {i j : Fin 11} (h : i ≠ j) (t : Side × Side)
    (hi : term t (pm i)) (hj : term t (pm j)) : ∃ k, term t (nm k) := by
  have edges := pair_ok i j h
  rcases ht : triple i j with ⟨a,b,c⟩
  rw [ht] at edges
  simp only [Bool.and_eq_true] at edges
  obtain ⟨⟨hab,hbc⟩,hac⟩ := edges
  have L1 := edgeHit hab hi.1 hj.1
  have L2 := edgeHit hbc hi.1 hj.1
  have L3 := edgeHit hac hi.1 hj.1
  have R1 := edgeHit hab hi.2 hj.2
  have R2 := edgeHit hbc hi.2 hj.2
  have R3 := edgeHit hac hi.2 hj.2
  have both : term t (nm a) ∨ term t (nm b) ∨ term t (nm c) := by unfold term; tauto
  rcases both with ha | hb | hc
  · exact ⟨a,ha⟩
  · exact ⟨b,hb⟩
  · exact ⟨c,hc⟩
end PEqualNP.Research.PlaneElevenSeparatedProducts.Core
open PEqualNP.Research.PlaneElevenSeparatedProducts.Core in
theorem PEqualNP.Research.PlaneElevenSeparatedProducts.raw_bound : ∀ (F : Side) (T : Finset (Side × Side)),
  (∀ i : Fin 11, hit F (sig (pos i)) ∨ ∃ t ∈ T, term t (sig (pos i))) →
  (∀ j : Fin 10, ¬hit F (sig (neg j)) ∧ ∀ t ∈ T, ¬term t (sig (neg j))) →
  11 ≤ T.card := by
  intro F T posHits negSafe
  simp only [pos_ok] at posHits
  simp only [neg_ok] at negSafe
  have chooseTerm (i : Fin 11) : ∃ t : T, term t.val (pm i) := by
    rcases posHits i with hf | ⟨t,ht,hp⟩
    · obtain ⟨k,hk,hp⟩ := hf
      obtain ⟨j,hj⟩ := single_ok i k hp
      exact False.elim ((negSafe j).1 ⟨k,hk,hj⟩)
    · exact ⟨⟨t,ht⟩,hp⟩
  choose f hf using chooseTerm
  have hinj : Function.Injective f := by
    intro i j he
    by_contra h
    obtain ⟨k,hk⟩ := separate h (f i).val (hf i) (he ▸ hf j)
    exact (negSafe k).2 (f i).val (f i).property hk
  simpa using Fintype.card_le_of_injective f hinj
open PEqualNP.Research.PlaneElevenSeparatedProducts.Core in
theorem PEqualNP.Research.PlaneElevenSeparatedProducts : ∀ (F : Side) (T : Finset (Side × Side)),
  (∀ i : Fin 11, hit F (pm i) ∨ ∃ t ∈ T, term t (pm i)) →
  (∀ j : Fin 10, ¬hit F (nm j) ∧ ∀ t ∈ T, ¬term t (nm j)) →
  11 ≤ T.card := by
  intro F T hp hn
  apply PEqualNP.Research.PlaneElevenSeparatedProducts.raw_bound F T
  · simpa only [pos_ok] using hp
  · simpa only [neg_ok] using hn
