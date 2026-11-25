import PEqualNP.Research.OrderThreePlanePrefixes

/-! The two gates in an independent prefix may trade places. Each
discarded representative has a word in the three plane symmetries
that sends its swapped pair to a retained representative. -/

namespace PEqualNP.Research.OrderThreePlaneSwaps

open OrderThreePlanePrefixData OrderThreePlanePrefixes

abbrev Pair := Nat × Nat

def retained : List Pair := [
  (742, 746), (742, 770), (742, 797), (742, 1), (742, 2), (742, 13),
  (742, 14), (742, 17), (742, 29), (742, 30), (742, 41), (742, 42),
  (742, 44), (742, 53), (742, 58), (742, 62), (742, 68), (742, 70),
  (742, 80), (1, 1106), (1, 1133), (1, 2), (1, 3), (1, 13),
  (1, 14), (1, 15), (1, 17), (1, 57), (1, 59), (1, 67),
  (1, 68), (1, 69), (1, 70), (1, 71), (1, 80), (1, 90),
  (1, 94), (1, 95), (1, 96), (1, 100), (1, 107), (1, 365),
  (1, 366), (1, 377), (1, 393), (1, 395), (1, 404), (1, 421),
  (1, 424), (1, 431), (13, 782), (13, 14), (13, 17), (13, 41),
  (13, 42), (13, 44), (13, 53), (13, 68), (13, 70), (13, 80),
  (14, 782), (14, 15), (14, 42), (14, 44), (14, 53), (14, 99),
  (14, 100), (14, 107)]

private def witnesses : List (Pair × List Nat) := [
  ((1, 742), []), ((1, 746), [2, 1, 0, 1, 2, 0, 0]),
  ((1, 797), [0, 1, 2, 0, 0, 1, 2, 0]), ((1, 798), [2, 0, 1, 0, 1, 1, 2, 1]),
  ((1, 823), [2, 0, 1, 2, 0, 0, 0]), ((1, 825), [1, 2, 0, 0, 1, 2, 0]),
  ((1, 58), [1, 1, 2, 1, 2, 1, 0, 0]), ((1, 396), [2, 0, 1]),
  ((13, 742), []), ((13, 746), [0, 1, 2, 1, 0, 0, 0, 2]),
  ((13, 770), [2, 0]), ((13, 797), [1, 2, 0, 0, 1, 1]),
  ((13, 1), []), ((13, 2), [0, 0, 1, 2, 0, 1, 0, 2]),
  ((13, 29), [0, 1, 2, 0, 0, 1, 2, 0]), ((13, 30), [1, 0, 0, 0, 1, 1, 0, 0]),
  ((13, 58), [1, 1, 2, 1, 2, 1, 0, 0]), ((13, 62), [0, 0, 1, 0, 1, 1, 0, 1, 0]),
  ((14, 742), []), ((14, 769), [0, 1, 2, 0, 0, 2]),
  ((14, 774), [0, 0, 1, 0, 1, 0, 0, 2]), ((14, 825), [2, 1, 1, 0, 0, 0]),
  ((14, 1), []), ((14, 3), [0, 0, 1, 2, 1, 2, 1, 0, 1, 0]),
  ((14, 13), []), ((14, 29), [0, 1, 2, 0, 0, 1, 2, 0]),
  ((14, 30), [1, 1, 0, 1, 2, 0, 0, 2, 1]), ((14, 32), [0, 1, 2, 0, 0, 0, 1, 2, 0, 0]),
  ((14, 40), [0, 1, 2, 0, 0, 2]), ((14, 45), [0, 0, 1, 0, 1, 0, 0, 2]),
  ((14, 86), [0, 0, 0, 0, 1, 2, 0, 1, 2, 1, 1]), ((14, 90), [0, 0, 0, 1, 1, 0, 0]),
  ((14, 96), [2, 1, 1, 0, 0, 0])]

def rawPair (g : Nat) : Bool := left g < 26 && right g < 26

def stepPair (v : Pair) (k : Nat) : Pair :=
  match stage0.permutations[k]? with
  | some p => (move p v.1,move p v.2)
  | none => v

def word (a : Pair) (ks : List Nat) := ks.foldl stepPair a

def validWitness (w : Pair × List Nat) : Bool :=
  rawPair w.1.1 && rawPair w.1.2 && w.2.all (fun k => k < 3) &&
    retained.contains (word (w.1.2,w.1.1) w.2)

def beforeSwap : List Pair := ([1,2,3,4] : List (Fin 5)).flatMap fun i =>
  (table i).representatives.toList.map (fun g => ((initial i).getD 0,g))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem verify : (witnesses.all validWitness = true) ∧
    (beforeSwap.all (fun x => retained.contains x || witnesses.any (fun w => w.1 == x))) = true := by
  decide +kernel

theorem swap_coverage (a : Pair) (h : a ∈ beforeSwap) :
    a ∈ retained ∨ rawPair a.1 = true ∧ rawPair a.2 = true ∧
      ∃ ks : List Nat, (∀ k ∈ ks, k < 3) ∧ word (a.2,a.1) ks ∈ retained := by
  have cover := List.all_eq_true.mp verify.2 a h
  rcases Bool.or_eq_true_iff.mp cover with keep|other
  · exact Or.inl (List.contains_iff_mem.mp keep)
  · obtain ⟨⟨w,ks⟩,mem,eq⟩ := List.any_eq_true.mp other
    have same : w = a := beq_iff_eq.mp eq
    subst w
    have v := List.all_eq_true.mp verify.1 (a,ks) mem
    simp only [validWitness,Bool.and_eq_true,List.contains_iff_mem,List.all_eq_true,decide_eq_true_eq] at v
    exact Or.inr ⟨v.1.1.1,v.1.1.2,ks,v.1.2,v.2⟩

theorem count_representatives :
    retained.length = 68 ∧ retained.Nodup ∧
    (retained.filter (fun a => !rawPair a.2)).length = 15 ∧ beforeSwap.length = 101 := by
  decide +kernel

end PEqualNP.Research.OrderThreePlaneSwaps
