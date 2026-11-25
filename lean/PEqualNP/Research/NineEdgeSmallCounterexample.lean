import PEqualNP.Defs.CircuitLowerBounds

import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Research.NineEdgeSmallCounterexample

open PEqualNP.CircuitLowerBounds

abbrev Block := Nat × Nat

def edges : List (Nat × Nat) :=
  [(0,4),(1,5),(0,6),(2,6),(3,6),(0,7),(2,7),(4,7),(6,7)]

def circuit : Circuit := ⟨[
  ⟨.and,[1,5]⟩, ⟨.or,[2,3]⟩, ⟨.and,[9,6]⟩,
  ⟨.or,[0,2]⟩, ⟨.and,[11,7]⟩, ⟨.or,[4,6]⟩,
  ⟨.or,[0,7]⟩, ⟨.and,[13,14]⟩, ⟨.or,[8,10]⟩,
  ⟨.or,[12,15]⟩, ⟨.or,[16,17]⟩],18⟩

def target (x : List Bool) := edges.any fun e => x.getD e.1 false && x.getD e.2 false

theorem witness : circuit.size = 11 ∧
    (∀ g ∈ circuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = target (List.ofFn x) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp [circuit] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · intro x
    have hx : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := rfl
    rw [hx]
    exact (by decide +kernel : ∀ a b c d e f g h : Bool,
      circuit.eval [a,b,c,d,e,f,g,h] = target [a,b,c,d,e,f,g,h])
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Research.NineEdgeSmallCounterexample

open PEqualNP.Research.NineEdgeSmallCounterexample in
private theorem nineEdgeBridge (xs : List Bool) : target xs = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, xs.getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ xs.getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  change target xs = decide (∃ i < 9, _)
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (edges.any _ = true) ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hot⟩
    simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨0, by decide, by change xs.getD 0 false = true ∧ xs.getD 4 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨1, by decide, by change xs.getD 1 false = true ∧ xs.getD 5 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨2, by decide, by change xs.getD 0 false = true ∧ xs.getD 6 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨3, by decide, by change xs.getD 2 false = true ∧ xs.getD 6 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨4, by decide, by change xs.getD 3 false = true ∧ xs.getD 6 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨5, by decide, by change xs.getD 0 false = true ∧ xs.getD 7 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨6, by decide, by change xs.getD 2 false = true ∧ xs.getD 7 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨7, by decide, by change xs.getD 4 false = true ∧ xs.getD 7 false = true; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨8, by decide, by change xs.getD 6 false = true ∧ xs.getD 7 false = true; simpa only [Bool.and_eq_true] using hot⟩
  · rintro ⟨i, hi, hot⟩
    interval_cases i
    · exact ⟨(0,4), by decide, by change xs.getD 0 false = true ∧ xs.getD 4 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(1,5), by decide, by change xs.getD 1 false = true ∧ xs.getD 5 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(0,6), by decide, by change xs.getD 0 false = true ∧ xs.getD 6 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(2,6), by decide, by change xs.getD 2 false = true ∧ xs.getD 6 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(3,6), by decide, by change xs.getD 3 false = true ∧ xs.getD 6 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(0,7), by decide, by change xs.getD 0 false = true ∧ xs.getD 7 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(2,7), by decide, by change xs.getD 2 false = true ∧ xs.getD 7 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(4,7), by decide, by change xs.getD 4 false = true ∧ xs.getD 7 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩
    · exact ⟨(6,7), by decide, by change xs.getD 6 false = true ∧ xs.getD 7 false = true at hot; simpa only [Bool.and_eq_true] using hot⟩


open PEqualNP.Research.NineEdgeSmallCounterexample in
theorem PEqualNP.Research.NineEdgeSmallCounterexample : (¬ (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))) → ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), gates.length ≤ 10 ∧ (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro neg
  by_contra noSmall
  apply neg
  intro gates o basis one ev
  have enough : 11 ≤ gates.length := by
    by_contra! small
    exact noSmall ⟨gates, o, by omega, basis, one, ev⟩
  refine ⟨circuit.gates, circuit.output, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, hlen⟩ := witness.2.1 g hg
    exact ⟨hop, hlen.le⟩
  · exact witness.1.le.trans enough
  · intro x
    exact (witness.2.2 x).trans (nineEdgeBridge _)
