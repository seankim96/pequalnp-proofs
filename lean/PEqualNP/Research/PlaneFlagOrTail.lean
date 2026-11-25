import PEqualNP.Research.PlaneFlagFourth

namespace PEqualNP.Research.PlaneFlagOrTail
open OrderThreePlanePrefixData PlaneFlagFourth

def blocked (p : Nat) (a : Signature) : Bool :=
  !a.1.getLsbD p || a.2 != 0

def joinCols (a b : Signature) : Signature := (a.1 ||| b.1, a.2 ||| b.2)
def start (k : Nat) : List Signature := (List.ofFn (fun i : Fin 29 => col i.val)) ++ [gate k [],(0,0),(-1,-1)]
def step (s : List Signature) (g : Nat × Nat) : List Signature :=
  s ++ [joinCols (s.getD g.1 (0,0)) (s.getD g.2 (0,0))]

private theorem preserve (p : Nat) (a : Signature) (h : blocked p a = true)
    (b : Signature) (j : blocked p b = true) : blocked p (joinCols a b) = true := by
  by_cases hn : (a.2 ||| b.2) = 0
  · obtain ⟨ha,hb⟩ := BitVec.or_eq_zero_iff.mp hn
    simpa [blocked,joinCols,ha,hb] using And.intro (show a.1.getLsbD p = false by simpa [blocked,ha] using h) (show b.1.getLsbD p = false by simpa [blocked,hb] using j)
  · exact Bool.or_eq_true_iff.mpr (Or.inr (bne_iff_ne.mpr hn))

private theorem readSafe {p : Nat} {s : List Signature} (h : ∀ v ∈ s, blocked p v = true)
    (i : Nat) : blocked p (s.getD i (0,0)) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => simp [blocked]
  | some a => exact h a (List.mem_of_getElem? e)

private theorem runSafe (p : Nat) (gs : List (Nat × Nat)) (s : List Signature)
    (h : ∀ v ∈ s, blocked p v = true) : ∀ v ∈ gs.foldl step s, blocked p v = true := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with old | new
    · exact h v old
    · have e := List.mem_singleton.mp new
      subst v
      exact preserve p _ (readSafe h g.1) _ (readSafe h g.2)

private theorem rawOK (i : Fin 29) : blocked 8 (col i.val) = true ∧ blocked 13 (col i.val) = true := by
  revert i
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem newOK : ∀ i : Fin 58, ∀ j : Fin 29,
    (blocked 8 (gate (i.val*29+j.val) []) || blocked 13 (gate (i.val*29+j.val) [])) = true := by decide +kernel

theorem obstruction (k : Nat) (hk : k < 1682) (gs : List (Nat × Nat)) (i : Nat) :
    ((gs.foldl step (start k)).getD i (0,0)) ≠ (-1,0) := by
  have h := newOK ⟨k/29,by omega⟩ ⟨k%29,by omega⟩
  dsimp only at h
  rw [show k/29*29 + k%29 = k by omega] at h
  have req (p : Nat) (hp : p = 8 ∨ p = 13) (hf : blocked p (gate k []) = true) : ∀ v ∈ start k, blocked p v = true := by
    intro v hv
    rcases List.mem_append.mp hv with old | extra
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp old
      rcases hp with rfl|rfl
      · exact (rawOK j).1
      · exact (rawOK j).2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at extra
      rcases extra with rfl|rfl|rfl
      · exact hf
      · simp [blocked]
      · simp [blocked]
  intro eq
  rcases Bool.or_eq_true_iff.mp h with a|b
  · have z := readSafe (runSafe 8 gs _ (req 8 (Or.inl rfl) a)) i
    rw [eq] at z
    contradiction
  · have z := readSafe (runSafe 13 gs _ (req 13 (Or.inr rfl) b)) i
    rw [eq] at z
    contradiction
end PEqualNP.Research.PlaneFlagOrTail

open PEqualNP.Research.PlaneFlagOrTail in
theorem PEqualNP.Research.PlaneFlagOrTail : ∀ k : Nat, k < 1682 → ∀ gs : List (Nat × Nat), ∀ i : Nat,
    ((gs.foldl step (start k)).getD i (0,0)) ≠ (-1,0) := obstruction
