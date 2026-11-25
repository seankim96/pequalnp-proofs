import PEqualNP.Research.PlaneFlagFourth

namespace PEqualNP.Research.PlaneFlagAndTail
open OrderThreePlanePrefixData PlaneFlagFourth

def blocked (a : Signature) : Bool := a.1 != -1 || a.2.getLsbD 0

def meetCols (a b : Signature) : Signature := (a.1 &&& b.1, a.2 &&& b.2)
def start (k : Nat) : List Signature := (List.ofFn (fun i : Fin 29 => col i.val)) ++ [gate k [],(0,0),(-1,-1)]
def step (s : List Signature) (g : Nat × Nat) : List Signature :=
  s ++ [meetCols (s.getD g.1 (0,0)) (s.getD g.2 (0,0))]

private theorem preserve (a : Signature) (h : blocked a = true)
    (b : Signature) (j : blocked b = true) : blocked (meetCols a b) = true := by
  by_cases hn : (a.1 &&& b.1) = -1
  · have hh : a.1 = -1 ∧ b.1 = -1 := BitVec.and_eq_allOnes_iff.mp hn
    have ha : a.2.getLsbD 0 = true := by simpa [blocked,hh.1] using h
    have hb : b.2.getLsbD 0 = true := by simpa [blocked,hh.2] using j
    simp [blocked,meetCols,ha,hb]
  · exact Bool.or_eq_true_iff.mpr (Or.inl (bne_iff_ne.mpr hn))

private theorem readSafe {s : List Signature} (h : ∀ v ∈ s, blocked v = true)
    (i : Nat) : blocked (s.getD i (0,0)) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases e : s[i]? with
  | none => decide +kernel
  | some a => exact h a (List.mem_of_getElem? e)

private theorem runSafe (gs : List (Nat × Nat)) (s : List Signature)
    (h : ∀ v ∈ s, blocked v = true) : ∀ v ∈ gs.foldl step s, blocked v = true := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with old | new
    · exact h v old
    · have e := List.mem_singleton.mp new
      subst v
      exact preserve _ (readSafe h g.1) _ (readSafe h g.2)

private theorem rawOK : ∀ i : Fin 29, blocked (col i.val) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem newOK : ∀ i : Fin 58, ∀ j : Fin 29,
    blocked (gate (i.val*29+j.val) []) = true := by decide +kernel

theorem obstruction (k : Nat) (hk : k < 1682) (gs : List (Nat × Nat)) (i : Nat) :
    ((gs.foldl step (start k)).getD i (0,0)) ≠ (-1,0) := by
  have h := newOK ⟨k/29,by omega⟩ ⟨k%29,by omega⟩
  dsimp only at h
  rw [show k/29*29 + k%29 = k by omega] at h
  have req : ∀ v ∈ start k, blocked v = true := by
    intro v hv
    rcases List.mem_append.mp hv with old | extra
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp old
      exact rawOK j
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at extra
      rcases extra with rfl|rfl|rfl
      · exact h
      · decide +kernel
      · decide +kernel
  intro eq
  have z := readSafe (runSafe gs _ req) i
  rw [eq] at z
  contradiction
end PEqualNP.Research.PlaneFlagAndTail

open PEqualNP.Research.PlaneFlagAndTail in
theorem PEqualNP.Research.PlaneFlagAndTail : ∀ k : Nat, k < 1682 → ∀ gs : List (Nat × Nat), ∀ i : Nat,
    ((gs.foldl step (start k)).getD i (0,0)) ≠ (-1,0) := obstruction
