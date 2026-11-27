import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlaneOneOrGuardClosure.Core
abbrev Column := Nat → Bool
abbrev Gate := Bool × Nat × Nat
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def prod (x y : Column) : Column := fun t => x t && y t
def joinWire (x y : Column) : Column := fun t => x t || y t
def step (s : List Column) (g : Gate) : List Column :=
  let x := wire s g.2.1
  let y := wire s g.2.2
  s ++ [if g.1 then prod x y else joinWire x y]
def cheap (j : Nat) (g : Gate) := g.1 = true ∧ (g.2.1 = j ∨ g.2.2 = j)
def raw (s : List Column) (j : Nat) (w : Column) : Prop :=
  ∃ i : Nat, w = wire s i ∨ w = prod (wire s i) (wire s j)

private theorem prodMask (x g : Column) : prod (prod x g) g = prod x g := by
  funext t
  simp [prod]
private theorem prodComm (x y : Column) : prod x y = prod y x := by
  funext t
  exact Bool.and_comm _ _
private theorem rawMask {s : List Column} {j : Nat} {w : Column} (h : raw s j w) :
    raw s j (prod w (wire s j)) := by
  obtain ⟨i,e|e⟩ := h
  · exact ⟨i,Or.inr (congrArg (fun x => prod x (wire s j)) e)⟩
  · exact ⟨i,Or.inr (by rw [e,prodMask])⟩
private theorem grow (s : List Column) (w : Column) (P : Column → Prop)
    (h : ∀ i, P (wire s i)) (hw : P w) : ∀ i, P (wire (s ++ [w]) i) := by
  intro i
  by_cases eq : i = s.length
  · subst i; simpa [wire] using hw
  by_cases lt : i < s.length
  · simpa only [wire,List.getD_append _ _ _ _ lt] using h i
  · have left := List.getD_eq_default (s++[w]) (fun _ : Nat => false) (show (s++[w]).length ≤ i by simp; omega)
    have right := List.getD_eq_default s (fun _ : Nat => false) (show s.length ≤ i by omega)
    simpa only [wire,left,right] using h i

private theorem run {s : List Column} {j : Nat} (G : Column) (P : Column → Prop)
    (hs : j < s.length) (hg : wire s j = G) (closed : ∀ x, P x → P (prod x G))
    (h : ∀ i, P (wire s i)) (gs : List Gate) (hgates : ∀ g ∈ gs, cheap j g) :
    j < (gs.foldl step s).length ∧ wire (gs.foldl step s) j = G ∧ ∀ i, P (wire (gs.foldl step s) i) := by
  induction gs generalizing s with
  | nil => exact ⟨hs,hg,h⟩
  | cons g gs ih =>
    obtain ⟨op,ij⟩ := hgates g List.mem_cons_self
    have next : j < (step s g).length := by simp [step]; omega
    have keep : wire (step s g) j = G := (List.getD_append _ _ _ _ hs).trans hg
    apply ih next keep
    · apply grow _ _ _ h
      simp only [op, ite_true]
      rcases ij with a|b
      · rw [a,hg,prodComm]; exact closed _ (h _)
      · rw [b,hg]; exact closed _ (h _)
    · exact fun x hx => hgates x (List.mem_cons_of_mem _ hx)
end PEqualNP.Research.PlaneOneOrGuardClosure.Core
open PEqualNP.Research.PlaneOneOrGuardClosure.Core in
theorem PEqualNP.Research.PlaneOneOrGuardClosure : ∀ (s : List Column) (j : Nat), j < s.length →
    ∀ (xs ys : List Gate) (a b : Nat),
    (∀ g ∈ xs, cheap j g) → (∀ g ∈ ys, cheap j g) →
    ∃ x y : Column, raw s j x ∧ raw s j y ∧
      ∀ i : Nat,
        let w := wire (ys.foldl step (step (xs.foldl step s) (false,a,b))) i
        raw s j w ∨ w = joinWire x y ∨ w = prod (joinWire x y) (wire s j) := by
  intro s j hj xs ys a b hx hy
  obtain ⟨len,guard,hr⟩ := run (wire s j) (raw s j) hj rfl (fun _ h => rawMask h)
    (fun i => ⟨i,Or.inl rfl⟩) xs hx
  let t := xs.foldl step s
  let u := joinWire (wire t a) (wire t b)
  let P := fun w => raw s j w ∨ w = u ∨ w = prod u (wire s j)
  refine ⟨wire t a,wire t b,hr a,hr b,?_⟩
  have next : j < (step t (false,a,b)).length := by change j < (t++[u]).length; simp; change j < t.length at len; omega
  have keep : wire (step t (false,a,b)) j = wire s j := (List.getD_append _ _ _ _ len).trans guard
  have h : ∀ i, P (wire (step t (false,a,b)) i) :=
    grow t u P (fun i => Or.inl (hr i)) (Or.inr (Or.inl rfl))
  apply (run (wire s j) P next keep ?_ h ys hy).2.2
  intro w hw
  rcases hw with r|e|e
  · exact Or.inl (rawMask r)
  · exact Or.inr (Or.inr (congrArg (fun z => prod z (wire s j)) e))
  · exact Or.inr (Or.inr (by rw [e,prodMask]))
