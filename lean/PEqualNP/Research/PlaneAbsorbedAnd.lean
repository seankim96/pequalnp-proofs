import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlaneAbsorbedAnd
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def rises (u v : List Bool) :=
  ∀ i, u.getD i false = true → v.getD i false = true

private theorem extend {u v : List Bool} {x y : Bool} (len : u.length = v.length)
    (h : rises u v) (xy : x = true → y = true) : rises (u ++ [x]) (v ++ [y]) := by
  intro k
  by_cases hk : k < u.length
  · simpa only [List.getD_append _ _ _ _ hk,List.getD_append _ _ _ _ (len ▸ hk)] using h k
  · have hn := Nat.le_of_not_gt hk
    rw [List.getD_append_right _ _ _ _ hn,List.getD_append_right _ _ _ _ (len ▸ hn),← len]
    cases k-u.length with
    | zero => exact xy
    | succ n => simp [List.getD]

private theorem later (gs : List Gate) (u v : List Bool) (len : u.length = v.length)
    (h : rises u v) (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    rises (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step u g) (step v g) (by simp [step,len]) _ (fun t ht => mono t (by simp [ht]))
    apply extend len h
    rcases mono g (by simp) with op | op
    · simp only [op,GateOp.eval,List.all_eq_true,List.mem_map]
      intro all b hb
      obtain ⟨k,hk,rfl⟩ := hb
      exact h k (all _ ⟨k,hk,rfl⟩)
    · simp only [op,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨b,⟨k,hk,rfl⟩,hb⟩
      exact ⟨_,⟨k,hk,rfl⟩,h k hb⟩

private theorem at_and (pre post : List Gate) (i j out : Nat) (r : List Bool) :
    (Circuit.mk (pre ++ (⟨.and,[i,j]⟩ : Gate) :: post) out).eval r =
      let w := pre.foldl step r
      (post.foldl step (w ++ [w.getD i false && w.getD j false])).getD out false := by
  change ((pre ++ _ :: post).foldl step r).getD out false = _
  rw [List.foldl_append,List.foldl_cons]
  congr 2
  simp [step,GateOp.eval]

private theorem at_copy (pre post : List Gate) (i out : Nat) (r : List Bool) :
    (Circuit.mk (pre ++ (⟨.or,[i]⟩ : Gate) :: post) out).eval r =
      let w := pre.foldl step r
      (post.foldl step (w ++ [w.getD i false])).getD out false := by
  change ((pre ++ _ :: post).foldl step r).getD out false = _
  rw [List.foldl_append,List.foldl_cons]
  congr 2
  simp [step,GateOp.eval]

end PEqualNP.Research.PlaneAbsorbedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PlaneAbsorbedAnd in
theorem PEqualNP.Research.PlaneAbsorbedAnd :
    ∀ (pre post : List Gate) (i j out : Nat) (P N : List Bool → Prop),
      let C : Circuit := ⟨pre ++ (⟨.and,[i,j]⟩ : Gate) :: post,out⟩
      let D : Circuit := ⟨pre ++ (⟨.or,[i]⟩ : Gate) :: post,out⟩
      Monotone2 C →
      (∀ r, N r → ((Circuit.mk pre out).wires r).getD i false = true →
        ((Circuit.mk pre out).wires r).getD j false = true) →
      (∀ r, P r → C.eval r = true) → (∀ r, N r → C.eval r = false) →
      Monotone2 D ∧ D.size = C.size ∧ (∀ r, P r → D.eval r = true) ∧
        (∀ r, N r → D.eval r = false) := by
  intro pre post i j out P N C D mono absorb pos neg
  have suffix (g : Gate) (hg : g ∈ post) : g.op = .and ∨ g.op = .or :=
    (mono g (by simp [C,hg])).1
  refine ⟨?_,by simp [C,D,Circuit.size],?_,?_⟩
  · intro g hg
    change g ∈ pre ++ _ :: post at hg
    rcases List.mem_append.mp hg with a | a
    · exact mono g (List.mem_append.mpr (Or.inl a))
    · rcases List.mem_cons.mp a with rfl | a
      · exact ⟨Or.inr rfl,by simp⟩
      · exact mono g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ a)))
  · intro r hr
    let w := pre.foldl step r
    have h := later post (w ++ [w.getD i false && w.getD j false]) (w ++ [w.getD i false]) (by simp)
      (extend rfl (fun _ t => t) (fun t => (Bool.and_eq_true_iff.mp t).1)) suffix
    rw [show D.eval r = _ from at_copy pre post i out r]
    exact h out ((at_and pre post i j out r) ▸ pos r hr)
  · intro r hr
    let w := pre.foldl step r
    have eq : (w.getD i false && w.getD j false) = w.getD i false := by
      cases hi : w.getD i false with
      | false => rfl
      | true => rw [show w.getD j false = true from absorb r hr hi]; rfl
    have h := neg r hr
    rw [show C.eval r = _ from at_and pre post i j out r] at h
    rw [show D.eval r = _ from at_copy pre post i out r]
    change (post.foldl step (w ++ [_])).getD out false = false at h ⊢
    rw [eq] at h
    exact h
