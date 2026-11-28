import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlanePureSupportDeletion
open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem shape (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,step]; omega

private theorem keep (gs : List Gate) (w : List Bool) (hw : 0 < w.length) :
    (gs.foldl step w).getD 0 false = w.getD 0 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step])]
    exact List.getD_append _ _ _ _ hw

private def repair (C : Circuit) (n : Nat) : Circuit :=
  ⟨C.gates ++ [⟨.or,[C.output,0]⟩], n+1+C.gates.length⟩

private theorem repaired (C : Circuit) (n : Nat) (r : List Bool)
    (hr : r.length = n) (b : Bool) :
    (repair C n).eval (b :: r) = (C.eval (b :: r) || b) := by
  let w := C.gates.foldl step (b :: r)
  have len : w.length = n+1+C.gates.length := by simp [w,shape,hr]
  have first : w.getD 0 false = b := by simpa [w] using keep C.gates (b :: r) (by simp)
  change ((C.gates ++ [_]).foldl step (b :: r)).getD _ false = _
  rw [List.foldl_append]
  change (w ++ [_]).getD (n+1+C.gates.length) false = _
  rw [← len,List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  rw [Nat.sub_self]
  change [GateOp.or.eval [w.getD C.output false,w.getD 0 false]].getD 0 false =
    (w.getD C.output false || b)
  rw [first]
  simp [GateOp.eval]

end PEqualNP.Research.PlanePureSupportDeletion
open PEqualNP.CircuitLowerBounds PEqualNP.Research.PlanePureSupportDeletion in
theorem PEqualNP.Research.PlanePureSupportDeletion :
  ∀ (n h t : Nat) (P N : List Bool → Prop) (mask : List Bool → Bool),
    (∀ r, r.length = n → N r → mask r = false) →
    let has := fun (budget : Nat) (sel : List Bool → Bool) (pos : List Bool → Prop) =>
      ∃ C : Circuit, (∀ g ∈ C.gates,
        g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        C.size ≤ budget ∧
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false g.op) ≤ h ∧
        ∀ r : List Bool, r.length = n →
          (pos r → C.eval (sel r :: r) = true) ∧ (N r → C.eval (sel r :: r) = false)
    let rest := fun r => P r ∧ mask r = false
    (has t mask P → has t (fun _ => false) rest) ∧
    (has t (fun _ => false) rest → has (t+1) mask P) := by
  intro n h t P N mask safe has rest
  constructor
  · rintro ⟨C,mono,sz,count,ok⟩
    refine ⟨C,mono,sz,count,?_⟩
    intro r hr
    constructor
    · rintro ⟨pos,off⟩
      simpa [off] using (ok r hr).1 pos
    · intro neg
      simpa [safe r hr neg] using (ok r hr).2 neg
  · rintro ⟨C,mono,sz,count,ok⟩
    refine ⟨repair C n,?_,?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with old | new
      · exact mono g old
      · have eq : g = ⟨.or,[C.output,0]⟩ := List.mem_singleton.mp new
        subst g
        simp
    · simpa [repair,Circuit.size] using Nat.add_le_add_right sz 1
    · simpa [repair,List.countP_append] using count
    · intro r hr
      rw [repaired C n r hr]
      constructor
      · intro pos
        cases val : mask r with
        | true => simp
        | false => simpa using (ok r hr).1 ⟨pos,val⟩
      · intro neg
        simp [safe r hr neg,(ok r hr).2 neg]
