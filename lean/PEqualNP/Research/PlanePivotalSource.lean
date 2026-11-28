import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlanePivotalSource
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rename (cut src k : Nat) : Nat :=
  if k < cut then k else if k = cut then src else k - 1

def route (cut src : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename cut src)⟩

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

private theorem length_after (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

private theorem read_wire (u t : List Bool) (src k : Nat) (hs : src < u.length) :
    (u ++ (u.getD src false :: t)).getD k false =
    (u ++ t).getD (rename u.length src k) false := by
  by_cases h : k < u.length
  · simp only [rename,h,↓reduceIte,List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)]
    by_cases e : k = u.length
    · subst k
      simp only [rename,Nat.lt_irrefl,↓reduceIte,Nat.sub_self]
      exact (List.getD_append _ _ _ _ hs).symm
    · have h' : u.length ≤ k - 1 := by omega
      simp only [rename,h,e,↓reduceIte,List.getD_append_right _ _ _ _ h']
      rw [show k - u.length = (k-1-u.length)+1 by omega]
      simp [List.getD]

private theorem run (gs : List Gate) (u t : List Bool) (src out : Nat) (hs : src < u.length) :
    (gs.foldl step (u ++ (u.getD src false :: t))).getD out false =
    ((gs.map (route u.length src)).foldl step (u ++ t)).getD (rename u.length src out) false := by
  induction gs generalizing t with
  | nil => exact read_wire u t src out hs
  | cons g gs ih =>
    let w := u ++ (u.getD src false :: t)
    let b := g.op.eval (g.inputs.map fun k => w.getD k false)
    have val : b = (route u.length src g).op.eval
        ((route u.length src g).inputs.map fun k => (u ++ t).getD k false) := by
      simp only [b,w,route,List.map_map,Function.comp_def,read_wire u t src _ hs]
    have a : step w g = u ++ (u.getD src false :: (t ++ [b])) := by simp [step,w,b]
    have d : step (u ++ t) (route u.length src g) = u ++ (t ++ [b]) := by
      simp only [step,List.append_assoc,val]
    change (gs.foldl step (step w g)).getD out false = _
    simp only [List.map_cons,List.foldl_cons]
    rw [a,d]
    exact ih (t ++ [b])

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

private theorem erase_copy :
    ∀ (pre post : List Gate) (n src out : Nat), src < n + pre.length →
      let C : Circuit := ⟨pre ++ (⟨.or,[src]⟩ : Gate) :: post,out⟩
      ∃ D : Circuit, D.size + 1 = C.size ∧ (Monotone2 C → Monotone2 D) ∧
        ∀ r : List Bool, r.length = n → D.eval r = C.eval r := by
  intro pre post n src out hs C
  let cut := n + pre.length
  let D : Circuit := ⟨pre ++ post.map (route cut src),rename cut src out⟩
  refine ⟨D,by simp [D,C,Circuit.size]; omega,?_,?_⟩
  · intro mono g hg
    change g ∈ pre ++ post.map _ at hg
    rcases List.mem_append.mp hg with h | h
    · exact mono g (List.mem_append.mpr (Or.inl h))
    · obtain ⟨orig,ho,rfl⟩ := List.mem_map.mp h
      obtain ⟨op,len⟩ := mono orig (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ho)))
      exact ⟨op,by simpa [route] using len⟩
  · intro r hr
    let u := pre.foldl step r
    have hu : u.length = cut := by simp [u,cut,length_after,hr]
    have h := run post u [] src out (by simpa [hu,cut] using hs)
    simp only [List.append_nil,hu] at h
    change (((pre ++ _).foldl step r).getD _ false) = (((pre ++ _).foldl step r).getD _ false)
    simp only [List.foldl_append,List.foldl_cons]
    change _ = (post.foldl step (step u ⟨.or,[src]⟩)).getD out false
    simpa [step,GateOp.eval,u] using h.symm

private theorem splice (pre post : List Gate) (g : Gate) (out : Nat) (r : List Bool) :
    (Circuit.mk (pre ++ g :: post) out).eval r =
      let w := (Circuit.mk pre out).wires r
      (Circuit.mk post out).eval (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) := by
  change ((pre ++ g :: post).foldl step r).getD out false = _
  rw [List.foldl_append,List.foldl_cons]
  rfl

end PEqualNP.Research.PlanePivotalSource

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PlanePivotalSource in
theorem PEqualNP.Research.PlanePivotalSource :
    ∀ (pre post : List Gate) (g : Gate) (out n : Nat) (P N : List Bool → Prop),
      let C := Circuit.mk (pre ++ g :: post) out
      let separates := fun (D : Circuit) =>
        ∀ r : List Bool, r.length = n → (P r → D.eval r = true) ∧ (N r → D.eval r = false)
      Monotone2 C → separates C →
      (∀ D, Monotone2 D → separates D → C.size ≤ D.size) →
      ∀ src, src < n + pre.length →
      ∃ r : List Bool, r.length = n ∧
        let w := (Circuit.mk pre out).wires r
        let bit := g.op.eval (g.inputs.map fun k => w.getD k false)
        let readout := fun b => (Circuit.mk post out).eval (w ++ [b])
        readout false = false ∧ readout true = true ∧
          ((P r ∧ bit = true ∧ w.getD src false = false) ∨
           (N r ∧ bit = false ∧ w.getD src false = true)) := by
  intro pre post g out n P N C sep mono correct minimal src hs
  let copy : Gate := ⟨.or,[src]⟩
  let B := Circuit.mk (pre ++ copy :: post) out
  obtain ⟨D,size,md,same⟩ := erase_copy pre post n src out hs
  have mb : Monotone2 B := by
    intro h mem
    change h ∈ pre ++ copy :: post at mem
    rcases List.mem_append.mp mem with m | m
    · exact mono h (List.mem_append.mpr (Or.inl m))
    · rcases List.mem_cons.mp m with rfl | m
      · exact ⟨Or.inr rfl,by simp [copy]⟩
      · exact mono h (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ m)))
  by_contra absent
  apply Nat.not_succ_le_self D.size
  have eqsize : C.size = D.size + 1 := by simpa [C,Circuit.size] using size.symm
  change D.size + 1 ≤ D.size
  rw [← eqsize]
  apply minimal D (md mb)
  intro r hr
  let w := (Circuit.mk pre out).wires r
  let bit := g.op.eval (g.inputs.map fun k => w.getD k false)
  let x := w.getD src false
  let readout := fun b => (Circuit.mk post out).eval (w ++ [b])
  have order : readout false = true → readout true = true :=
    later post (w ++ [false]) (w ++ [true]) (by simp)
      (extend rfl (fun _ t => t) (by simp))
      (fun h m => (mono h (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ m)))).1) out
  have orig : C.eval r = readout bit := splice pre post g out r
  have cp : D.eval r = readout x := by
    rw [same r hr,splice]
    simp [readout,x,w,GateOp.eval]
  have good := correct r hr
  rw [orig] at good
  rw [cp]
  have no : ¬(readout false = false ∧ readout true = true ∧
    ((P r ∧ bit = true ∧ x = false) ∨ (N r ∧ bit = false ∧ x = true))) :=
    fun h => absent ⟨r,hr,h⟩
  cases hb : bit <;> cases hx : x <;> cases h0 : readout false <;> cases h1 : readout true <;>
    simp_all
