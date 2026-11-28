import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD

namespace PEqualNP.Research.PlaneDeleteCopy
open PEqualNP.CircuitLowerBounds

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

end PEqualNP.Research.PlaneDeleteCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PlaneDeleteCopy in
theorem PEqualNP.Research.PlaneDeleteCopy :
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
