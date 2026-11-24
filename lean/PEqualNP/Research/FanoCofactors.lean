import PEqualNP.Research.FanoCanonicalCircuit

/-! In the incidence graph of the Fano plane, fixing two input bits either
forces an already present edge, or leaves every remaining bit essential.
Three fixed zeros can extinguish a variable, so the threshold is sharp. -/

namespace PEqualNP.Research.FanoCofactors

open PEqualNP.Research.FanoCanonicalCircuit
abbrev V := Fin 14

def adj (a b : V) : Bool :=
  flags.contains (a,b) || flags.contains (b,a)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem candidates : ∀ v j k : V, v ≠ j → v ≠ k → ∀ b c : Bool, ∃ w : V,
    adj v w = true ∧ (if b then adj j w = false else w ≠ j) ∧
      (if c then adj k w = false else w ≠ k) := by
  decide +kernel

def baseRow (j k w : V) (b c : Bool) : Input := fun i =>
  decide (i = w) || (b && decide (i = j)) || (c && decide (i = k))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem base_value : ∀ j k w : V, ∀ b c : Bool,
    target (baseRow j k w b c) =
      ((b && c && adj j k) || (b && adj j w) || (c && adj k w)) := by
  decide +kernel

private theorem no_loops : ∀ v : V, adj v v = false := by decide +kernel

private theorem edge_on (x : Input) (u v : V) (edge : adj u v = true)
    (hu : x u = true) (hv : x v = true) : target x = true := by
  apply List.any_eq_true.mpr
  rcases Bool.or_eq_true_iff.mp edge with dir|rev
  · exact ⟨(u,v),List.contains_iff_mem.mp dir,by simp [hu,hv]⟩
  · exact ⟨(v,u),List.contains_iff_mem.mp rev,by simp [hu,hv]⟩

/-- The variable v remains essential under two fixed coordinates j and k
unless those coordinates already contain an edge. -/
theorem sensitive_after_two (v j k : V) (vj : v ≠ j) (vk : v ≠ k) (jk : j ≠ k)
    (b c : Bool) (independent : (b && c && adj j k) = false) :
    ∃ x y : Input, x j = b ∧ y j = b ∧ x k = c ∧ y k = c ∧
      x v = false ∧ y v = true ∧ (∀ i ≠ v, x i = y i) ∧
      target x = false ∧ target y = true := by
  obtain ⟨w,vw,avoidJ,avoidK⟩ := candidates v j k vj vk b c
  have vwNe : v ≠ w := by
    rintro rfl
    simp [no_loops] at vw
  let x := baseRow j k w b c
  let y := Function.update x v true
  have xj : x j = b := by
    cases b with
    | false =>
      have ne : w ≠ j := avoidJ
      simp [x,baseRow,Ne.symm ne,jk]
    | true => simp [x,baseRow]
  have xk : x k = c := by
    cases c with
    | false =>
      have ne : w ≠ k := avoidK
      simp [x,baseRow,Ne.symm ne,Ne.symm jk]
    | true => simp [x,baseRow]
  have xv : x v = false := by simp [x,baseRow,vj,vk,vwNe]
  have xw : x w = true := by simp [x,baseRow]
  have neg : target x = false := by
    rw [show x = baseRow j k w b c from rfl,base_value,independent]
    cases b <;> cases c <;> simp_all
  have pos : target y = true := edge_on y v w vw
    (by simp [y]) (by simpa [y,Function.update_of_ne (Ne.symm vwNe)] using xw)
  exact ⟨x,y,xj,by simpa only [y,Function.update_of_ne (Ne.symm vj)] using xj,
    xk,by simpa only [y,Function.update_of_ne (Ne.symm vk)] using xk,
    xv,by simp [y],fun i hi => by simp [y,Function.update_of_ne hi],neg,pos⟩

theorem three_zeros_can_hide_a_variable (x : Input)
    (h7 : x 7 = false) (h8 : x 8 = false) (h10 : x 10 = false) :
    target (Function.update x 0 true) = target (Function.update x 0 false) := by
  simp [target,flags,Function.update,h7,h8,h10]

end PEqualNP.Research.FanoCofactors
