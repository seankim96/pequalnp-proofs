import PEqualNP.Research.PlaneCase35GuardedPair

namespace PEqualNP.Research.PlaneCase35LineAnd
open PEqualNP.Research.PlaneCase35FourthOrBudget
theorem off : ∀ (p : Fin 52) (u : Fin 2), 8 ≤ p.val → input (13+u.val) p.val = false := by decide +kernel
end PEqualNP.Research.PlaneCase35LineAnd

open PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35FourthOrBudget in
theorem PEqualNP.Research.PlaneCase35LineAnd : ∀ (u v : Fin 2) (r : Fin 28) (b : Fin 29) (gs : List Gate) (o : Nat),
    let l : Fin 28 := ⟨13+u.val,by omega⟩
    let a : Fin 29 := ⟨13+v.val,by omega⟩
    let c := mix true (input l.val) (input r.val)
    let d := mix true (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst ∧ 18 ≤ gs.countP (fun g => !g.1) ∧ 31 ≤ 4 + gs.length := by
  intro u v r b gs o l a c d pool hp hn
  have h₃ : PEqualNP.Research.PlaneCase35GuardedPair.rule true (input l.val) (input r.val) := by
    right; right
    intro p low
    simp [l,PEqualNP.Research.PlaneCase35LineAnd.off p u low]
  have h₄ : PEqualNP.Research.PlaneCase35GuardedPair.rule true (source c a) (source c b) := by
    right; right
    intro p low
    have hv : a.val < 28 := by dsimp [a]; omega
    simp [source,hv,a,PEqualNP.Research.PlaneCase35LineAnd.off p v low]
  simpa using PEqualNP.Research.PlaneCase35GuardedPair true true l r a b gs o h₃ h₄ hp hn
