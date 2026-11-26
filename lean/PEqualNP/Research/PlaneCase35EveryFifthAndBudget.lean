import PEqualNP.Research.PlaneCase35FifthComposition
import PEqualNP.Research.PlaneCase35FifthGuard
import PEqualNP.Research.PlaneCase35SecondFamily
import PEqualNP.Research.PlaneCase35FifthTransport

namespace PEqualNP.Research.PlaneCase35EveryFifthAndBudget
open PlaneFirstAndSeparation PlaneFirstAndBudget PlaneCase35FourthOrBudget PlaneCase35FifthGuard
private theorem toJoin (x y : Nat) : x &&& y = x ↔ x ||| y = y := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
    have e := congrArg (fun v : Nat => v.testBit k) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and] at e ⊢ <;>
    cases ex : x.testBit k <;> cases ey : y.testBit k <;> simp_all
private theorem first : PlaneCase35FifthTransport.W 66559 := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j lt
  obtain ⟨p,h,cov⟩ := pairGuard i j lt
  exact ⟨p,h,(toJoin _ _).mp cov⟩
private theorem second : PlaneCase35FifthTransport.W 1030807945728 := by
  obtain ⟨f,h⟩ := PEqualNP.Research.PlaneCase35SecondFamily
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,h,cov⟩ := h i j lt
  exact ⟨p,h,(toJoin _ _).mp cov⟩
private theorem single : PlaneCase35FifthComposition.Single := by
  intro u
  obtain ⟨f,h⟩ := PEqualNP.Research.PlaneCase35FifthTransport first second u
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,h1,h2,h3,h4⟩ := h i j lt
  exact ⟨p,⟨h1,h2,(toJoin _ _).mpr h4⟩,h3⟩
private theorem seedOff : ∀ p : Fin 52, omittedFlags.testBit p.val = false →
    p.val ≠ 9 ∧ p.val ≠ 16 ∧ p.val ≠ 0 ∧ p.val ≠ 1 ∧ p.val ≠ 2 ∧ p.val ≠ 3 := by decide +kernel
private theorem four : PlaneCase35FifthComposition.Four := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j lt
  obtain ⟨p,off,cov⟩ := pairGuard i j lt
  obtain ⟨h9,h16,h0,h1,h2,h3⟩ := seedOff p off
  exact ⟨p,⟨h9,h16,cov⟩,by omega⟩
end PEqualNP.Research.PlaneCase35EveryFifthAndBudget
open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35FifthGuard
  PEqualNP.Research.PlaneCase35EveryFifthAndBudget in
theorem PEqualNP.Research.PlaneCase35EveryFifthAndBudget : ∀ (op : Bool) (a b : Fin 30) (gs : List Gate) (o : Nat),
    let e := mix op (base a) (base b)
    let pool := (initial ++ [c,d,e]) ++ [fun _ => false, fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  exact PEqualNP.Research.PlaneCase35FifthComposition single four
