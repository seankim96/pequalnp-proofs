import PEqualNP.Research.PlaneCase35BudgetComposition
import PEqualNP.Research.PlaneCase35AnyLines
import PEqualNP.Research.PlaneCase35OrCut
import PEqualNP.Research.PlaneCase35FourthWitnessTypes

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget in
theorem PEqualNP.Research.PlaneCase35UniformFourth : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29) (gs : List Gate) (o : Nat),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst ∧ 18 ≤ (!op₃).toNat + (!op₄).toNat + gs.countP (fun g => !g.1) ∧
    29 + op₃.toNat + op₄.toNat ≤ 4 + gs.length :=
  PEqualNP.Research.PlaneCase35BudgetComposition PEqualNP.Research.PlaneCase35AnyLines
    PEqualNP.Research.PlaneCase35FourthWitnessTypes PEqualNP.Research.PlaneCase35OrCut
