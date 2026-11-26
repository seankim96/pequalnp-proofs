import PEqualNP.Research.PlaneCase35EightFlags
import PEqualNP.Research.PlaneCase35OrCut

namespace PEqualNP.Research.PlaneCase35GuardedPair
open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35EightFlags

def rule (op : Bool) (x y : Column) : Prop :=
  op = false ∨ x = y ∨ ∀ p : Fin 52, 8 ≤ p.val → (x p.val && y p.val) = false

open PEqualNP.Research.PlaneFirstAndBudget in
private theorem count_types (gs : List Gate) : gs.countP Prod.fst + gs.countP (fun g => !g.1) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g tail ih => cases h : g.1 <;> simp [h] <;> omega

private def inherits (w : Column) : Prop :=
  ∀ p : Fin 52, 8 ≤ p.val → w p.val = true →
    ∃ v ∈ initial, v p.val = true ∧ ∀ n : Fin 468, v (52+n.val) = true → w (52+n.val) = true

private theorem raw (k : Fin 28) : inherits (input k.val) := by
  intro p _ on
  exact ⟨_, List.mem_ofFn.mpr ⟨k,rfl⟩,on,fun _ h => h⟩

private theorem combine (op : Bool) {x y : Column} (hx : inherits x) (hy : inherits y)
    (h : rule op x y) : inherits (mix op x y) := by
  cases op with
  | false =>
    intro p low on
    change (x p.val || y p.val) = true at on
    rw [Bool.or_eq_true] at on
    rcases on with left | right
    · obtain ⟨v,hv,hit,down⟩ := hx p low left
      exact ⟨v,hv,hit,fun n hn => by simp [mix, down n hn]⟩
    · obtain ⟨v,hv,hit,down⟩ := hy p low right
      exact ⟨v,hv,hit,fun n hn => by simp [mix, down n hn]⟩
  | true =>
    rcases h with bad | eq | off
    · contradiction
    · subst y
      have same : mix true x x = x := by funext n; simp [mix]
      rwa [same]
    · intro p low on
      change (x p.val && y p.val) = true at on
      rw [off p low] at on
      contradiction

private theorem readSource {c : Column} (hc : inherits c) (i : Fin 29) : inherits (source c i) := by
  by_cases h : i.val < 28
  · simpa [source,h] using raw ⟨i.val,h⟩
  · simpa [source,h] using hc
end PEqualNP.Research.PlaneCase35GuardedPair

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35GuardedPair in
theorem PEqualNP.Research.PlaneCase35GuardedPair : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29) (gs : List Gate) (o : Nat),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    rule op₃ (input l.val) (input r.val) →
    rule op₄ (source c a) (source c b) →
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst ∧ 18 ≤ (!op₃).toNat + (!op₄).toNat + gs.countP (fun g => !g.1) ∧
    29 + op₃.toNat + op₄.toNat ≤ 4 + gs.length := by
  intro op₃ op₄ l r a b gs o c d pool h₃ h₄ hp hn
  have hc := combine op₃ (raw l) (raw r) h₃
  have hd := combine op₄ (readSource hc a) (readSource hc b) h₄
  have hor := PEqualNP.Research.PlaneCase35OrCut op₃ op₄ l r a b gs o hp hn
  have hand : 9 ≤ gs.countP Prod.fst := by
    apply PEqualNP.Research.PlaneCase35EightFlags [c,d] gs o _ _ _
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact hc
      · exact hd
    · simpa [pool,PEqualNP.Research.PlaneCase35EightFlags.initial,List.append_assoc] using hp
    · simpa [pool,PEqualNP.Research.PlaneCase35EightFlags.initial,List.append_assoc] using hn
  refine ⟨hand,hor,?_⟩
  have count := count_types gs
  cases op₃ <;> cases op₄ <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] at * <;> omega
