import PEqualNP.Research.Plane888NineFlags

namespace PEqualNP.Research.Plane888ThreeRepresentatives
open Plane888NineFlags PlaneFirstAndSeparation
def operands (k : Fin 3) : List Nat × List Nat :=
  if k.val = 0 then ([2,4,10],[1,14]) else if k.val = 1 then ([14,17],[4,16]) else ([15,17],[4,5])
def granted (ks : List Nat) (p : Nat) : Bool :=
  (ks ++ [26,28,29]).any (fun j => wire base j p)

private theorem flags : ∀ k : Fin 3, ∀ p : Fin 52,
    granted (operands k).1 p.val = true → granted (operands k).2 p.val = true →
    omittedFlags.testBit p.val = true := by decide +kernel
end PEqualNP.Research.Plane888ThreeRepresentatives

open PEqualNP.Research.Plane888ThreeRepresentatives PEqualNP.Research.Plane888NineFlags
  PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane888ThreeRepresentatives : ∀ (k : Fin 3) (ors : List (Nat × Nat)) (left right : Nat) (tail : List Gate) (out : Nat),
    let s := ors.foldl addOr base
    let l := wire s left
    let r := wire s right
    let final := tail.foldl step (s ++ [both l r])
    (∀ p : Fin 52, l p.val = true → granted (operands k).1 p.val = true) →
    (∀ p : Fin 52, r p.val = true → granted (operands k).2 p.val = true) →
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro k ors left right tail out
  dsimp only
  intro hl hr hp hn
  apply PEqualNP.Research.Plane888NineFlags ors left right tail out _ hp hn
  intro p on
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp on
  exact flags k p (hl p a) (hr p b)
