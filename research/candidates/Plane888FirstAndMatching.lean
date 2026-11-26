import PEqualNP.Research.Plane888ConflictGraph
import PEqualNP.Research.PlaneMatchingAndBudget

namespace PEqualNP.Research.Plane888FirstAndMatching
open Plane888NineFlags PlaneFirstAndBudget PlaneFirstAndSeparation
private theorem baseGood (p : Fin 52) (a b : Fin 468)
    (cover : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ base, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  rcases List.mem_append.mp hw with raw | constants
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp raw
    have eq := congrArg (fun k : Nat => k.testBit j.val) cover
    simp only [Nat.testBit_and,Nat.testBit_or] at eq
    intro hp
    have yes : (pos p.val).testBit j.val = true := by simpa [input,p.isLt] using hp
    rw [yes,Bool.true_and,Bool.or_eq_true] at eq
    simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using eq
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at constants
    rcases constants with rfl | rfl <;> simp [good]

private theorem readGood {p a b : Nat} {s : List Column} (h : ∀ v ∈ s, good p a b v) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases e : s[j]? with
  | none => simp [good]
  | some v => exact h v (List.mem_of_getElem? e)

private theorem orGood (gs : List (Nat × Nat)) (s : List Column) {p a b : Nat}
    (h : ∀ v ∈ s, good p a b v) : ∀ v ∈ gs.foldl addOr s, good p a b v := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact h v old
    · obtain rfl := List.mem_singleton.mp last
      have hl := readGood h g.1
      have hr := readGood h g.2
      unfold good at *
      simp only [Bool.or_eq_true] at *
      tauto
end PEqualNP.Research.Plane888FirstAndMatching

open PEqualNP.Research.Plane888FirstAndMatching PEqualNP.Research.Plane888ConflictGraph
  PEqualNP.Research.Plane888NineFlags PEqualNP.Research.PlaneMatchingAndBudget
  PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane888FirstAndMatching : ∀ (ors : List (Nat × Nat)) (left right : Nat)
    (tail : List Gate) (out : Nat),
    let s := ors.foldl addOr base
    let l := wire s left
    let r := wire s right
    (257 + (clashes (side l r) mate).card ≤ (side l r).card ∨
     257 + (clashes (side r l) mate).card ≤ (side r l).card) →
    let final := tail.foldl step (s ++ [both l r])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro ors left right tail out
  dsimp only
  intro count hp hn
  apply PEqualNP.Research.PlaneMatchingAndBudget _ _ _ mate tail out _ _ count hp hn
  · intro a b lt ne
    obtain ⟨p,cover⟩ := (PEqualNP.Research.Plane888ConflictGraph.2.2 a b lt).mp ne
    exact ⟨p,orGood ors base (baseGood p a b cover)⟩
  · intro p a b h
    exact ⟨readGood h left,readGood h right⟩
