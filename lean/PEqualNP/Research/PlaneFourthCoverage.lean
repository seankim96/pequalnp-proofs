import PEqualNP.Research.PlaneFlagOrTail

namespace PEqualNP.Research.PlaneFourthCoverage
open PlaneFlagFourth

def first : BitVec 52 := 0x10100000100f1
def second : BitVec 52 := 0x10001010121f
def groupA : BitVec 52 := 0xa240d46448500
def groupB : BitVec 52 := 0x4caf2a9aa6800
private def choices : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 26, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 19, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 20, 23, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 24, 27, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 28, 31, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 294, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 32, 35, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 324, 0, 0, 0, 1, 0, 0, 0, 0, 0, 29, 0, 36, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 354, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 40, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 384, 0, 0, 0, 13, 0, 0, 0, 0, 0, 37, 0, 45, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 414, 0, 0, 0, 17, 0, 0, 0, 0, 0, 41, 0, 49, 53, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 1, 0, 12, 0, 0, 0, 0, 0, 13, 0, 0, 0, 504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15, 0, 16, 0, 0, 0, 0, 0, 17, 0, 0, 0, 534, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 20, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 564, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 23, 24, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 594, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 27, 28, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 624, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 31, 32, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 654, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 35, 36, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 684, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 39, 40, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 714, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 44, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 744, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 47, 0, 0, 0, 48, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 774, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 804, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def valid (k : Nat) : Bool :=
  let c := choices[k]!
  let x := gate (841+k) []
  if c = 0 then x.1 &&& first == x.1
  else if c = 1 then x.1 &&& second == x.1
  else if c < 54 then
    let e := c-2
    ((groupA ||| groupB).getLsbD e) &&
      (List.finRange 52).all (fun j => j.val == e || !x.1.getLsbD j.val)
  else decide (c-54 < 841) && (x == gate (c-54) [])

set_option maxRecDepth 2000 in
private theorem batch0 : ∀ i : Fin 29, valid (0*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch1 : ∀ i : Fin 29, valid (1*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch2 : ∀ i : Fin 29, valid (2*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch3 : ∀ i : Fin 29, valid (3*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch4 : ∀ i : Fin 29, valid (4*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch5 : ∀ i : Fin 29, valid (5*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch6 : ∀ i : Fin 29, valid (6*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch7 : ∀ i : Fin 29, valid (7*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch8 : ∀ i : Fin 29, valid (8*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch9 : ∀ i : Fin 29, valid (9*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch10 : ∀ i : Fin 29, valid (10*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch11 : ∀ i : Fin 29, valid (11*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch12 : ∀ i : Fin 29, valid (12*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch13 : ∀ i : Fin 29, valid (13*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch14 : ∀ i : Fin 29, valid (14*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch15 : ∀ i : Fin 29, valid (15*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch16 : ∀ i : Fin 29, valid (16*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch17 : ∀ i : Fin 29, valid (17*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch18 : ∀ i : Fin 29, valid (18*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch19 : ∀ i : Fin 29, valid (19*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch20 : ∀ i : Fin 29, valid (20*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch21 : ∀ i : Fin 29, valid (21*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch22 : ∀ i : Fin 29, valid (22*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch23 : ∀ i : Fin 29, valid (23*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch24 : ∀ i : Fin 29, valid (24*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch25 : ∀ i : Fin 29, valid (25*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch26 : ∀ i : Fin 29, valid (26*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch27 : ∀ i : Fin 29, valid (27*29+i.val) = true := by decide +kernel
set_option maxRecDepth 2000 in
private theorem batch28 : ∀ i : Fin 29, valid (28*29+i.val) = true := by decide +kernel
private theorem checked (r : Fin 841) : valid r.val = true := by
  have h (q : Fin 29) : ∀ i : Fin 29, valid (q.val*29+i.val) = true := by
    match q with
    | ⟨0,_⟩ => exact batch0
    | ⟨1,_⟩ => exact batch1
    | ⟨2,_⟩ => exact batch2
    | ⟨3,_⟩ => exact batch3
    | ⟨4,_⟩ => exact batch4
    | ⟨5,_⟩ => exact batch5
    | ⟨6,_⟩ => exact batch6
    | ⟨7,_⟩ => exact batch7
    | ⟨8,_⟩ => exact batch8
    | ⟨9,_⟩ => exact batch9
    | ⟨10,_⟩ => exact batch10
    | ⟨11,_⟩ => exact batch11
    | ⟨12,_⟩ => exact batch12
    | ⟨13,_⟩ => exact batch13
    | ⟨14,_⟩ => exact batch14
    | ⟨15,_⟩ => exact batch15
    | ⟨16,_⟩ => exact batch16
    | ⟨17,_⟩ => exact batch17
    | ⟨18,_⟩ => exact batch18
    | ⟨19,_⟩ => exact batch19
    | ⟨20,_⟩ => exact batch20
    | ⟨21,_⟩ => exact batch21
    | ⟨22,_⟩ => exact batch22
    | ⟨23,_⟩ => exact batch23
    | ⟨24,_⟩ => exact batch24
    | ⟨25,_⟩ => exact batch25
    | ⟨26,_⟩ => exact batch26
    | ⟨27,_⟩ => exact batch27
    | ⟨28,_⟩ => exact batch28
    | ⟨n+29,hn⟩ => omega
  have z := h ⟨r.val/29,by omega⟩ ⟨r.val%29,by omega⟩
  simpa only [show r.val/29*29+r.val%29=r.val by omega] using z

end PEqualNP.Research.PlaneFourthCoverage

open PEqualNP.Research.PlaneFourthCoverage PEqualNP.Research.PlaneFlagFourth in
theorem PEqualNP.Research.PlaneFourthCoverage : ∀ k : Nat, k < 1682 →
    (∃ r : Nat, r < 841 ∧ gate k [] = gate r []) ∨
    (gate k []).1 &&& first = (gate k []).1 ∨
    (gate k []).1 &&& second = (gate k []).1 ∨
    ∃ e : Fin 52, (groupA.getLsbD e.val = true ∨ groupB.getLsbD e.val = true) ∧
      ∀ j : Fin 52, j ≠ e → (gate k []).1.getLsbD j.val = false := by
  intro k hk
  by_cases isOr : k < 841
  · exact Or.inl ⟨k,isOr,rfl⟩
  let r := k-841
  have hr : 841+r = k := by dsimp [r]; omega
  have h := checked ⟨r,by dsimp [r]; omega⟩
  simp only [valid,hr] at h
  let c := choices[r]!
  change (if c = 0 then _ else if c = 1 then _ else if c < 54 then _ else _) = true at h
  split at h
  · exact Or.inr (Or.inl (eq_of_beq h))
  split at h
  · exact Or.inr (Or.inr (Or.inl (eq_of_beq h)))
  split at h
  · rename_i ht
    let e : Fin 52 := ⟨c-2,by omega⟩
    obtain ⟨hg,ha⟩ := Bool.and_eq_true_iff.mp h
    refine Or.inr (Or.inr (Or.inr ⟨e,?_,?_⟩))
    · simpa only [BitVec.getLsbD_or,Bool.or_eq_true] using hg
    · intro j ne
      have diff : j.val ≠ c-2 := fun q => ne (Fin.ext q)
      have hh := List.all_eq_true.mp ha j (by simp)
      change (j.val == c-2 || !(gate k []).1.getLsbD j.val) = true at hh
      simpa [diff] using hh
  · have hh := Bool.and_eq_true_iff.mp h
    exact Or.inl ⟨_,of_decide_eq_true hh.1,eq_of_beq hh.2⟩
