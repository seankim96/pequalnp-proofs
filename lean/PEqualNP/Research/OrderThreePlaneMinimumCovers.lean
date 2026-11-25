import PEqualNP.Research.OrderThreePlaneStarCenters

/-! Classification of all proper mixed star covers attaining the 16-center bound.
Pairs encode the omitted points and the selected lines, in that order. -/

namespace PEqualNP.Research.OrderThreePlaneMinimumCovers

open OrderThreePlaneStarCenters

private def oneBit (i : Vertex) : Mask := (1 : Mask) <<< i.val

/-- Points incident with line i have offsets 0, 1, 3 and 9 from i. -/
def pointsOn (i : Vertex) : Mask :=
  let x := oneBit i
  x ||| x.rotateLeft 1 ||| x.rotateLeft 3 ||| x.rotateLeft 9

def minimumCovers : List (Mask × Mask) :=
  (List.finRange 13).map (fun i => (oneBit i, mandatory (oneBit i))) ++
  (List.finRange 13).map (fun i => (~~~(pointsOn i), ~~~(oneBit i)))

def ProperCover (u l : Mask) : Prop :=
  u ≠ 0 ∧ (∃ i : Vertex, l.getLsbD i.val = false) ∧
    ∀ i < 13, (mandatory u).getLsbD i = true → l.getLsbD i = true

private theorem weight_order (a b : Mask) (n : Nat)
    (sub : ∀ i < n, a.getLsbD i = true → b.getLsbD i = true) :
    weight a n ≤ weight b n ∧
      (weight a n = weight b n → ∀ i < n, a.getLsbD i = b.getLsbD i) := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    obtain ⟨le,equal⟩ := ih (fun i hi => sub i (by omega))
    have last := sub n (by omega)
    have lastLe : (a.getLsbD n).toNat ≤ (b.getLsbD n).toNat := by
      cases ha : a.getLsbD n <;> cases hb : b.getLsbD n <;> simp_all
    constructor
    · exact Nat.add_le_add le lastLe
    · intro sum i hi
      simp only [weight] at sum
      by_cases early : i < n
      · exact equal (by omega) i early
      · have eq : i = n := by omega
        subst i
        cases ha : a.getLsbD n <;> cases hb : b.getLsbD n <;> simp_all <;> omega

private def checkMask (n : Nat) : Bool :=
  let u := BitVec.ofNat 13 n
  u == 0 || mandatory u == BitVec.allOnes 13 ||
    decide (16 < weight (~~~u) 13 + weight (mandatory u) 13) ||
    minimumCovers.contains (u, mandatory u)

private def block (check : Nat → Bool) : Nat → Nat → Bool
  | 0, i => check i
  | d+1, i => block check d i && block check d (i+2^d)

private theorem joinBlock {check d i} (a : block check d i = true) (b : block check d (i+2^d) = true) :
    block check (d+1) i = true := Bool.and_eq_true_iff.mpr ⟨a,b⟩

private theorem block_at (check : Nat → Bool) (d i j : Nat) (lo : i ≤ j) (hi : j < i+2^d)
    (ok : block check d i = true) : check j = true := by
  induction d generalizing i with
  | zero =>
    have eq : i = j := by omega
    simpa [block,eq] using ok
  | succ d ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ok
    rw [Nat.pow_succ] at hi
    by_cases early : j < i+2^d
    · exact ih i lo early a
    · exact ih (i+2^d) (by omega) (by omega) b

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem verified : block checkMask 13 0 = true := by
  iterate 7 (all_goals apply joinBlock)
  all_goals as_aux_lemma => decide +kernel

private def valid (pair : Mask × Mask) : Bool :=
  let (u,l) := pair
  decide (u ≠ 0) && (List.finRange 13).any (fun i => !l.getLsbD i.val) &&
    (List.finRange 13).all (fun i => !(mandatory u).getLsbD i.val || l.getLsbD i.val) &&
    decide (weight (~~~u) 13 + weight l 13 = 16)

theorem list_certificate :
    minimumCovers.length = 26 ∧ minimumCovers.Nodup ∧ minimumCovers.all valid = true := by
  decide +kernel

theorem minimum_iff (u l : Mask) :
    ProperCover u l ∧ weight (~~~u) 13 + weight l 13 ≤ 16 ↔ (u,l) ∈ minimumCovers := by
  constructor
  · rintro ⟨⟨nonzero,⟨i,missing⟩,sub⟩,budget⟩
    have requiredMissing : (mandatory u).getLsbD i.val = false := by
      cases h : (mandatory u).getLsbD i.val with
      | false => rfl
      | true => exact Bool.noConfusion ((sub _ i.isLt h).symm.trans missing)
    have lower := mixed_cover_bound u (mandatory u) nonzero ⟨i,requiredMissing⟩ (fun _ _ h => h)
    obtain ⟨le,eq⟩ := weight_order (mandatory u) l 13 sub
    have same : mandatory u = l := BitVec.eq_of_getLsbD_eq (eq (by omega))
    have notFull : mandatory u ≠ BitVec.allOnes 13 := by
      intro full
      rw [full,BitVec.getLsbD_allOnes] at requiredMissing
      simp [i.isLt] at requiredMissing
    have chk := block_at checkMask 13 0 u.toNat (Nat.zero_le _) u.isLt verified
    simp only [checkMask,BitVec.ofNat_toNat,BitVec.setWidth_eq,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,
      List.contains_iff_mem] at chk
    rcases chk with ((h|h)|h)|h
    · exact False.elim (nonzero h)
    · exact False.elim (notFull h)
    · omega
    · exact same ▸ h
  · intro mem
    have info := List.all_eq_true.mp list_certificate.2.2 (u,l) mem
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,List.all_eq_true,
      Bool.not_eq_true',Bool.or_eq_true] at info
    obtain ⟨⟨⟨nz,⟨i,_,hi⟩⟩,allBits⟩,size⟩ := info
    refine ⟨⟨nz,⟨i,hi⟩,?_⟩,Nat.le_of_eq size⟩
    intro j hj hit
    have bit := allBits ⟨j,hj⟩ (List.mem_finRange _)
    simpa [hit] using bit


/-- Omitting several centers on both sides restricts how many flags one can cover. -/
private def profile (u l : Mask) : Prop :=
  (2 ≤ weight u 13 → 2 ≤ weight (~~~l) 13 → 18 ≤ weight (~~~u) 13 + weight l 13) ∧
  (3 ≤ weight u 13 → 3 ≤ weight (~~~l) 13 → 19 ≤ weight (~~~u) 13 + weight l 13) ∧
  (4 ≤ weight u 13 → weight (~~~l) 13 < 4)

private instance (u l : Mask) : Decidable (profile u l) := by unfold profile; infer_instance

private def checkProfile (n : Nat) : Bool :=
  let u := BitVec.ofNat 13 n
  decide (profile u (mandatory u))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem profile_verified : block checkProfile 13 0 = true := by
  iterate 7 (all_goals apply joinBlock)
  all_goals as_aux_lemma => decide +kernel

theorem omission_profile (u l : Mask) (h : ProperCover u l) :
    (2 ≤ weight u 13 → 2 ≤ weight (~~~l) 13 → 18 ≤ weight (~~~u) 13 + weight l 13) ∧
    (3 ≤ weight u 13 → 3 ≤ weight (~~~l) 13 → 19 ≤ weight (~~~u) 13 + weight l 13) ∧
    (4 ≤ weight u 13 → weight (~~~l) 13 < 4) := by
  have ok := block_at checkProfile 13 0 u.toNat (Nat.zero_le _) u.isLt profile_verified
  have cert : profile u (mandatory u) := by
    simpa only [checkProfile,BitVec.ofNat_toNat,BitVec.setWidth_eq,decide_eq_true_eq] using ok
  have size := (weight_order (mandatory u) l 13 h.2.2).1
  have comp : weight (~~~l) 13 ≤ weight (~~~(mandatory u)) 13 := by
    apply (weight_order _ _ _ ?_).1
    intro i hi bit
    have sub := h.2.2 i hi
    cases ha : (mandatory u).getLsbD i <;> cases hb : l.getLsbD i <;>
      simp_all
  obtain ⟨a,b,c⟩ := cert
  exact ⟨fun x y => Nat.le_trans (a x (Nat.le_trans y comp)) (Nat.add_le_add_left size _),
    fun x y => Nat.le_trans (b x (Nat.le_trans y comp)) (Nat.add_le_add_left size _),
    fun x => Nat.lt_of_le_of_lt comp (c x)⟩

theorem profile_examples :
    (weight (3 : Mask) 13, weight (~~~(mandatory 3)) 13,
      weight (~~~(3 : Mask)) 13 + weight (mandatory 3) 13) = (2,6,18) ∧
    (weight (7 : Mask) 13, weight (~~~(mandatory 7)) 13,
      weight (~~~(7 : Mask)) 13 + weight (mandatory 7) 13) = (3,4,19) := by decide +kernel

end PEqualNP.Research.OrderThreePlaneMinimumCovers
