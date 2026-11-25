import Std

/-! The diagonal flags and the offset-one flags already pin every cover
by at most thirteen point or line centers to one entire side of PG(2,3).
This concerns covers by stars and does not assume a general circuit is one. -/

namespace PEqualNP.Research.OrderThreePlaneStarCenters

abbrev Vertex := Fin 13
abbrev Selection := Vertex → Bool

def centerCount (p l : Selection) (vertices : List Vertex) : Nat :=
  match vertices with
  | [] => 0
  | i :: rest => (p i).toNat + (l i).toNat + centerCount p l rest

private theorem diagonal_bound (p l : Selection)
    (diag : ∀ i, p i = true ∨ l i = true) (xs : List Vertex) :
    xs.length ≤ centerCount p l xs := by
  induction xs with
  | nil => simp [centerCount]
  | cons i xs ih =>
    have h := diag i
    cases hp : p i <;> cases hl : l i <;>
      simp_all [centerCount,Bool.toNat] <;> omega

private theorem exclusive (p l : Selection) (diag : ∀ i, p i = true ∨ l i = true)
    (xs : List Vertex) (budget : centerCount p l xs ≤ xs.length) :
    ∀ i ∈ xs, p i = true → l i = false := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    have lower := diagonal_bound p l diag xs
    have h := diag j
    intro i member point
    rcases List.mem_cons.mp member with eq | tail
    · subst i
      cases line : l j <;> simp_all [centerCount,Bool.toNat] <;> omega
    · apply ih _ i tail point
      cases hp : p j <;> cases hl : l j <;>
        simp_all [centerCount,Bool.toNat] <;> omega

private def walk (i : Vertex) : Nat → Vertex
  | 0 => i
  | n+1 => walk i n + 1

private theorem reachable : ∀ i j : Vertex, ∃ n : Fin 13, walk i n.val = j := by
  decide +kernel

theorem side_rigidity (p l : Selection)
    (diag : ∀ i, p i = true ∨ l i = true)
    (shift : ∀ i : Vertex, p (i+1) = true ∨ l i = true)
    (budget : centerCount p l (List.finRange 13) ≤ 13) :
    (∀ i, p i = true ∧ l i = false) ∨ (∀ i, p i = false ∧ l i = true) := by
  have only (i : Vertex) := exclusive p l diag (List.finRange 13) (by simpa using budget)
    i (List.mem_finRange i)
  by_cases somePoint : ∃ i, p i = true
  · obtain ⟨start,hit⟩ := somePoint
    have along (n : Nat) : p (walk start n) = true := by
      induction n with
      | zero => exact hit
      | succ n ih =>
        rcases shift (walk start n) with yes | no
        · exact yes
        · simp [only _ ih] at no
    left
    intro i
    obtain ⟨n,eq⟩ := reachable start i
    have yes := eq ▸ along n.val
    exact ⟨yes,only i yes⟩
  · right
    intro i
    cases hp : p i with
    | false => exact ⟨rfl,(diag i).resolve_left (by simp [hp])⟩
    | true => exact False.elim (somePoint ⟨i,hp⟩)


abbrev Mask := BitVec 13

/-- For an omitted point p, the four mandatory lines are p, p-1, p-3 and p-9. -/
def mandatory (u : Mask) : Mask :=
  u ||| u.rotateRight 1 ||| u.rotateRight 3 ||| u.rotateRight 9

theorem mandatory_semantics (u : Mask) (i : Vertex) :
    (mandatory u).getLsbD i.val =
      (u.getLsbD i.val || u.getLsbD ((i.val+1)%13) ||
       u.getLsbD ((i.val+3)%13) || u.getLsbD ((i.val+9)%13)) := by
  have choices : ∀ i : Vertex, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by decide +kernel
  rcases choices i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [mandatory] <;> rfl

def weight (v : Mask) : Nat → Nat
  | 0 => 0
  | n+1 => weight v n + (v.getLsbD n).toNat

private def test (n : Nat) : Bool :=
  let u := BitVec.ofNat 13 n
  u == 0 || mandatory u == BitVec.allOnes 13 ||
    decide (16 ≤ weight (~~~u) 13 + weight (mandatory u) 13)

private def block : Nat → Nat → Bool
  | 0, i => test i
  | d+1, i => block d i && block d (i+2^d)

private theorem joinBlocks {d i} (a : block d i = true) (b : block d (i+2^d) = true) :
    block (d+1) i = true := Bool.and_eq_true_iff.mpr ⟨a,b⟩

private theorem block_sound (d i j : Nat) (lo : i ≤ j) (hi : j < i+2^d)
    (ok : block d i = true) : test j = true := by
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

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
private theorem verified : block 13 0 = true := by
  iterate 7 (all_goals apply joinBlocks)
  all_goals as_aux_lemma => decide +kernel

private theorem weight_mono (a b : Mask) (n : Nat)
    (h : ∀ i < n, a.getLsbD i = true → b.getLsbD i = true) : weight a n ≤ weight b n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have small := ih (fun i hi => h i (by omega))
    have last := h n (by omega)
    simp only [weight]
    cases ha : a.getLsbD n <;> cases hb : b.getLsbD n <;>
      simp_all [Bool.toNat] <;> omega

/-- If at least one point and one line are omitted, a star cover costs at least 16 centers.
Here u lists omitted points and l lists selected lines, possibly including redundant ones. -/
theorem mixed_cover_bound (u l : Mask) (pointMissing : u ≠ 0)
    (lineMissing : ∃ i : Fin 13, l.getLsbD i.val = false)
    (covers : ∀ i < 13, (mandatory u).getLsbD i = true → l.getLsbD i = true) :
    16 ≤ weight (~~~u) 13 + weight l 13 := by
  have notFull : mandatory u ≠ BitVec.allOnes 13 := by
    intro eq
    obtain ⟨i,hi⟩ := lineMissing
    have full : (mandatory u).getLsbD i.val = true := by
      rw [eq,BitVec.getLsbD_allOnes]
      exact decide_eq_true i.isLt
    have seen := covers i.val i.isLt full
    simp_all
  have ok := block_sound 13 0 u.toNat (Nat.zero_le _) u.isLt verified
  have required : 16 ≤ weight (~~~u) 13 + weight (mandatory u) 13 := by
    simp only [test, BitVec.ofNat_toNat, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
    rcases ok with (h|h)|h
    · exact False.elim (pointMissing h)
    · exact False.elim (notFull h)
    · exact h
  exact Nat.le_trans required (Nat.add_le_add_left (weight_mono _ _ _ covers) _)

/-- Omitting point zero forces four lines. The resulting proper mixed cover has size 16. -/
theorem sharp_example :
    (1 : Mask) ≠ 0 ∧ (mandatory 1).getLsbD 1 = false ∧
    weight (~~~(1 : Mask)) 13 + weight (mandatory 1) 13 = 16 := by decide +kernel

end PEqualNP.Research.OrderThreePlaneStarCenters
