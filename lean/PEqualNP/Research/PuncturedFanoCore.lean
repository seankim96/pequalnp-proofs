import Std.Tactic.BVDecide
import Mathlib.Data.List.Basic
import PEqualNP.Defs.LratEncoding
import PEqualNP.Library.LRAT.Link

/-! Exact completions of the punctured Fano incidence test. Bit i is coordinate i.
The two distinguished endpoints are 0 and 7. The remaining cycle is ordered
2,12,5,9,6,11,4,13 around its eight edges. -/

namespace PEqualNP.Research.PuncturedFanoCore

abbrev Word := BitVec 14
abbrev Core := BitVec 8

def kept (x : Word) : Bool :=
    (x.getLsbD 0 && x.getLsbD 8) ||
    (x.getLsbD 0 && x.getLsbD 10) ||
    (x.getLsbD 1 && x.getLsbD 7) ||
    (x.getLsbD 1 && x.getLsbD 9) ||
    (x.getLsbD 1 && x.getLsbD 13) ||
    (x.getLsbD 2 && x.getLsbD 8) ||
    (x.getLsbD 2 && x.getLsbD 12) ||
    (x.getLsbD 2 && x.getLsbD 13) ||
    (x.getLsbD 3 && x.getLsbD 7) ||
    (x.getLsbD 3 && x.getLsbD 11) ||
    (x.getLsbD 3 && x.getLsbD 12) ||
    (x.getLsbD 4 && x.getLsbD 10) ||
    (x.getLsbD 4 && x.getLsbD 11) ||
    (x.getLsbD 4 && x.getLsbD 13) ||
    (x.getLsbD 5 && x.getLsbD 9) ||
    (x.getLsbD 5 && x.getLsbD 10) ||
    (x.getLsbD 5 && x.getLsbD 12) ||
    (x.getLsbD 6 && x.getLsbD 8) ||
    (x.getLsbD 6 && x.getLsbD 9) ||
    (x.getLsbD 6 && x.getLsbD 11)

def full (x : Word) : Bool := kept x || (x.getLsbD 0 && x.getLsbD 7)

def readCore (x : Word) : Core :=
    BitVec.ofBool (x.getLsbD 13) ++
    BitVec.ofBool (x.getLsbD 4) ++
    BitVec.ofBool (x.getLsbD 11) ++
    BitVec.ofBool (x.getLsbD 6) ++
    BitVec.ofBool (x.getLsbD 9) ++
    BitVec.ofBool (x.getLsbD 5) ++
    BitVec.ofBool (x.getLsbD 12) ++
    BitVec.ofBool (x.getLsbD 2)

def embed (z : Core) : Word :=
    BitVec.ofBool (z.getLsbD 7) ++
    BitVec.ofBool (z.getLsbD 1) ++
    BitVec.ofBool (z.getLsbD 5) ++
    BitVec.ofBool (false) ++
    BitVec.ofBool (z.getLsbD 3) ++
    BitVec.ofBool (false) ++
    BitVec.ofBool (true) ++
    BitVec.ofBool (z.getLsbD 4) ++
    BitVec.ofBool (z.getLsbD 2) ++
    BitVec.ofBool (z.getLsbD 6) ++
    BitVec.ofBool (false) ++
    BitVec.ofBool (z.getLsbD 0) ++
    BitVec.ofBool (false) ++
    BitVec.ofBool (true)

def independent (z : Core) : Bool :=
  !(
    (z.getLsbD 0 && z.getLsbD 1) ||
    (z.getLsbD 1 && z.getLsbD 2) ||
    (z.getLsbD 2 && z.getLsbD 3) ||
    (z.getLsbD 3 && z.getLsbD 4) ||
    (z.getLsbD 4 && z.getLsbD 5) ||
    (z.getLsbD 5 && z.getLsbD 6) ||
    (z.getLsbD 6 && z.getLsbD 7) ||
    (z.getLsbD 7 && z.getLsbD 0))

abbrev sub {w : ℕ} (x y : BitVec w) : Prop := x &&& y = x

theorem decode (z : Core) : readCore (embed z) = z := by
  unfold readCore embed
  bv_decide

theorem gap (x : Word) :
    full x = true ∧ kept x = false ↔ x = embed (readCore x) ∧ independent (readCore x) = true := by
  unfold full kept embed readCore independent
  bv_decide

private theorem kept_mono (x y : Word) : sub x y → kept x = true → kept y = true := by
  unfold sub kept
  bv_decide

private theorem full_mono (x y : Word) : sub x y → full x = true → full y = true := by
  unfold sub full kept
  bv_decide

private theorem read_mono (x y : Word) : sub x y → sub (readCore x) (readCore y) := by
  unfold sub readCore
  bv_decide

private theorem embed_mono (z w : Core) : sub z w → sub (embed z) (embed w) := by
  unfold sub embed
  bv_decide

abbrev MonotoneBits {w : ℕ} (f : BitVec w → Bool) : Prop :=
  ∀ x y, sub x y → f x = true → f y = true

def Allowed (f : Word → Bool) : Prop :=
  MonotoneBits f ∧ f (embed 0) = false ∧
  (∀ x, kept x = true → f x = true) ∧ (∀ x, f x = true → full x = true)

def Residual (r : Core → Bool) : Prop :=
  r 0 = false ∧ ∀ z w, independent z = true → independent w = true →
    sub z w → r z = true → r w = true

def completion (r : Core → Bool) (x : Word) : Bool :=
  kept x || (full x && r (readCore x))

theorem classify (f : Word → Bool) (h : Allowed f) :
    ∃ r, Residual r ∧ f = completion r := by
  refine ⟨fun z => f (embed z), ⟨h.2.1,fun z w _ _ le hz => h.1 _ _ (embed_mono z w le) hz⟩,?_⟩
  funext x
  by_cases yes : kept x = true
  · simp [completion,yes,h.2.2.1 x yes]
  · have no : kept x = false := Bool.eq_false_of_not_eq_true yes
    by_cases top : full x = true
    · have eq := ((gap x).mp ⟨top,no⟩).1
      simp only [completion,no,top,Bool.false_or,Bool.true_and]
      exact congrArg f eq
    · have bot : f x = false := Bool.eq_false_of_not_eq_true (fun hx => top (h.2.2.2 x hx))
      simp [completion,no,Bool.eq_false_of_not_eq_true top,bot]

theorem realize (r : Core → Bool) (h : Residual r) : Allowed (completion r) := by
  have upper (x : Word) : completion r x = true → full x = true := by
    intro hx
    rcases Bool.or_eq_true_iff.mp hx with hot|other
    · simp [full,hot]
    · exact (Bool.and_eq_true_iff.mp other).1
  refine ⟨?_,?_,fun x hx => by simp [completion,hx],upper⟩
  · intro x y le hx
    by_cases hot : kept x = true
    · simp [completion,kept_mono x y le hot]
    · by_cases next : kept y = true
      · simp [completion,next]
      · have low := Bool.eq_false_of_not_eq_true hot
        have low' := Bool.eq_false_of_not_eq_true next
        have top := upper x hx
        have top' := full_mono x y le top
        have rx : r (readCore x) = true := by simpa [completion,low,top] using hx
        have ry := h.2 _ _ ((gap _).mp ⟨top,low⟩).2 ((gap _).mp ⟨top',low'⟩).2 (read_mono x y le) rx
        simp [completion,low',top',ry]
  · have empty : kept (embed 0) = false := by decide +kernel
    unfold completion
    rw [empty,decode,h.1]
    simp

theorem independent_count :
    ((List.range 256).filter (fun i => independent (BitVec.ofNat 8 i))).length = 47 := by decide +kernel

theorem free_count :
    ((List.range 256).filter (fun i => i != 0 && independent (BitVec.ofNat 8 i))).length = 46 := by decide +kernel

def reflect (z : Core) : Core :=
    BitVec.ofBool (z.getLsbD 1) ++
    BitVec.ofBool (z.getLsbD 2) ++
    BitVec.ofBool (z.getLsbD 3) ++
    BitVec.ofBool (z.getLsbD 4) ++
    BitVec.ofBool (z.getLsbD 5) ++
    BitVec.ofBool (z.getLsbD 6) ++
    BitVec.ofBool (z.getLsbD 7) ++
    BitVec.ofBool (z.getLsbD 0)

def orbit (z : Core) : List Core :=
  [z.rotateLeft 0, z.rotateLeft 1, z.rotateLeft 2, z.rotateLeft 3, z.rotateLeft 4, z.rotateLeft 5, z.rotateLeft 6, z.rotateLeft 7, (reflect z).rotateLeft 0, (reflect z).rotateLeft 1, (reflect z).rotateLeft 2, (reflect z).rotateLeft 3, (reflect z).rotateLeft 4, (reflect z).rotateLeft 5, (reflect z).rotateLeft 6, (reflect z).rotateLeft 7]

def representatives : List Core := [1,5,9,17,21,37,85]

theorem seven_orbits (z : Core) : independent z = true → z ≠ 0 →
    (orbit z).any (fun t => representatives.contains t) = true := by
  unfold independent representatives orbit reflect
  simp only [List.any_cons,List.any_nil,List.contains_cons,List.contains_nil]
  bv_decide

/-- The seven representatives are all independent, nonempty and pairwise
inequivalent under rotations and reflections. -/
theorem distinct_orbits :
    (representatives.all (fun z => z != 0 && independent z)) = true ∧
    (representatives.all fun z => representatives.all fun w => !(orbit z).contains w || z == w) = true := by
  decide +kernel


/-- A small monotone circuit that agrees on the listed rows gives a satisfying
assignment for exactly the pinned project CNF. Rows outside the list are free. -/
theorem row_cnf_complete (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (bounded : ∀ r ∈ rows, r < 2^n)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (small : C.size ≤ s)
    (agree : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) :
    PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc n s g rows) := by
  let R := fun r => r ∈ rows
  have hv := PEqualNP.Library.LRAT.Link.valid_ofCirc n s g R C mono small agree
  obtain ⟨M,valid,nf⟩ := PEqualNP.Library.LRAT.Link.exists_nf ⟨_,hv⟩
  exact ⟨PEqualNP.Library.LRAT.Link.val n s M,PEqualNP.Library.LRAT.Link.enc_sat bounded valid nf⟩


def rotateLabels (x : Word) : Word :=
    BitVec.ofBool (x.getLsbD 4) ++
    BitVec.ofBool (x.getLsbD 2) ++
    BitVec.ofBool (x.getLsbD 6) ++
    BitVec.ofBool (x.getLsbD 3) ++
    BitVec.ofBool (x.getLsbD 5) ++
    BitVec.ofBool (x.getLsbD 1) ++
    BitVec.ofBool (x.getLsbD 0) ++
    BitVec.ofBool (x.getLsbD 9) ++
    BitVec.ofBool (x.getLsbD 12) ++
    BitVec.ofBool (x.getLsbD 11) ++
    BitVec.ofBool (x.getLsbD 8) ++
    BitVec.ofBool (x.getLsbD 13) ++
    BitVec.ofBool (x.getLsbD 10) ++
    BitVec.ofBool (x.getLsbD 7)

def reflectLabels (x : Word) : Word :=
    BitVec.ofBool (x.getLsbD 12) ++
    BitVec.ofBool (x.getLsbD 13) ++
    BitVec.ofBool (x.getLsbD 9) ++
    BitVec.ofBool (x.getLsbD 10) ++
    BitVec.ofBool (x.getLsbD 11) ++
    BitVec.ofBool (x.getLsbD 8) ++
    BitVec.ofBool (x.getLsbD 7) ++
    BitVec.ofBool (x.getLsbD 6) ++
    BitVec.ofBool (x.getLsbD 4) ++
    BitVec.ofBool (x.getLsbD 5) ++
    BitVec.ofBool (x.getLsbD 1) ++
    BitVec.ofBool (x.getLsbD 2) ++
    BitVec.ofBool (x.getLsbD 3) ++
    BitVec.ofBool (x.getLsbD 0)

/-- The dihedral generators on the core lift to symmetries of the
original labeled 14-variable graph that also preserve the removed edge. -/
theorem graph_symmetries (x : Word) :
    full (rotateLabels x) = full x ∧ kept (rotateLabels x) = kept x ∧
    readCore (rotateLabels x) = (readCore x).rotateLeft 1 ∧
    full (reflectLabels x) = full x ∧ kept (reflectLabels x) = kept x ∧
    readCore (reflectLabels x) = reflect (readCore x) := by
  unfold rotateLabels reflectLabels full kept readCore reflect
  bv_decide

def positiveRows : List Word := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
def maximalNegativeRows : List Word := [127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]

theorem includes_positive (x : Word) : kept x = true →
    positiveRows.any (fun y => decide (sub y x)) = true := by
  unfold kept positiveRows sub
  simp only [List.any_cons,List.any_nil]
  bv_decide

theorem extends_negative (x : Word) : full x = false →
    maximalNegativeRows.any (fun y => decide (sub x y)) = true := by
  unfold full kept maximalNegativeRows sub
  simp only [List.any_cons,List.any_nil]
  bv_decide

def passes (f : Word → Bool) : Prop :=
  (∀ x ∈ positiveRows, f x = true) ∧ (∀ y ∈ maximalNegativeRows, f y = false) ∧ f (embed 0) = false

/-- For monotone circuits precisely these 58 tests suffice. The 20
positive edges force the lower envelope, and the 37 maximal negative
rows force the upper envelope. The remaining test rejects the bare flag. -/
theorem tests_exact (f : Word → Bool) (mono : MonotoneBits f) : passes f ↔ Allowed f := by
  constructor
  · rintro ⟨pos,neg,empty⟩
    refine ⟨mono,empty,?_,?_⟩
    · intro x hx
      obtain ⟨y,hy,le⟩ := List.any_eq_true.mp (includes_positive x hx)
      exact mono y x (of_decide_eq_true le) (pos y hy)
    · intro x hx
      cases v : full x with
      | true => rfl
      | false =>
        obtain ⟨y,hy,le⟩ := List.any_eq_true.mp (extends_negative x v)
        exact Bool.noConfusion ((mono x y (of_decide_eq_true le) hx).symm.trans (neg y hy))
  · rintro ⟨_,empty,low,high⟩
    refine ⟨fun x hx => low _ (List.all_eq_true.mp (show positiveRows.all kept = true from by decide +kernel) x hx),?_,empty⟩
    intro y hy
    have no : full y = false := by
      have h := List.all_eq_true.mp (show maximalNegativeRows.all (fun y => !(full y)) = true from by decide +kernel) y hy
      simpa using h
    exact Bool.eq_false_of_not_eq_true (fun on => Bool.noConfusion ((high y on).symm.trans no))

end PEqualNP.Research.PuncturedFanoCore
