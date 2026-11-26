import PEqualNP.Research.PermanentThreeRows
import PEqualNP.Research.PermanentSupportMinors
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination


namespace PEqualNP.Research.PermanentTwelveCoordinates
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Matrix
abbrev T := Fin 4 × Fin 4 → ℂ
abbrev X := Fin 17 → ℂ

def gradient (t : T) : ℂ :=
    16 * t (0,0) +
    16 * t (1,1) +
    16 * t (2,2) +
    16 * t (3,3) +
    11 * t (2,3) +
    11 * t (3,2) +
    11 * t (1,2) +
    11 * t (2,1) +
    11 * t (3,1) +
    11 * t (1,3) +
    11 * t (0,1) +
    11 * t (1,0) +
    11 * t (2,0) +
    11 * t (3,0) +
    11 * t (0,2) +
    11 * t (0,3)

def second (t : T) : ℂ :=
    5 * t (0,0) * t (1,1) +
    5 * t (0,0) * t (2,2) +
    5 * t (0,0) * t (3,3) +
    5 * t (1,1) * t (2,2) +
    5 * t (1,1) * t (3,3) +
    5 * t (2,2) * t (3,3) +
    3 * t (0,0) * t (2,3) +
    3 * t (0,0) * t (3,2) +
    3 * t (1,1) * t (2,3) +
    3 * t (1,1) * t (3,2) +
    5 * t (2,3) * t (3,2) +
    3 * t (0,0) * t (1,2) +
    3 * t (0,0) * t (2,1) +
    5 * t (1,2) * t (2,1) +
    3 * t (1,2) * t (3,3) +
    3 * t (2,1) * t (3,3) +
    3 * t (0,0) * t (3,1) +
    3 * t (1,2) * t (2,3) +
    3 * t (1,2) * t (3,1) +
    3 * t (2,3) * t (3,1) +
    3 * t (0,0) * t (1,3) +
    3 * t (1,3) * t (2,1) +
    3 * t (1,3) * t (3,2) +
    3 * t (2,1) * t (3,2) +
    3 * t (1,3) * t (2,2) +
    5 * t (1,3) * t (3,1) +
    3 * t (2,2) * t (3,1) +
    5 * t (0,1) * t (1,0) +
    3 * t (0,1) * t (2,2) +
    3 * t (0,1) * t (3,3) +
    3 * t (1,0) * t (2,2) +
    3 * t (1,0) * t (3,3) +
    2 * t (0,1) * t (2,3) +
    2 * t (0,1) * t (3,2) +
    2 * t (1,0) * t (2,3) +
    2 * t (1,0) * t (3,2) +
    3 * t (0,1) * t (1,2) +
    3 * t (0,1) * t (2,0) +
    3 * t (1,2) * t (2,0) +
    3 * t (2,0) * t (3,3) +
    3 * t (0,1) * t (3,0) +
    2 * t (1,2) * t (3,0) +
    3 * t (2,3) * t (3,0) +
    3 * t (0,1) * t (1,3) +
    2 * t (1,3) * t (2,0) +
    3 * t (2,0) * t (3,2) +
    3 * t (1,3) * t (3,0) +
    3 * t (2,2) * t (3,0) +
    3 * t (0,2) * t (1,0) +
    3 * t (0,2) * t (2,1) +
    3 * t (0,2) * t (3,3) +
    3 * t (1,0) * t (2,1) +
    3 * t (0,2) * t (2,3) +
    2 * t (0,2) * t (3,1) +
    3 * t (1,0) * t (3,1) +
    3 * t (0,2) * t (1,1) +
    5 * t (0,2) * t (2,0) +
    3 * t (1,1) * t (2,0) +
    3 * t (0,2) * t (3,0) +
    3 * t (1,1) * t (3,0) +
    2 * t (0,2) * t (1,3) +
    2 * t (2,0) * t (3,1) +
    2 * t (2,1) * t (3,0) +
    3 * t (0,3) * t (1,0) +
    2 * t (0,3) * t (2,1) +
    3 * t (0,3) * t (3,2) +
    3 * t (0,3) * t (2,2) +
    3 * t (0,3) * t (3,1) +
    3 * t (0,3) * t (1,1) +
    3 * t (0,3) * t (2,0) +
    5 * t (0,3) * t (3,0) +
    2 * t (0,3) * t (1,2)

def third (t : T) : ℂ :=
    2 * t (0,0) * t (1,1) * t (2,2) +
    2 * t (0,0) * t (1,1) * t (3,3) +
    2 * t (0,0) * t (2,2) * t (3,3) +
    2 * t (1,1) * t (2,2) * t (3,3) +
    t (0,0) * t (1,1) * t (2,3) +
    t (0,0) * t (1,1) * t (3,2) +
    2 * t (0,0) * t (2,3) * t (3,2) +
    2 * t (1,1) * t (2,3) * t (3,2) +
    2 * t (0,0) * t (1,2) * t (2,1) +
    t (0,0) * t (1,2) * t (3,3) +
    t (0,0) * t (2,1) * t (3,3) +
    2 * t (1,2) * t (2,1) * t (3,3) +
    t (0,0) * t (1,2) * t (2,3) +
    t (0,0) * t (1,2) * t (3,1) +
    t (0,0) * t (2,3) * t (3,1) +
    2 * t (1,2) * t (2,3) * t (3,1) +
    t (0,0) * t (1,3) * t (2,1) +
    t (0,0) * t (1,3) * t (3,2) +
    t (0,0) * t (2,1) * t (3,2) +
    2 * t (1,3) * t (2,1) * t (3,2) +
    t (0,0) * t (1,3) * t (2,2) +
    2 * t (0,0) * t (1,3) * t (3,1) +
    t (0,0) * t (2,2) * t (3,1) +
    2 * t (1,3) * t (2,2) * t (3,1) +
    2 * t (0,1) * t (1,0) * t (2,2) +
    2 * t (0,1) * t (1,0) * t (3,3) +
    t (0,1) * t (2,2) * t (3,3) +
    t (1,0) * t (2,2) * t (3,3) +
    t (0,1) * t (1,0) * t (2,3) +
    t (0,1) * t (1,0) * t (3,2) +
    t (0,1) * t (2,3) * t (3,2) +
    t (1,0) * t (2,3) * t (3,2) +
    2 * t (0,1) * t (1,2) * t (2,0) +
    t (0,1) * t (1,2) * t (3,3) +
    t (0,1) * t (2,0) * t (3,3) +
    t (1,2) * t (2,0) * t (3,3) +
    t (0,1) * t (1,2) * t (2,3) +
    t (0,1) * t (1,2) * t (3,0) +
    t (0,1) * t (2,3) * t (3,0) +
    t (1,2) * t (2,3) * t (3,0) +
    t (0,1) * t (1,3) * t (2,0) +
    t (0,1) * t (1,3) * t (3,2) +
    t (0,1) * t (2,0) * t (3,2) +
    t (1,3) * t (2,0) * t (3,2) +
    t (0,1) * t (1,3) * t (2,2) +
    2 * t (0,1) * t (1,3) * t (3,0) +
    t (0,1) * t (2,2) * t (3,0) +
    t (1,3) * t (2,2) * t (3,0) +
    2 * t (0,2) * t (1,0) * t (2,1) +
    t (0,2) * t (1,0) * t (3,3) +
    t (0,2) * t (2,1) * t (3,3) +
    t (1,0) * t (2,1) * t (3,3) +
    t (0,2) * t (1,0) * t (2,3) +
    t (0,2) * t (1,0) * t (3,1) +
    t (0,2) * t (2,3) * t (3,1) +
    t (1,0) * t (2,3) * t (3,1) +
    2 * t (0,2) * t (1,1) * t (2,0) +
    t (0,2) * t (1,1) * t (3,3) +
    2 * t (0,2) * t (2,0) * t (3,3) +
    t (1,1) * t (2,0) * t (3,3) +
    t (0,2) * t (1,1) * t (2,3) +
    t (0,2) * t (1,1) * t (3,0) +
    2 * t (0,2) * t (2,3) * t (3,0) +
    t (1,1) * t (2,3) * t (3,0) +
    t (0,2) * t (1,3) * t (2,0) +
    t (0,2) * t (1,3) * t (3,1) +
    t (0,2) * t (2,0) * t (3,1) +
    t (1,3) * t (2,0) * t (3,1) +
    t (0,2) * t (1,3) * t (2,1) +
    t (0,2) * t (1,3) * t (3,0) +
    t (0,2) * t (2,1) * t (3,0) +
    t (1,3) * t (2,1) * t (3,0) +
    t (0,3) * t (1,0) * t (2,1) +
    t (0,3) * t (1,0) * t (3,2) +
    t (0,3) * t (2,1) * t (3,2) +
    t (1,0) * t (2,1) * t (3,2) +
    t (0,3) * t (1,0) * t (2,2) +
    2 * t (0,3) * t (1,0) * t (3,1) +
    t (0,3) * t (2,2) * t (3,1) +
    t (1,0) * t (2,2) * t (3,1) +
    t (0,3) * t (1,1) * t (2,0) +
    t (0,3) * t (1,1) * t (3,2) +
    2 * t (0,3) * t (2,0) * t (3,2) +
    t (1,1) * t (2,0) * t (3,2) +
    t (0,3) * t (1,1) * t (2,2) +
    2 * t (0,3) * t (1,1) * t (3,0) +
    2 * t (0,3) * t (2,2) * t (3,0) +
    t (1,1) * t (2,2) * t (3,0) +
    t (0,3) * t (1,2) * t (2,0) +
    t (0,3) * t (1,2) * t (3,1) +
    t (0,3) * t (2,0) * t (3,1) +
    t (1,2) * t (2,0) * t (3,1) +
    t (0,3) * t (1,2) * t (2,1) +
    t (0,3) * t (1,2) * t (3,0) +
    t (0,3) * t (2,1) * t (3,0) +
    t (1,2) * t (2,1) * t (3,0)

def fourth (t : T) : ℂ :=
    t (0,0) * t (1,1) * t (2,2) * t (3,3) +
    t (0,0) * t (1,1) * t (2,3) * t (3,2) +
    t (0,0) * t (1,2) * t (2,1) * t (3,3) +
    t (0,0) * t (1,2) * t (2,3) * t (3,1) +
    t (0,0) * t (1,3) * t (2,1) * t (3,2) +
    t (0,0) * t (1,3) * t (2,2) * t (3,1) +
    t (0,1) * t (1,0) * t (2,2) * t (3,3) +
    t (0,1) * t (1,0) * t (2,3) * t (3,2) +
    t (0,1) * t (1,2) * t (2,0) * t (3,3) +
    t (0,1) * t (1,2) * t (2,3) * t (3,0) +
    t (0,1) * t (1,3) * t (2,0) * t (3,2) +
    t (0,1) * t (1,3) * t (2,2) * t (3,0) +
    t (0,2) * t (1,0) * t (2,1) * t (3,3) +
    t (0,2) * t (1,0) * t (2,3) * t (3,1) +
    t (0,2) * t (1,1) * t (2,0) * t (3,3) +
    t (0,2) * t (1,1) * t (2,3) * t (3,0) +
    t (0,2) * t (1,3) * t (2,0) * t (3,1) +
    t (0,2) * t (1,3) * t (2,1) * t (3,0) +
    t (0,3) * t (1,0) * t (2,1) * t (3,2) +
    t (0,3) * t (1,0) * t (2,2) * t (3,1) +
    t (0,3) * t (1,1) * t (2,0) * t (3,2) +
    t (0,3) * t (1,1) * t (2,2) * t (3,0) +
    t (0,3) * t (1,2) * t (2,0) * t (3,1) +
    t (0,3) * t (1,2) * t (2,1) * t (3,0)

theorem expansion (t : T) (s : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + s * t (i,j)) =
      65 + s * gradient t + s^2 * second t + s^3 * third t + s^4 * fourth t := by
  rw [PEqualNP.Research.PermanentThreeRows.perm4]
  simp +decide only [Matrix.of_apply, ite_true, ite_false, gradient, second, third, fourth]
  ring

theorem interpolate (a b c d : ℂ)
    (he : ∀ s : ℂ, 65 + s*a + s^2*b + s^3*c + s^4*d = 65) : a = 0 ∧ b = 0 := by
  constructor
  · linear_combination (8 * (he 1 - he (-1)) - (he 2 - he (-2))) / 12
  · linear_combination (16 * (he 1 + he (-1)) - (he 2 + he (-2))) / 24

theorem moments (L : Submodule ℂ T) (t : L)
    (hl : ∀ u ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + u (i,j)) = 65) :
    gradient t.val = 0 ∧ second t.val = 0 := by
  apply interpolate _ _ (third t.val) (fourth t.val)
  intro s
  rw [← expansion t.val s]
  exact hl (s • t.val) (L.smul_mem s t.property)

def H : Matrix (Fin 17) (Fin 17) ℂ := fun i j => (Int.castRingHom ℂ) (PEqualNP.Research.PermanentSupportMinors.H i j)
def J : Matrix (Fin 17) (Fin 17) ℂ := (Int.castRingHom ℂ).mapMatrix PEqualNP.Research.PermanentSupportMinors.J

theorem inverse_certificate : H * J = (8090940 : ℂ) • (1 : Matrix (Fin 17) (Fin 17) ℂ) := by
  have e := congrArg (Int.castRingHom ℂ).mapMatrix PEqualNP.Research.PermanentSupportMinors.inverse_certificate
  rw [map_mul] at e
  refine e.trans ?_
  ext i j
  change (Int.castRingHom ℂ) ((8090940 : ℤ) * (1 : Matrix (Fin 17) (Fin 17) ℤ) i j) = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem regular : H.toBilin'.Nondegenerate := by
  apply Matrix.Nondegenerate.toBilin'
  apply Matrix.nondegenerate_of_det_ne_zero
  have e := congrArg Matrix.det inverse_certificate
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at e
  intro h
  rw [h, zero_mul] at e
  norm_num at e

theorem symmetric : H.toBilin'.IsSymm := by
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  have e : PEqualNP.Research.PermanentSupportMinors.H.transpose = PEqualNP.Research.PermanentSupportMinors.H := by decide +kernel
  exact congrArg (Int.castRingHom ℂ).mapMatrix e

def pack (L : Submodule ℂ T) : (L × ℂ) →ₗ[ℂ] X where
  toFun p := ![p.1.val (0,0), p.1.val (0,1), p.1.val (0,2), p.1.val (0,3), p.1.val (1,0), p.1.val (1,1), p.1.val (1,2), p.1.val (1,3), p.1.val (2,0), p.1.val (2,1), p.1.val (2,2), p.1.val (2,3), p.1.val (3,0), p.1.val (3,1), p.1.val (3,2), p.1.val (3,3), p.2]
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

theorem pack_at (L : Submodule ℂ T) (p : L × ℂ) (a : Fin 16) :
    pack L p a.castSucc = p.1.val (finProdFinEquiv.symm a) := by
  fin_cases a <;> rfl

theorem pack_inj (L : Submodule ℂ T) : Function.Injective (pack L) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
    · exact congrFun h 5
    · exact congrFun h 6
    · exact congrFun h 7
    · exact congrFun h 8
    · exact congrFun h 9
    · exact congrFun h 10
    · exact congrFun h 11
    · exact congrFun h 12
    · exact congrFun h 13
    · exact congrFun h 14
    · exact congrFun h 15
  · exact congrFun h 16

theorem diagonal (L : Submodule ℂ T) (p : L × ℂ) :
    H.toBilin' (pack L p) (pack L p) = 2 * second p.1.val + 2 * p.2 * gradient p.1.val := by
  calc
    _ = ∑ i : Fin 17, ∑ j : Fin 17, pack L p i * ((Int.castRingHom ℂ) (PEqualNP.Research.PermanentSupportMinors.H i j)) * pack L p j :=
      Matrix.toBilin'_apply _ _ _
    _ = _ := by
      simp only [PEqualNP.Research.PermanentSupportMinors.H, pack, Fin.sum_univ_succ, Fin.sum_univ_zero, gradient, second,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_succ,
        map_zero, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
      ring

theorem codimFour (H J : Matrix (Fin 17) (Fin 17) ℂ)
    (k : ℂ) (hk : H * J = k • (1 : Matrix (Fin 17) (Fin 17) ℂ))
    (hr : H.toBilin'.Nondegenerate) (f : Fin 4 → Fin 17) (hd : (J.submatrix f f).det ≠ 0)
    (W : Submodule ℂ X) (hz : ∀ x ∈ W, ∀ i, x (f i) = 0)
    (hw : W ≤ H.toBilin'.orthogonal W) : Module.finrank ℂ W ≤ 6 := by
  let N := J.submatrix id f
  let g := N.mulVecLin
  let F := W.subtype.coprod g
  have inj : Function.Injective F := by
    rintro ⟨x,a⟩ ⟨y,b⟩ e
    change x.val + N *ᵥ a = y.val + N *ᵥ b at e
    have ev : (J.submatrix f f) *ᵥ a = (J.submatrix f f) *ᵥ b := by
      funext i
      have h := congrFun e (f i)
      simp only [Pi.add_apply, hz _ x.property, hz _ y.property, zero_add] at h
      exact h
    have eqab := Matrix.mulVec_injective_of_det_ne_zero hd ev
    subst b
    exact Prod.ext (Subtype.ext (add_right_cancel e)) rfl
  have orth : F.range ≤ H.toBilin'.orthogonal W := by
    rintro _ ⟨⟨x,a⟩,rfl⟩
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    change H.toBilin' y (x.val + N *ᵥ a) = 0
    rw [map_add, LinearMap.BilinForm.mem_orthogonal_iff.mp (hw x.property) y hy, zero_add,
      Matrix.toBilin'_apply', Matrix.mulVec_mulVec]
    have hN : H * N = (H*J).submatrix id f := rfl
    rw [hN, Matrix.dotProduct_mulVec]
    have hz' : y ᵥ* (H*J).submatrix id f = 0 := by
      funext i
      change (y ᵥ* (H*J)) (f i) = 0
      rw [hk, Matrix.vecMul_smul, Matrix.vecMul_one, Pi.smul_apply, hz _ hy i, smul_zero]
    rw [hz', zero_dotProduct]
  have d := Submodule.finrank_mono orth
  rw [LinearMap.finrank_range_of_inj inj, Module.finrank_prod, Module.finrank_fin_fun,
    LinearMap.BilinForm.finrank_orthogonal hr, Module.finrank_fin_fun] at d
  have bound (n : ℕ) (h : n + 4 ≤ 17 - n) : n ≤ 6 := by omega
  exact bound _ d

end
end PEqualNP.Research.PermanentTwelveCoordinates

open PEqualNP.Research.PermanentTwelveCoordinates in
theorem PEqualNP.Research.PermanentTwelveCoordinates : ∀ (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ)) (a b c d : Fin 16),
    a < b → b < c → c < d →
    (∀ t ∈ L, ∀ u ∈ ([a,b,c,d] : List (Fin 16)), t (finProdFinEquiv.symm u) = 0) →
    (∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + t (i,j)) = 65) →
    Module.finrank ℂ L ≤ 5 := by
  intro L a b c d hab hbc hcd hz hl
  let f : Fin 4 → Fin 17 := ![a.castSucc,b.castSucc,c.castSucc,d.castSucc]
  let W := (pack L).range
  have hd : (J.submatrix f f).det ≠ 0 := by
    have hm := PEqualNP.Research.PermanentSupportMinors.nonzero a b c d hab hbc hcd
    have hz : (PEqualNP.Research.PermanentSupportMinors.J.submatrix f f).det ≠ 0 := by
      rw [PEqualNP.Research.PermanentSupportMinors.det4_correct]
      exact hm
    change ((Int.castRingHom ℂ).mapMatrix (PEqualNP.Research.PermanentSupportMinors.J.submatrix f f)).det ≠ 0
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr hz
  have pinned : ∀ x ∈ W, ∀ i, x (f i) = 0 := by
    rintro _ ⟨p,rfl⟩ i
    fin_cases i
    · exact (pack_at L p a).trans (hz _ p.1.property a (by simp))
    · exact (pack_at L p b).trans (hz _ p.1.property b (by simp))
    · exact (pack_at L p c).trans (hz _ p.1.property c (by simp))
    · exact (pack_at L p d).trans (hz _ p.1.property d (by simp))
  have diag (x : X) (hx : x ∈ W) : H.toBilin' x x = 0 := by
    obtain ⟨p,rfl⟩ := hx
    rw [diagonal, (moments _ _ hl).1, (moments _ _ hl).2]
    ring
  have iso : W ≤ H.toBilin'.orthogonal W := by
    intro x hx
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    have he := diag (x+y) (W.add_mem hx hy)
    simp only [map_add, LinearMap.add_apply, diag x hx, diag y hy] at he
    linear_combination (he - symmetric.eq x y) / 2
  have hw := codimFour H J _ inverse_certificate regular f hd W pinned iso
  have eqd : Module.finrank ℂ W = Module.finrank ℂ L + 1 := by
    rw [show W = (pack L).range from rfl, LinearMap.finrank_range_of_inj (pack_inj L),
      Module.finrank_prod, Module.finrank_self]
  rw [eqd] at hw
  omega
