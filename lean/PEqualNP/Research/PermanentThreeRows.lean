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

namespace PEqualNP.Research.PermanentThreeRows
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

lemma sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


abbrev T := Fin 4 × Fin 4 → ℂ
abbrev X := Fin 13 → ℂ

def gradient (t : T) : ℂ :=
    16 * t (0,0) +
    16 * t (1,1) +
    16 * t (2,2) +
    11 * t (2,3) +
    11 * t (1,2) +
    11 * t (2,1) +
    11 * t (1,3) +
    11 * t (0,1) +
    11 * t (1,0) +
    11 * t (2,0) +
    11 * t (0,2) +
    11 * t (0,3)

def second (t : T) : ℂ :=
    5 * t (0,0) * t (1,1) +
    5 * t (0,0) * t (2,2) +
    5 * t (1,1) * t (2,2) +
    3 * t (0,0) * t (2,3) +
    3 * t (1,1) * t (2,3) +
    3 * t (0,0) * t (1,2) +
    3 * t (0,0) * t (2,1) +
    5 * t (1,2) * t (2,1) +
    3 * t (1,2) * t (2,3) +
    3 * t (0,0) * t (1,3) +
    3 * t (1,3) * t (2,1) +
    3 * t (1,3) * t (2,2) +
    5 * t (0,1) * t (1,0) +
    3 * t (0,1) * t (2,2) +
    3 * t (1,0) * t (2,2) +
    2 * t (0,1) * t (2,3) +
    2 * t (1,0) * t (2,3) +
    3 * t (0,1) * t (1,2) +
    3 * t (0,1) * t (2,0) +
    3 * t (1,2) * t (2,0) +
    3 * t (0,1) * t (1,3) +
    2 * t (1,3) * t (2,0) +
    3 * t (0,2) * t (1,0) +
    3 * t (0,2) * t (2,1) +
    3 * t (1,0) * t (2,1) +
    3 * t (0,2) * t (2,3) +
    3 * t (0,2) * t (1,1) +
    5 * t (0,2) * t (2,0) +
    3 * t (1,1) * t (2,0) +
    2 * t (0,2) * t (1,3) +
    3 * t (0,3) * t (1,0) +
    2 * t (0,3) * t (2,1) +
    3 * t (0,3) * t (2,2) +
    3 * t (0,3) * t (1,1) +
    3 * t (0,3) * t (2,0) +
    2 * t (0,3) * t (1,2)

def third (t : T) : ℂ :=
    2 * t (0,0) * t (1,1) * t (2,2) +
    t (0,0) * t (1,1) * t (2,3) +
    2 * t (0,0) * t (1,2) * t (2,1) +
    t (0,0) * t (1,2) * t (2,3) +
    t (0,0) * t (1,3) * t (2,1) +
    t (0,0) * t (1,3) * t (2,2) +
    2 * t (0,1) * t (1,0) * t (2,2) +
    t (0,1) * t (1,0) * t (2,3) +
    2 * t (0,1) * t (1,2) * t (2,0) +
    t (0,1) * t (1,2) * t (2,3) +
    t (0,1) * t (1,3) * t (2,0) +
    t (0,1) * t (1,3) * t (2,2) +
    2 * t (0,2) * t (1,0) * t (2,1) +
    t (0,2) * t (1,0) * t (2,3) +
    2 * t (0,2) * t (1,1) * t (2,0) +
    t (0,2) * t (1,1) * t (2,3) +
    t (0,2) * t (1,3) * t (2,0) +
    t (0,2) * t (1,3) * t (2,1) +
    t (0,3) * t (1,0) * t (2,1) +
    t (0,3) * t (1,0) * t (2,2) +
    t (0,3) * t (1,1) * t (2,0) +
    t (0,3) * t (1,1) * t (2,2) +
    t (0,3) * t (1,2) * t (2,0) +
    t (0,3) * t (1,2) * t (2,1)

theorem expansion (t : T) (hz : ∀ j : Fin 4, t (3,j) = 0) (s : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + s * t (i,j)) =
      65 + s * gradient t + s^2 * second t + s^3 * third t := by
  rw [perm4]
  simp +decide only [Matrix.of_apply, ite_true, ite_false, hz, mul_zero, add_zero, gradient, second, third]
  ring

theorem interpolate (a b c : ℂ)
    (he : ∀ s : ℂ, 65 + s*a + s^2*b + s^3*c = 65) : a = 0 ∧ b = 0 := by
  constructor
  · linear_combination (6 * he 1 - 2 * he (-1) - he 2) / 6
  · linear_combination (he 1 + he (-1)) / 2

theorem moments (L : Submodule ℂ T) (t : L) (hz : ∀ j : Fin 4, t.val (3,j) = 0)
    (hl : ∀ u ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + u (i,j)) = 65) :
    gradient t.val = 0 ∧ second t.val = 0 := by
  apply interpolate (gradient t.val) (second t.val) (third t.val)
  intro s
  rw [← expansion t.val hz s]
  exact hl (s • t.val) (L.smul_mem s t.property)

def hessian : Matrix (Fin 13) (Fin 13) ℚ :=
  ![![0, 0, 0, 0, 0, 5, 3, 3, 0, 3, 5, 3, 16], ![0, 0, 0, 0, 5, 0, 3, 3, 3, 0, 3, 2, 11], ![0, 0, 0, 0, 3, 3, 0, 2, 5, 3, 0, 3, 11], ![0, 0, 0, 0, 3, 3, 2, 0, 3, 2, 3, 0, 11], ![0, 5, 3, 3, 0, 0, 0, 0, 0, 3, 3, 2, 11], ![5, 0, 3, 3, 0, 0, 0, 0, 3, 0, 5, 3, 16], ![3, 3, 0, 2, 0, 0, 0, 0, 3, 5, 0, 3, 11], ![3, 3, 2, 0, 0, 0, 0, 0, 2, 3, 3, 0, 11], ![0, 3, 5, 3, 0, 3, 3, 2, 0, 0, 0, 0, 11], ![3, 0, 3, 2, 3, 0, 5, 3, 0, 0, 0, 0, 11], ![5, 3, 0, 3, 3, 5, 0, 3, 0, 0, 0, 0, 16], ![3, 2, 3, 0, 2, 3, 3, 0, 0, 0, 0, 0, 11], ![16, 11, 11, 11, 11, 16, 11, 11, 11, 11, 16, 11, 0]]

def inverse : Matrix (Fin 13) (Fin 13) ℚ :=
  ![![-48913/16879980, -506009/16879980, -506009/16879980, -481447/8439990, -1211519/16879980, 552077/16879980, 513061/16879980, 459233/8439990, -1211519/16879980, 513061/16879980, 552077/16879980, 459233/8439990, 2/195], ![-506009/16879980, 3882263/16879980, -2911537/16879980, -628871/8439990, -1160827/16879980, -1211519/16879980, 2497373/16879980, 468589/8439990, 2497373/16879980, -3930607/16879980, 513061/16879980, 599239/8439990, 1/195], ![-506009/16879980, -2911537/16879980, 3882263/16879980, -628871/8439990, 2497373/16879980, 513061/16879980, -3930607/16879980, 599239/8439990, -1160827/16879980, 2497373/16879980, -1211519/16879980, 468589/8439990, 1/195], ![-481447/8439990, -628871/8439990, -628871/8439990, 723257/4219995, 468589/8439990, 459233/8439990, 599239/8439990, -740023/4219995, 468589/8439990, 599239/8439990, 459233/8439990, -740023/4219995, 1/195], ![-1211519/16879980, -1160827/16879980, 2497373/16879980, 468589/8439990, 3882263/16879980, -506009/16879980, -2911537/16879980, -628871/8439990, -3930607/16879980, 2497373/16879980, 513061/16879980, 599239/8439990, 1/195], ![552077/16879980, -1211519/16879980, 513061/16879980, 459233/8439990, -506009/16879980, -48913/16879980, -506009/16879980, -481447/8439990, 513061/16879980, -1211519/16879980, 552077/16879980, 459233/8439990, 2/195], ![513061/16879980, 2497373/16879980, -3930607/16879980, 599239/8439990, -2911537/16879980, -506009/16879980, 3882263/16879980, -628871/8439990, 2497373/16879980, -1160827/16879980, -1211519/16879980, 468589/8439990, 1/195], ![459233/8439990, 468589/8439990, 599239/8439990, -740023/4219995, -628871/8439990, -481447/8439990, -628871/8439990, 723257/4219995, 599239/8439990, 468589/8439990, 459233/8439990, -740023/4219995, 1/195], ![-1211519/16879980, 2497373/16879980, -1160827/16879980, 468589/8439990, -3930607/16879980, 513061/16879980, 2497373/16879980, 599239/8439990, 3882263/16879980, -2911537/16879980, -506009/16879980, -628871/8439990, 1/195], ![513061/16879980, -3930607/16879980, 2497373/16879980, 599239/8439990, 2497373/16879980, -1211519/16879980, -1160827/16879980, 468589/8439990, -2911537/16879980, 3882263/16879980, -506009/16879980, -628871/8439990, 1/195], ![552077/16879980, 513061/16879980, -1211519/16879980, 459233/8439990, 513061/16879980, 552077/16879980, -1211519/16879980, 459233/8439990, -506009/16879980, -506009/16879980, -48913/16879980, -481447/8439990, 2/195], ![459233/8439990, 599239/8439990, 468589/8439990, -740023/4219995, 599239/8439990, 459233/8439990, 468589/8439990, -740023/4219995, -628871/8439990, -628871/8439990, -481447/8439990, 723257/4219995, 1/195], ![2/195, 1/195, 1/195, 1/195, 1/195, 2/195, 1/195, 1/195, 1/195, 1/195, 2/195, 1/195, -2/195]]

theorem inverse_certificate : hessian * inverse = 1 := by
  apply Matrix.ext
  intro i
  fin_cases i <;> as_aux_lemma => decide +kernel

def form := Matrix.toBilin' (fun i j : Fin 13 => (Rat.castHom ℂ) (hessian i j))

theorem form_regular : form.Nondegenerate := by
  change ((Rat.castHom ℂ).mapMatrix hessian).toBilin'.Nondegenerate
  apply Matrix.Nondegenerate.toBilin'
  apply Matrix.nondegenerate_of_det_ne_zero
  rw [← RingHom.map_det]
  have h := congrArg Matrix.det inverse_certificate
  rw [Matrix.det_mul, Matrix.det_one] at h
  have hn : hessian.det ≠ 0 := by
    intro e
    rw [e, zero_mul] at h
    exact zero_ne_one h
  exact (map_ne_zero (Rat.castHom ℂ)).mpr hn

theorem form_symmetric : form.IsSymm := by
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  have h : hessian.transpose = hessian := by decide +kernel
  exact congrArg (Rat.castHom ℂ).mapMatrix h

def pack (L : Submodule ℂ T) : (L × ℂ) →ₗ[ℂ] X where
  toFun p := ![p.1.val (0,0), p.1.val (0,1), p.1.val (0,2), p.1.val (0,3), p.1.val (1,0), p.1.val (1,1), p.1.val (1,2), p.1.val (1,3), p.1.val (2,0), p.1.val (2,1), p.1.val (2,2), p.1.val (2,3), p.2]
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

theorem pack_inj (L : Submodule ℂ T) (hz : ∀ t ∈ L, ∀ j : Fin 4, t (3,j) = 0) :
    Function.Injective (pack L) := by
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
    all_goals exact (hz _ x.1.property _).trans (hz _ y.1.property _).symm
  · exact congrFun h 12

theorem diagonal (L : Submodule ℂ T) (p : L × ℂ) :
    form (pack L p) (pack L p) = 2 * second p.1.val + 2 * p.2 * gradient p.1.val := by
  calc
    _ = ∑ i : Fin 13, ∑ j : Fin 13, pack L p i * ((Rat.castHom ℂ) (hessian i j)) * pack L p j :=
      Matrix.toBilin'_apply _ _ _
    _ = _ := by
      simp only [hessian, pack, Fin.sum_univ_succ, Fin.sum_univ_zero, gradient, second,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_succ,
        map_zero, map_ofNat, mul_zero, zero_mul, add_zero, zero_add]
      ring

end
end PEqualNP.Research.PermanentThreeRows

theorem PEqualNP.Research.PermanentThreeRows : ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
    (∀ t ∈ L, ∀ j : Fin 4, t (3, j) = 0) →
    (∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      (if i = j then (2 : ℂ) else 1) + t (i, j)) = 65) →
    Module.finrank ℂ L ≤ 5 := by
  intro L hz hl
  let f := PEqualNP.Research.PermanentThreeRows.pack L
  let W := f.range
  let B := PEqualNP.Research.PermanentThreeRows.form
  have diag (x : PEqualNP.Research.PermanentThreeRows.X) (hx : x ∈ W) : B x x = 0 := by
    obtain ⟨p,rfl⟩ := hx
    have h := PEqualNP.Research.PermanentThreeRows.moments L p.1 (hz _ p.1.property) hl
    rw [show B (f p) (f p) = _ from PEqualNP.Research.PermanentThreeRows.diagonal L p, h.1, h.2]
    ring
  have iso : W ≤ B.orthogonal W := by
    intro x hx
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    have h := diag (x+y) (W.add_mem hx hy)
    simp only [map_add, LinearMap.add_apply, diag x hx, diag y hy] at h
    have hs := PEqualNP.Research.PermanentThreeRows.form_symmetric.eq x y
    change B x y = B y x at hs
    linear_combination (h - hs) / 2
  have h := Submodule.finrank_mono iso
  rw [LinearMap.BilinForm.finrank_orthogonal PEqualNP.Research.PermanentThreeRows.form_regular, Module.finrank_fin_fun] at h
  have hw : Module.finrank ℂ W = Module.finrank ℂ L + 1 := by
    rw [show W = (PEqualNP.Research.PermanentThreeRows.pack L).range from rfl, LinearMap.finrank_range_of_inj (PEqualNP.Research.PermanentThreeRows.pack_inj L hz),
      Module.finrank_prod, Module.finrank_self]
  change Module.finrank ℂ W ≤ 13 - Module.finrank ℂ W at h
  rw [hw] at h
  omega
