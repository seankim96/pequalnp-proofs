import PEqualNP.Research.Plane975ResidualOffDiagonal

open PEqualNP.Research.Plane975ResidualSharedMask PEqualNP.Research.Plane975ResidualOffDiagonal PEqualNP.Research.PlaneFirstAndBudget PEqualNP.Research.PlaneFirstAndSeparation in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Research.Plane975FinalResidual : ∀ (k : Nat), k ∈ [32, 55, 64, 87, 96, 128, 141, 160, 172, 192, 256, 273, 288, 320, 352, 480, 531, 532, 544, 745, 768, 777, 783, 800] → ∀ (tail : List Gate) (out : Nat),
    let f := both (wire base (k/31)) (wire base (k%31))
    let final := tail.foldl step (base ++ [f])
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  have cover : ∀ k : Fin 961, k.val ∈ [32, 55, 64, 87, 96, 128, 141, 160, 172, 192, 256, 273, 288, 320, 352, 480, 531, 532, 544, 745, 768, 777, 783, 800] → k.val / 31 = k.val % 31 ∨ k.val ∈ codes := by
    decide +kernel
  intro k hk tail out
  dsimp only
  intro hp hn
  have bound : k < 961 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
  rcases cover ⟨k,bound⟩ hk with same | mem
  · change k / 31 = k % 31 at same
    rw [same] at hp hn
    exact separated_bound _ tail out (diagonalSeparated _) hp hn
  · exact PEqualNP.Research.Plane975ResidualOffDiagonal.2 k mem tail out hp hn
