import PEqualNP.Research.PlaneNonincidentThird

namespace PEqualNP.Research.PlaneCase6And113
open PlaneNonincidentThird

/- Code 825 is AND(1,13) after the two pinned gates of case 6. -/
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem irredundant : 825 ∈ roots ∧
    (∀ i : Fin 28, dominates (col i.val) (gate 825 []) = false) ∧
    (∀ q ∈ roots, ∀ w ∈ words, dominates (gate q w) (gate 825 []) = true → q = 825) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have all : roots.all (fun q => words.all (fun w =>
      !(dominates (gate q w) (gate 825 [])) || q == 825)) = true := by decide +kernel
  intro q hq w hw hd
  have good := Array.all_eq_true_iff_forall_mem.mp
    (Array.all_eq_true_iff_forall_mem.mp all q hq) w hw
  simpa [hd] using good
end PEqualNP.Research.PlaneCase6And113
