import PEqualNP.Research.PlaneFourthCoverage
import PEqualNP.Research.PlaneFourthAndTransfer
import PEqualNP.Research.PlaneSecondMaskAndCount
import PEqualNP.Research.PlaneMaskAndCount
import PEqualNP.Research.PlaneFlagFamilyA
import PEqualNP.Research.PlaneFlagFamilyB

open PEqualNP.Research PEqualNP.Research.PlanePairAndCount PEqualNP.Research.PlaneFourthAndTransfer in
theorem PEqualNP.Research.PlaneAllFourthAndCount : ∀ k : Nat, k < 1682 → ∀ (gs : List Gate) (o : Nat),
    (∀ i : Fin 52, readWire (gs.foldl step (testRow k true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (testRow k false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst := by
  intro k hk gs o hp hn
  rcases PlaneFourthCoverage k hk with ⟨r,hr,same⟩ | first | second | ⟨e,which,off⟩
  · have eq (b : Bool) (i : Nat) : testRow r b i = testRow k b i := by
      simp only [testRow,PlaneFlagOrTail.start,same]
    have h := PlaneFourthAndTransfer r gs o
      (fun i => by rw [eq]; exact hp i) (fun i => by rw [eq]; exact hn i)
    simpa [show ¬841 ≤ r by omega] using h
  · exact PlaneMaskAndCount.2 _ gs o first hp hn
  · exact PlaneSecondMaskAndCount.2 _ gs o second hp hn
  · cases which with
    | inl h => exact PlaneFlagFamilyA _ e gs o h off hp hn
    | inr h => exact PlaneFlagFamilyB _ e gs o h off hp hn
