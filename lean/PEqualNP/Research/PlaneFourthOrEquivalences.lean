import PEqualNP.Research.PlaneFlagOrTail
import PEqualNP.Research.PlanePairAndCount

namespace PEqualNP.Research.PlaneFourthOrEquivalences
open PlanePairAndCount

def pairs : List (Nat × Nat) := [(871, 813), (883, 840), (898, 840), (901, 60), (931, 90), (961, 120), (991, 150), (1021, 180), (1051, 210), (1081, 240), (1111, 270), (1141, 300), (1171, 330), (1201, 360), (1219, 840), (1231, 825), (1246, 840), (1291, 450), (1321, 480), (1351, 510), (1381, 540), (1411, 570), (1441, 600), (1471, 630), (1501, 660), (1531, 690), (1561, 720), (1591, 750), (1654, 840), (1666, 840), (1681, 840)]
def testRow (k : Nat) (pos : Bool) (i : Nat) : Row :=
  (PlaneFlagOrTail.start k).map fun x => if pos then x.1.getLsbD i else x.2.getLsbD i

private theorem signatures : ∀ p ∈ pairs, 841 ≤ p.1 ∧ p.1 < 1682 ∧ p.2 < 841 ∧
    PlaneFlagFourth.gate p.1 [] = PlaneFlagFourth.gate p.2 [] := by decide +kernel

end PEqualNP.Research.PlaneFourthOrEquivalences

open PEqualNP.Research.PlaneFourthOrEquivalences PEqualNP.Research.PlanePairAndCount in
theorem PEqualNP.Research.PlaneFourthOrEquivalences : pairs.length = 31 ∧ (pairs.map Prod.fst).Nodup ∧
    ∀ p ∈ pairs, 841 ≤ p.1 ∧ p.1 < 1682 ∧ p.2 < 841 ∧
    ∀ (gs : List Gate) (o : Nat) (b : Bool) (i : Nat),
    readWire (gs.foldl step (testRow p.1 b i)) o =
    readWire (gs.foldl step (testRow p.2 b i)) o := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro p mem
  obtain ⟨lo,hi,isOr,eq⟩ := signatures p mem
  refine ⟨lo,hi,isOr,?_⟩
  intro gs o b i
  simp only [testRow,PEqualNP.Research.PlaneFlagOrTail.start,eq]
