import Std.Tactic.BVDecide
import Mathlib.Data.List.Basic
import PEqualNP.Defs.LratEncoding

/-! The padding branch for 24 gate slots in the punctured Fano instance. A
112-clause subsequence of the pinned CNF already has no model. The sublist
and Boolean contradiction are both checked by Lean's kernel. -/

namespace PEqualNP.Research.PuncturedFanoPadding
open PEqualNP.Defs.LratEncoding

def yes : List ℕ := [130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208]
def no : List ℕ := [127,129,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]

def core : List (List ℕ) := [
  [755464],
  [7,2463706],
  [32853,2496552],
  [65699,2529398],
  [98545,2562244],
  [131391,2595090],
  [164237,2627936],
  [197083,2660782],
  [229929,2693628],
  [262775,2726474],
  [295621,2759320],
  [328467,2792166],
  [361313,2825012],
  [394159,2857858],
  [427005,2890704],
  [459851,2923550],
  [492697,2956396],
  [525543,2989242],
  [558389,3022088],
  [591235,3054934],
  [624081,3087780],
  [656927,3120626],
  [689773,3153472],
  [722619,3186318],
  [755465,3219164],
  [4926902,4926904,4926906,4926908,4926910,4926912,4926914,4926916,4926918,4926920,4926922,4926924,4926926,4926928,4926930,4926932,4926934,4926936,4926938,4926940,4926942,4926944,4926946,4926948,4926950,4926952,4926954,4926956,4926958,4926960,4926962,4926964,4926966,4926968,4926970,4926972,4926974,4926976,4926978],
  [4926903],
  [4926907],
  [4926909],
  [4926911],
  [4926913],
  [4926915],
  [4926919],
  [4926921],
  [4926923],
  [4926925],
  [4926927],
  [4926929],
  [4926979],
  [4926905],
  [4926917],
  [4926931,2463707],
  [4926933,2496553],
  [4926935,2529399],
  [4926937,2562245],
  [4926939,2595091],
  [4926941,2627937],
  [4926943,2660783],
  [4926945,2693629],
  [4926947,2726475],
  [4926949,2759321],
  [4926951,2792167],
  [4926953,2825013],
  [4926955,2857859],
  [4926957,2890705],
  [4926959,2923551],
  [4926961,2956397],
  [4926963,2989243],
  [4926965,3022089],
  [4926967,3054935],
  [4926969,3087781],
  [4926971,3120627],
  [4926973,3153473],
  [4926975,3186319],
  [4926977,3219165],
  [4926976,6503510],
  [5748053,6],
  [5780899,32852],
  [5813745,65698],
  [5846591,98544],
  [5879437,131390],
  [5912283,164236],
  [5945129,197082],
  [5977975,229928],
  [6010821,262774],
  [6043667,295620],
  [6076513,328466],
  [6109359,361312],
  [6142205,394158],
  [6175051,427004],
  [6207897,459850],
  [6240743,492696],
  [6273589,525542],
  [6306435,558388],
  [6339281,591234],
  [6372127,624080],
  [6404973,656926],
  [6437819,689772],
  [6470665,722618],
  [5780899,5748052],
  [5813745,5780898],
  [5846591,5813744],
  [5879437,5846590],
  [5912283,5879436],
  [5945129,5912282],
  [5977975,5945128],
  [6010821,5977974],
  [6043667,6010820],
  [6076513,6043666],
  [6109359,6076512],
  [6142205,6109358],
  [6175051,6142204],
  [6207897,6175050],
  [6240743,6207896],
  [6273589,6240742],
  [6306435,6273588],
  [6339281,6306434],
  [6372127,6339280],
  [6404973,6372126],
  [6437819,6404972],
  [6470665,6437818],
  [6503511,6470664]]

private def fragment : List (List ℕ) :=
  [P (ix 14 24 0 23 2)] :: (fGate 14 24 [127] ++ fOutAlo 14 24 ++
    fOutEq 14 24 (fun r => yes.contains r) (yes ++ [127]) ++ fOut 14 24 ++ fPad 14 24 ++ fPre 14 24)

set_option maxRecDepth 20000 in
private theorem inFragment : core.Sublist fragment := by decide +kernel

private theorem part {c : List ℕ} (hc : c ∈ core) :
    c ∈ [P (ix 14 24 0 23 2)] :: enc 14 24 (fun r => yes.contains r) (yes ++ no) := by
  have h := inFragment.subset hc
  have root : 127 ∈ yes ++ no := List.mem_append_right _ (show 127 ∈ no from by decide +kernel)
  have subset : ∀ r ∈ yes ++ [127], r ∈ yes ++ no := by
    intro r hr
    rcases List.mem_append.mp hr with hr|hr
    · exact List.mem_append_left _ hr
    · exact (List.mem_singleton.mp hr) ▸ root
  have gate : c ∈ fGate 14 24 [127] → c ∈ fGate 14 24 (yes++no) := by
    intro hc
    obtain ⟨j,hj,hh⟩ := List.mem_flatMap.mp hc
    obtain ⟨r,hr,atR⟩ := List.mem_flatMap.mp hh
    exact List.mem_flatMap.mpr ⟨j,hj,List.mem_flatMap.mpr ⟨r,(List.mem_singleton.mp hr) ▸ root,atR⟩⟩
  have out : c ∈ fOutEq 14 24 (fun r => yes.contains r) (yes++[127]) →
      c ∈ fOutEq 14 24 (fun r => yes.contains r) (yes++no) := by
    intro hc
    obtain ⟨r,hr,atR⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨r,subset r hr,atR⟩
  simp only [fragment,List.mem_cons,List.mem_append] at h
  simp only [enc,List.mem_cons,List.mem_append]
  rcases h with u | (((((g|a)|o)|t)|d)|p)
  · exact Or.inl u
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (gate g))))))))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr a))))))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (out o))))))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr t))))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr d)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr p))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
private theorem clash (a : ℕ → Bool) (all : ∀ c ∈ core, ClauseSat a c) : False := by
  have h : core.all (fun c => c.any (litVal a)) = true :=
    List.all_eq_true.mpr (fun c hc => List.any_eq_true.mpr (all c hc))
  simp only [core,List.all_cons,List.all_nil,List.any_cons,List.any_nil] at h
  change (((a 377732 == true) || false) &&
     (((a 3 == false) || ((a 1231853 == true) || false)) &&
     (((a 16426 == false) || ((a 1248276 == true) || false)) &&
     (((a 32849 == false) || ((a 1264699 == true) || false)) &&
     (((a 49272 == false) || ((a 1281122 == true) || false)) &&
     (((a 65695 == false) || ((a 1297545 == true) || false)) &&
     (((a 82118 == false) || ((a 1313968 == true) || false)) &&
     (((a 98541 == false) || ((a 1330391 == true) || false)) &&
     (((a 114964 == false) || ((a 1346814 == true) || false)) &&
     (((a 131387 == false) || ((a 1363237 == true) || false)) &&
     (((a 147810 == false) || ((a 1379660 == true) || false)) &&
     (((a 164233 == false) || ((a 1396083 == true) || false)) &&
     (((a 180656 == false) || ((a 1412506 == true) || false)) &&
     (((a 197079 == false) || ((a 1428929 == true) || false)) &&
     (((a 213502 == false) || ((a 1445352 == true) || false)) &&
     (((a 229925 == false) || ((a 1461775 == true) || false)) &&
     (((a 246348 == false) || ((a 1478198 == true) || false)) &&
     (((a 262771 == false) || ((a 1494621 == true) || false)) &&
     (((a 279194 == false) || ((a 1511044 == true) || false)) &&
     (((a 295617 == false) || ((a 1527467 == true) || false)) &&
     (((a 312040 == false) || ((a 1543890 == true) || false)) &&
     (((a 328463 == false) || ((a 1560313 == true) || false)) &&
     (((a 344886 == false) || ((a 1576736 == true) || false)) &&
     (((a 361309 == false) || ((a 1593159 == true) || false)) &&
     (((a 377732 == false) || ((a 1609582 == true) || false)) &&
     (((a 2463451 == true) || ((a 2463452 == true) || ((a 2463453 == true) || ((a 2463454 == true) || ((a 2463455 == true) || ((a 2463456 == true) || ((a 2463457 == true) || ((a 2463458 == true) || ((a 2463459 == true) || ((a 2463460 == true) || ((a 2463461 == true) || ((a 2463462 == true) || ((a 2463463 == true) || ((a 2463464 == true) || ((a 2463465 == true) || ((a 2463466 == true) || ((a 2463467 == true) || ((a 2463468 == true) || ((a 2463469 == true) || ((a 2463470 == true) || ((a 2463471 == true) || ((a 2463472 == true) || ((a 2463473 == true) || ((a 2463474 == true) || ((a 2463475 == true) || ((a 2463476 == true) || ((a 2463477 == true) || ((a 2463478 == true) || ((a 2463479 == true) || ((a 2463480 == true) || ((a 2463481 == true) || ((a 2463482 == true) || ((a 2463483 == true) || ((a 2463484 == true) || ((a 2463485 == true) || ((a 2463486 == true) || ((a 2463487 == true) || ((a 2463488 == true) || ((a 2463489 == true) || false))))))))))))))))))))))))))))))))))))))) &&
     (((a 2463451 == false) || false) &&
     (((a 2463453 == false) || false) &&
     (((a 2463454 == false) || false) &&
     (((a 2463455 == false) || false) &&
     (((a 2463456 == false) || false) &&
     (((a 2463457 == false) || false) &&
     (((a 2463459 == false) || false) &&
     (((a 2463460 == false) || false) &&
     (((a 2463461 == false) || false) &&
     (((a 2463462 == false) || false) &&
     (((a 2463463 == false) || false) &&
     (((a 2463464 == false) || false) &&
     (((a 2463489 == false) || false) &&
     (((a 2463452 == false) || false) &&
     (((a 2463458 == false) || false) &&
     (((a 2463465 == false) || ((a 1231853 == false) || false)) &&
     (((a 2463466 == false) || ((a 1248276 == false) || false)) &&
     (((a 2463467 == false) || ((a 1264699 == false) || false)) &&
     (((a 2463468 == false) || ((a 1281122 == false) || false)) &&
     (((a 2463469 == false) || ((a 1297545 == false) || false)) &&
     (((a 2463470 == false) || ((a 1313968 == false) || false)) &&
     (((a 2463471 == false) || ((a 1330391 == false) || false)) &&
     (((a 2463472 == false) || ((a 1346814 == false) || false)) &&
     (((a 2463473 == false) || ((a 1363237 == false) || false)) &&
     (((a 2463474 == false) || ((a 1379660 == false) || false)) &&
     (((a 2463475 == false) || ((a 1396083 == false) || false)) &&
     (((a 2463476 == false) || ((a 1412506 == false) || false)) &&
     (((a 2463477 == false) || ((a 1428929 == false) || false)) &&
     (((a 2463478 == false) || ((a 1445352 == false) || false)) &&
     (((a 2463479 == false) || ((a 1461775 == false) || false)) &&
     (((a 2463480 == false) || ((a 1478198 == false) || false)) &&
     (((a 2463481 == false) || ((a 1494621 == false) || false)) &&
     (((a 2463482 == false) || ((a 1511044 == false) || false)) &&
     (((a 2463483 == false) || ((a 1527467 == false) || false)) &&
     (((a 2463484 == false) || ((a 1543890 == false) || false)) &&
     (((a 2463485 == false) || ((a 1560313 == false) || false)) &&
     (((a 2463486 == false) || ((a 1576736 == false) || false)) &&
     (((a 2463487 == false) || ((a 1593159 == false) || false)) &&
     (((a 2463488 == false) || ((a 1609582 == false) || false)) &&
     (((a 2463488 == true) || ((a 3251755 == true) || false)) &&
     (((a 2874026 == false) || ((a 3 == true) || false)) &&
     (((a 2890449 == false) || ((a 16426 == true) || false)) &&
     (((a 2906872 == false) || ((a 32849 == true) || false)) &&
     (((a 2923295 == false) || ((a 49272 == true) || false)) &&
     (((a 2939718 == false) || ((a 65695 == true) || false)) &&
     (((a 2956141 == false) || ((a 82118 == true) || false)) &&
     (((a 2972564 == false) || ((a 98541 == true) || false)) &&
     (((a 2988987 == false) || ((a 114964 == true) || false)) &&
     (((a 3005410 == false) || ((a 131387 == true) || false)) &&
     (((a 3021833 == false) || ((a 147810 == true) || false)) &&
     (((a 3038256 == false) || ((a 164233 == true) || false)) &&
     (((a 3054679 == false) || ((a 180656 == true) || false)) &&
     (((a 3071102 == false) || ((a 197079 == true) || false)) &&
     (((a 3087525 == false) || ((a 213502 == true) || false)) &&
     (((a 3103948 == false) || ((a 229925 == true) || false)) &&
     (((a 3120371 == false) || ((a 246348 == true) || false)) &&
     (((a 3136794 == false) || ((a 262771 == true) || false)) &&
     (((a 3153217 == false) || ((a 279194 == true) || false)) &&
     (((a 3169640 == false) || ((a 295617 == true) || false)) &&
     (((a 3186063 == false) || ((a 312040 == true) || false)) &&
     (((a 3202486 == false) || ((a 328463 == true) || false)) &&
     (((a 3218909 == false) || ((a 344886 == true) || false)) &&
     (((a 3235332 == false) || ((a 361309 == true) || false)) &&
     (((a 2890449 == false) || ((a 2874026 == true) || false)) &&
     (((a 2906872 == false) || ((a 2890449 == true) || false)) &&
     (((a 2923295 == false) || ((a 2906872 == true) || false)) &&
     (((a 2939718 == false) || ((a 2923295 == true) || false)) &&
     (((a 2956141 == false) || ((a 2939718 == true) || false)) &&
     (((a 2972564 == false) || ((a 2956141 == true) || false)) &&
     (((a 2988987 == false) || ((a 2972564 == true) || false)) &&
     (((a 3005410 == false) || ((a 2988987 == true) || false)) &&
     (((a 3021833 == false) || ((a 3005410 == true) || false)) &&
     (((a 3038256 == false) || ((a 3021833 == true) || false)) &&
     (((a 3054679 == false) || ((a 3038256 == true) || false)) &&
     (((a 3071102 == false) || ((a 3054679 == true) || false)) &&
     (((a 3087525 == false) || ((a 3071102 == true) || false)) &&
     (((a 3103948 == false) || ((a 3087525 == true) || false)) &&
     (((a 3120371 == false) || ((a 3103948 == true) || false)) &&
     (((a 3136794 == false) || ((a 3120371 == true) || false)) &&
     (((a 3153217 == false) || ((a 3136794 == true) || false)) &&
     (((a 3169640 == false) || ((a 3153217 == true) || false)) &&
     (((a 3186063 == false) || ((a 3169640 == true) || false)) &&
     (((a 3202486 == false) || ((a 3186063 == true) || false)) &&
     (((a 3218909 == false) || ((a 3202486 == true) || false)) &&
     (((a 3235332 == false) || ((a 3218909 == true) || false)) &&
     (((a 3251755 == false) || ((a 3235332 == true) || false)) &&
     true)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = true at h
  clear all
  bv_decide

theorem padding_unsat : ¬ FormulaSat ([P (ix 14 24 0 23 2)] :: enc 14 24 (fun r => yes.contains r) (yes ++ no)) := by
  rintro ⟨a,sat⟩
  exact clash a (fun c hc => sat c (part hc))

end PEqualNP.Research.PuncturedFanoPadding
