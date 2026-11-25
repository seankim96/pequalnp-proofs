import PEqualNP.Research.OrderThreePlanePrefixData

namespace PEqualNP.Research.PlaneNonincidentThird
open OrderThreePlanePrefixData
def roots : Array Nat := #[801,825,826,830,854,855,865,881,883,939,941,942,1,2,3,5,13,15,17,18,30,31,33,41,42,43,45,46,54,55,59,60,61,64,69,70,71,72,73,74,81,82,83,89,93,97,98,99,101,102,103,110,111,146,147,151,153,154,155,156,157,158,159,163,164,166,167,378,379,381,382,391,407,409,410,418,436,437,438,439,441,445,446,447,494,499,502,503,528,530,531]
def words : Array (List Nat) := #[[],[0],[1],[2],[0,1],[0,2],[1,2],[2,0],[0,1,2],[0,2,0],[1,2,0],[0,1,2,0]]
private def witnesses : Array (Array Nat) := #[
#[0,40,41,42,314,43,407,225,589,224,678,134,316,44,27,45,318,46,47,227,682,591,955,137,138,319,0,27],
#[40,1,48,49,321,50,414,232,596,231,685,141,323,51,52,53,326,54,55,235,690,599,963,145,146,327,56,57],
#[41,48,2,58,59,60,424,242,61,240,150,151,152,62,63,64,65,66,67,246,156,247,429,157,158,68,69,70],
#[42,49,58,3,331,71,526,890,708,72,695,162,344,73,74,75,348,76,77,78,712,351,715,167,168,349,79,80],
#[314,321,59,331,4,516,515,334,606,604,514,788,333,335,336,338,337,341,522,611,520,610,793,521,340,339,342,343],
#[43,50,60,71,516,5,81,82,718,1072,1061,83,993,84,85,86,87,88,89,90,1091,1088,1087,91,92,1092,93,94],
#[407,414,424,526,515,81,6,265,536,435,698,173,356,448,449,454,541,455,453,450,542,545,451,452,456,546,457,458],
#[225,232,242,890,334,82,265,7,720,253,879,172,900,266,267,272,906,270,274,268,905,269,909,273,271,910,275,276],
#[589,596,61,708,606,718,536,720,8,617,697,629,355,630,631,724,636,728,635,633,723,632,727,637,638,634,639,640],
#[224,231,240,72,604,1072,435,253,617,9,968,799,981,255,256,260,624,258,441,257,988,621,985,440,259,622,261,262],
#[678,685,150,695,514,1061,698,879,697,968,10,880,970,699,700,702,884,885,704,975,701,1066,974,705,886,703,706,707],
#[134,141,151,162,788,83,173,172,629,799,880,11,354,175,176,177,818,182,183,181,178,814,815,179,180,819,184,185],
#[316,323,152,344,333,993,356,900,355,981,970,354,12,357,358,360,359,1001,365,997,1000,363,996,364,362,361,366,367],
#[44,51,62,73,335,84,448,266,630,255,699,175,357,13,95,96,369,97,98,278,733,642,1006,188,189,370,13,99],
#[27,52,63,74,336,85,449,267,631,256,700,176,358,95,14,100,373,101,102,282,737,646,1010,192,193,374,103,27],
#[45,53,64,75,338,86,454,272,724,260,702,177,360,96,100,15,104,105,106,107,195,108,199,196,197,109,110,111],
#[318,326,65,348,337,87,541,906,636,624,884,818,359,369,373,104,16,382,561,290,559,380,563,560,379,378,383,384],
#[46,54,66,76,341,88,455,270,728,258,885,182,1001,97,101,105,382,17,112,287,924,655,1106,113,294,750,114,115],
#[47,55,67,77,522,89,453,274,635,441,704,183,365,98,102,106,561,112,18,470,743,652,1107,476,116,658,117,118],
#[227,235,246,78,611,90,450,268,633,257,975,181,997,278,282,107,290,287,470,19,472,286,468,469,288,291,292,293],
#[682,690,156,712,520,1091,542,905,723,988,701,178,1000,733,737,195,559,924,743,472,20,836,744,746,925,742,747,748],
#[591,599,247,351,610,1088,545,269,632,621,1066,814,363,642,646,108,380,655,652,286,836,21,832,833,834,651,656,657],
#[955,963,429,715,793,1087,451,909,727,985,974,815,996,1006,1010,199,563,1106,1107,468,744,832,22,1019,1016,1015,1020,1021],
#[137,145,157,167,521,91,452,273,637,440,705,179,364,188,192,196,560,113,476,469,746,833,1019,23,203,386,205,206],
#[138,146,158,168,340,92,456,271,638,259,886,180,362,189,193,197,379,294,116,288,925,834,1016,203,24,385,208,209],
#[319,327,68,349,339,1092,546,910,634,622,703,819,361,370,374,109,378,750,658,291,742,651,1015,386,385,25,387,388],
#[0,56,69,79,342,93,457,275,639,261,706,184,366,13,103,110,383,114,117,292,747,656,1020,205,208,387,26,27],
#[27,57,70,80,343,94,458,276,640,262,707,185,367,99,27,111,384,115,118,293,748,657,1021,206,209,388,27,27],
#[0,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,28,26,26,26,26,26,119,26,301,26,0],
#[26,1,26,26,26,26,26,26,26,26,26,26,26,29,30,26,26,26,31,26,26,26,26,26,122,26,26,30],
#[26,26,2,26,26,26,26,26,26,26,26,26,26,26,32,33,26,26,26,215,26,26,26,26,26,34,26,32],
#[26,26,26,3,26,26,26,26,26,26,26,26,26,35,26,36,309,26,26,26,673,26,26,26,26,26,26,26],
#[26,26,26,26,4,26,26,26,26,26,26,26,26,26,305,26,306,307,26,26,26,579,26,26,26,26,26,305],
#[26,26,26,26,26,5,26,26,26,26,26,26,26,26,26,37,26,38,39,26,26,26,1038,26,26,26,26,26],
#[26,26,26,26,26,26,6,26,26,26,26,26,26,26,26,26,492,26,403,401,26,26,26,402,26,26,26,26],
#[26,26,26,26,26,26,26,7,26,26,26,26,26,26,26,26,26,220,26,219,856,26,26,26,221,26,26,26],
#[26,26,26,26,26,26,26,26,8,26,26,26,26,26,26,26,26,26,585,26,674,583,26,26,26,584,26,26],
#[26,26,26,26,26,26,26,26,26,9,26,26,26,217,26,26,26,26,26,218,26,582,946,26,26,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,10,26,26,26,669,26,26,26,26,26,670,26,943,671,26,26,26,669],
#[26,26,26,26,26,26,26,26,26,26,26,11,26,26,26,128,26,26,26,26,26,765,26,129,130,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,26,26,12,26,26,26,310,26,26,26,26,26,947,26,312,311,26,26],
#[26,29,26,35,26,26,26,26,26,217,26,26,26,13,26,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[26,30,32,26,305,26,26,26,26,26,669,26,26,26,14,26,26,26,26,26,26,26,26,26,26,26,26,14],
#[26,26,33,36,26,37,26,26,26,26,26,128,26,26,26,15,26,26,26,26,26,26,26,26,26,26,26,26],
#[26,26,26,309,306,26,492,26,26,26,26,26,310,26,26,26,16,26,26,26,26,26,26,26,26,26,26,26],
#[28,26,26,26,307,38,26,220,26,26,26,26,26,26,26,26,26,17,26,26,26,26,26,26,26,26,26,28],
#[26,31,26,26,26,39,403,26,585,26,26,26,26,26,26,26,26,26,18,26,26,26,26,26,26,26,26,26],
#[26,26,215,26,26,26,401,219,26,218,26,26,26,26,26,26,26,26,26,19,26,26,26,26,26,26,26,26],
#[26,26,26,673,26,26,26,856,674,26,670,26,26,26,26,26,26,26,26,26,20,26,26,26,26,26,26,26],
#[26,26,26,26,579,26,26,26,583,582,26,765,26,26,26,26,26,26,26,26,26,21,26,26,26,26,26,26],
#[26,26,26,26,26,1038,26,26,26,946,943,26,947,26,26,26,26,26,26,26,26,26,22,26,26,26,26,26],
#[119,26,26,26,26,26,402,26,26,26,671,129,26,26,26,26,26,26,26,26,26,26,26,23,26,26,26,119],
#[26,122,26,26,26,26,26,221,26,26,26,130,312,26,26,26,26,26,26,26,26,26,26,26,24,26,26,26],
#[301,26,34,26,26,26,26,26,584,26,26,26,311,26,26,26,26,26,26,26,26,26,26,26,26,25,26,301],
#[26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[0,30,32,26,305,26,26,26,26,26,669,26,26,26,14,26,26,28,26,26,26,26,26,119,26,301,26,27]
]

def ren (ks : List Nat) (i : Nat) := ks.foldl (fun j k => (stage1.permutations[k]!).getD j j) i
def col (i : Nat) : Signature :=
  let a := rawColumns[0]!
  let b := rawColumns[13]!
  if i == 26 then (a.1 &&& b.1,a.2 &&& b.2)
  else if i == 27 then (a.1 ||| rawColumns[14]!.1,a.2 ||| rawColumns[14]!.2)
  else rawColumns[i]!

def gate (k : Nat) (ks : List Nat) : Signature :=
  let a := col (ren ks ((k / 28) % 28))
  let b := col (ren ks (k % 28))
  if 784 ≤ k then (a.1 &&& b.1,a.2 &&& b.2) else (a.1 ||| b.1,a.2 ||| b.2)

def dominates (a b : Signature) : Bool :=
  (a.1 &&& b.1 == b.1) && (a.2 &&& b.2 == a.2)

def good (k : Nat) : Bool :=
  let w := (witnesses[k/28]!)[k%28]!
  if w < 28 then dominates (col w) (gate k [])
  else
    let r := (w-28)%91
    let i := (w-28)/91
    decide (r < roots.size ∧ i < words.size) &&
      dominates (gate roots[r]! words[i]!) (gate k [])

set_option maxRecDepth 4096 in
private theorem row0 : ∀ j : Fin 28, good (0*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row1 : ∀ j : Fin 28, good (1*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row2 : ∀ j : Fin 28, good (2*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row3 : ∀ j : Fin 28, good (3*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row4 : ∀ j : Fin 28, good (4*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row5 : ∀ j : Fin 28, good (5*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row6 : ∀ j : Fin 28, good (6*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row7 : ∀ j : Fin 28, good (7*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row8 : ∀ j : Fin 28, good (8*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row9 : ∀ j : Fin 28, good (9*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row10 : ∀ j : Fin 28, good (10*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row11 : ∀ j : Fin 28, good (11*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row12 : ∀ j : Fin 28, good (12*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row13 : ∀ j : Fin 28, good (13*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row14 : ∀ j : Fin 28, good (14*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row15 : ∀ j : Fin 28, good (15*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row16 : ∀ j : Fin 28, good (16*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row17 : ∀ j : Fin 28, good (17*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row18 : ∀ j : Fin 28, good (18*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row19 : ∀ j : Fin 28, good (19*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row20 : ∀ j : Fin 28, good (20*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row21 : ∀ j : Fin 28, good (21*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row22 : ∀ j : Fin 28, good (22*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row23 : ∀ j : Fin 28, good (23*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row24 : ∀ j : Fin 28, good (24*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row25 : ∀ j : Fin 28, good (25*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row26 : ∀ j : Fin 28, good (26*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row27 : ∀ j : Fin 28, good (27*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row28 : ∀ j : Fin 28, good (28*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row29 : ∀ j : Fin 28, good (29*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row30 : ∀ j : Fin 28, good (30*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row31 : ∀ j : Fin 28, good (31*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row32 : ∀ j : Fin 28, good (32*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row33 : ∀ j : Fin 28, good (33*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row34 : ∀ j : Fin 28, good (34*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row35 : ∀ j : Fin 28, good (35*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row36 : ∀ j : Fin 28, good (36*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row37 : ∀ j : Fin 28, good (37*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row38 : ∀ j : Fin 28, good (38*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row39 : ∀ j : Fin 28, good (39*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row40 : ∀ j : Fin 28, good (40*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row41 : ∀ j : Fin 28, good (41*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row42 : ∀ j : Fin 28, good (42*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row43 : ∀ j : Fin 28, good (43*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row44 : ∀ j : Fin 28, good (44*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row45 : ∀ j : Fin 28, good (45*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row46 : ∀ j : Fin 28, good (46*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row47 : ∀ j : Fin 28, good (47*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row48 : ∀ j : Fin 28, good (48*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row49 : ∀ j : Fin 28, good (49*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row50 : ∀ j : Fin 28, good (50*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row51 : ∀ j : Fin 28, good (51*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row52 : ∀ j : Fin 28, good (52*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row53 : ∀ j : Fin 28, good (53*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row54 : ∀ j : Fin 28, good (54*28+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row55 : ∀ j : Fin 28, good (55*28+j.val) = true := by decide +kernel

private theorem checkRange (k : Nat) (h : k < 1568) : good k = true := by
  have cover (i : Fin 56) : ∀ j : Fin 28, good (i.val*28+j.val) = true := by
    match i with
    | ⟨0,_⟩ => exact row0
    | ⟨1,_⟩ => exact row1
    | ⟨2,_⟩ => exact row2
    | ⟨3,_⟩ => exact row3
    | ⟨4,_⟩ => exact row4
    | ⟨5,_⟩ => exact row5
    | ⟨6,_⟩ => exact row6
    | ⟨7,_⟩ => exact row7
    | ⟨8,_⟩ => exact row8
    | ⟨9,_⟩ => exact row9
    | ⟨10,_⟩ => exact row10
    | ⟨11,_⟩ => exact row11
    | ⟨12,_⟩ => exact row12
    | ⟨13,_⟩ => exact row13
    | ⟨14,_⟩ => exact row14
    | ⟨15,_⟩ => exact row15
    | ⟨16,_⟩ => exact row16
    | ⟨17,_⟩ => exact row17
    | ⟨18,_⟩ => exact row18
    | ⟨19,_⟩ => exact row19
    | ⟨20,_⟩ => exact row20
    | ⟨21,_⟩ => exact row21
    | ⟨22,_⟩ => exact row22
    | ⟨23,_⟩ => exact row23
    | ⟨24,_⟩ => exact row24
    | ⟨25,_⟩ => exact row25
    | ⟨26,_⟩ => exact row26
    | ⟨27,_⟩ => exact row27
    | ⟨28,_⟩ => exact row28
    | ⟨29,_⟩ => exact row29
    | ⟨30,_⟩ => exact row30
    | ⟨31,_⟩ => exact row31
    | ⟨32,_⟩ => exact row32
    | ⟨33,_⟩ => exact row33
    | ⟨34,_⟩ => exact row34
    | ⟨35,_⟩ => exact row35
    | ⟨36,_⟩ => exact row36
    | ⟨37,_⟩ => exact row37
    | ⟨38,_⟩ => exact row38
    | ⟨39,_⟩ => exact row39
    | ⟨40,_⟩ => exact row40
    | ⟨41,_⟩ => exact row41
    | ⟨42,_⟩ => exact row42
    | ⟨43,_⟩ => exact row43
    | ⟨44,_⟩ => exact row44
    | ⟨45,_⟩ => exact row45
    | ⟨46,_⟩ => exact row46
    | ⟨47,_⟩ => exact row47
    | ⟨48,_⟩ => exact row48
    | ⟨49,_⟩ => exact row49
    | ⟨50,_⟩ => exact row50
    | ⟨51,_⟩ => exact row51
    | ⟨52,_⟩ => exact row52
    | ⟨53,_⟩ => exact row53
    | ⟨54,_⟩ => exact row54
    | ⟨55,_⟩ => exact row55
    | ⟨n+56,hn⟩ => omega
  have eq : k/28*28 + k%28 = k := by omega
  simpa only [eq] using cover ⟨k/28,by omega⟩ ⟨k%28,by omega⟩

theorem sound (k : Nat) (hk : k < 1568) :
    (∃ i < 28, dominates (col i) (gate k []) = true) ∨
    ∃ r ∈ roots, ∃ ks ∈ words, dominates (gate r ks) (gate k []) = true := by
  have h := checkRange k hk
  unfold good at h
  dsimp only at h
  split at h
  next hw => exact Or.inl ⟨_,hw,h⟩
  next hw =>
    obtain ⟨bounds,better⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hr,hi⟩ := of_decide_eq_true bounds
    exact Or.inr ⟨_,by simpa [hr] using (Array.getElem_mem (xs := roots) hr),_,
      by simpa [hi] using (Array.getElem_mem (xs := words) hi),better⟩

theorem certificate_size : roots.size = 91 ∧ roots.toList.Nodup ∧
    words.all (fun ks => ks.all (fun i => i < 6)) = true := by decide +kernel
end PEqualNP.Research.PlaneNonincidentThird

open PEqualNP.Research.PlaneNonincidentThird in
theorem PEqualNP.Research.PlaneNonincidentThird :
    ∀ k : Nat, k < 1568 →
      (∃ i < 28, dominates (col i) (gate k []) = true) ∨
      ∃ r ∈ roots, ∃ ks : List Nat, (∀ i ∈ ks, i < 6) ∧ ren ks 0 = 0 ∧ ren ks 14 = 14 ∧
        dominates (gate r ks) (gate k []) = true := by
  have fixed : words.all (fun ks => ren ks 0 == 0 && ren ks 14 == 14) = true := by decide +kernel
  intro k hk
  rcases sound k hk with old|⟨r,hr,ks,hw,hd⟩
  · exact Or.inl old
  · have goodWord := Array.all_eq_true_iff_forall_mem.mp certificate_size.2.2 ks hw
    obtain ⟨f0,f14⟩ := Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp fixed ks hw)
    exact Or.inr ⟨r,hr,ks,fun i hi => of_decide_eq_true (List.all_eq_true.mp goodWord i hi),beq_iff_eq.mp f0,beq_iff_eq.mp f14,hd⟩
