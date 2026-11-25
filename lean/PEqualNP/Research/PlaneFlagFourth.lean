import PEqualNP.Research.OrderThreePlanePrefixData

namespace PEqualNP.Research.PlaneFlagFourth
open OrderThreePlanePrefixData
def roots : Array Nat := #[1,2,3,5,13,15,17,18,28,31,32,34,42,43,44,46,47,55,56,61,62,63,66,71,72,73,74,75,76,83,84,85,86,92,96,100,101,102,104,105,106,113,114,115,151,152,156,158,159,160,161,162,163,164,168,169,171,172,173,391,392,394,395,404,421,423,424,432,434,451,452,453,454,456,460,461,462,463,511,516,519,520,521,546,548,549,550,782,811,858,884,888,913,914,924,941,943,1001,1003,1004]
def words : Array (List Nat) := #[[],[0],[1],[2],[0, 1],[0, 2],[1, 2],[2, 0],[0, 1, 2],[0, 2, 0],[1, 2, 0],[0, 1, 2, 0]]
private def witnesses : Array (Array Nat) := #[
#[0,29,30,31,330,32,432,232,632,231,730,132,332,33,27,34,334,35,36,234,734,634,1034,135,136,335,0,27,37],
#[29,1,38,39,338,40,440,240,640,239,738,140,340,41,42,43,343,44,45,243,743,643,1043,144,145,344,46,47,1],
#[30,38,2,48,49,50,450,250,51,248,149,150,151,52,53,54,55,56,57,254,155,255,455,156,157,58,59,60,61],
#[31,39,48,3,348,62,562,962,762,63,748,162,362,64,65,66,366,67,68,69,766,369,769,167,168,367,70,71,72],
#[330,338,49,348,4,551,550,351,650,648,549,850,350,352,353,355,354,358,557,655,555,654,855,556,357,356,359,360,361],
#[32,40,50,62,551,5,73,74,773,1162,1150,75,1075,76,77,78,79,80,81,82,1182,1179,1178,83,84,1183,85,86,87],
#[432,440,450,562,550,73,6,275,573,462,751,174,375,476,477,482,578,483,481,478,579,582,479,480,484,583,485,486,487],
#[232,240,250,962,351,74,275,7,775,262,950,173,973,276,277,282,979,280,284,278,978,279,982,283,281,983,285,286,287],
#[632,640,51,762,650,773,573,775,8,662,750,675,374,676,677,779,682,783,681,679,778,678,782,683,684,680,685,686,687],
#[231,239,248,63,648,1162,462,262,662,9,1048,862,1062,264,265,269,669,267,468,266,1069,666,1066,467,268,667,270,271,272],
#[730,738,149,748,549,1150,751,950,750,1048,10,951,1050,752,753,755,955,956,757,1055,754,1155,1054,758,957,756,759,760,761],
#[132,140,150,162,850,75,174,173,675,862,951,11,373,176,177,178,882,183,184,182,179,878,879,180,181,883,185,186,187],
#[332,340,151,362,350,1075,375,973,374,1062,1050,373,12,376,377,379,378,1083,384,1079,1082,382,1078,383,381,380,385,386,387],
#[33,41,52,64,352,76,476,276,676,264,752,176,376,13,88,89,389,90,91,289,789,689,1089,190,191,390,13,92,13],
#[27,42,53,65,353,77,477,277,677,265,753,177,377,88,14,93,393,94,95,293,793,693,1093,194,195,394,96,27,97],
#[34,43,54,66,355,78,482,282,779,269,755,178,379,89,93,15,98,99,100,101,198,102,202,199,200,103,104,105,106],
#[334,343,55,366,354,79,578,979,682,669,955,882,378,389,393,98,16,403,600,302,598,401,602,599,400,399,404,405,406],
#[35,44,56,67,358,80,483,280,783,267,956,183,1083,90,94,99,403,17,107,299,999,703,1199,108,307,808,109,110,111],
#[36,45,57,68,557,81,481,284,681,468,757,184,384,91,95,100,600,107,18,500,800,700,1200,507,112,707,113,114,115],
#[234,243,254,69,655,82,478,278,679,266,1055,182,1079,289,293,101,302,299,500,19,502,298,498,499,300,303,304,305,306],
#[734,743,155,766,555,1182,579,978,778,1069,754,179,1082,789,793,198,598,999,800,502,20,902,801,803,1000,799,804,805,806],
#[634,643,255,369,654,1179,582,279,678,666,1155,878,382,689,693,102,401,703,700,298,902,21,898,899,900,699,704,705,706],
#[1034,1043,455,769,855,1178,479,982,782,1066,1054,879,1078,1089,1093,202,602,1199,1200,498,801,898,22,1103,1100,1099,1104,1105,1106],
#[135,144,156,167,556,83,480,283,683,467,758,180,383,190,194,199,599,108,507,499,803,899,1103,23,207,408,209,210,211],
#[136,145,157,168,357,84,484,281,684,268,957,181,381,191,195,200,400,307,112,300,1000,900,1100,207,24,407,213,214,215],
#[335,344,58,367,356,1183,583,983,680,667,756,883,380,390,394,103,399,808,707,303,799,699,1099,408,407,25,409,410,411],
#[0,46,59,70,359,85,485,285,685,270,759,185,385,13,96,104,404,109,113,304,804,704,1104,209,213,409,26,27,116],
#[27,47,60,71,360,86,486,286,686,271,760,186,386,92,27,105,405,110,114,305,805,705,1105,210,214,410,27,27,117],
#[37,1,61,72,361,87,487,287,687,272,761,187,387,13,97,106,406,111,115,306,806,706,1106,211,215,411,116,117,28],
#[0,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,118,26,26,26,26,26,218,26,418,26,0,26],
#[26,1,26,26,26,26,26,26,26,26,26,26,26,28,119,26,26,26,120,26,26,26,26,26,220,26,26,119,28],
#[26,26,2,26,26,26,26,26,26,26,26,26,26,26,121,122,26,26,26,322,26,26,26,26,26,123,26,121,26],
#[26,26,26,3,26,26,26,26,26,26,26,26,26,124,26,125,425,26,26,26,825,26,26,26,26,26,26,26,26],
#[26,26,26,26,4,26,26,26,26,26,26,26,26,26,421,26,422,423,26,26,26,722,26,26,26,26,26,421,26],
#[26,26,26,26,26,5,26,26,26,26,26,26,26,26,26,126,26,127,128,26,26,26,1226,26,26,26,26,26,26],
#[26,26,26,26,26,26,6,26,26,26,26,26,26,26,26,26,626,26,528,526,26,26,26,527,26,26,26,26,26],
#[26,26,26,26,26,26,26,7,26,26,26,26,26,26,26,26,26,327,26,326,1026,26,26,26,328,26,26,26,26],
#[26,26,26,26,26,26,26,26,8,26,26,26,26,26,26,26,26,26,728,26,826,726,26,26,26,727,26,26,26],
#[26,26,26,26,26,26,26,26,26,9,26,26,26,324,26,26,26,26,26,325,26,725,1125,26,26,26,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,10,26,26,26,821,26,26,26,26,26,822,26,1122,823,26,26,26,821,26],
#[26,26,26,26,26,26,26,26,26,26,26,11,26,26,26,226,26,26,26,26,26,926,26,227,228,26,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,26,26,12,26,26,26,426,26,26,26,26,26,1126,26,428,427,26,26,26],
#[26,28,26,124,26,26,26,26,26,324,26,26,26,13,26,26,26,26,26,26,26,26,26,26,26,26,26,26,28],
#[26,119,121,26,421,26,26,26,26,26,821,26,26,26,14,26,26,26,26,26,26,26,26,26,26,26,26,14,26],
#[26,26,122,125,26,126,26,26,26,26,26,226,26,26,26,15,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[26,26,26,425,422,26,626,26,26,26,26,26,426,26,26,26,16,26,26,26,26,26,26,26,26,26,26,26,26],
#[118,26,26,26,423,127,26,327,26,26,26,26,26,26,26,26,26,17,26,26,26,26,26,26,26,26,26,118,26],
#[26,120,26,26,26,128,528,26,728,26,26,26,26,26,26,26,26,26,18,26,26,26,26,26,26,26,26,26,26],
#[26,26,322,26,26,26,526,326,26,325,26,26,26,26,26,26,26,26,26,19,26,26,26,26,26,26,26,26,26],
#[26,26,26,825,26,26,26,1026,826,26,822,26,26,26,26,26,26,26,26,26,20,26,26,26,26,26,26,26,26],
#[26,26,26,26,722,26,26,26,726,725,26,926,26,26,26,26,26,26,26,26,26,21,26,26,26,26,26,26,26],
#[26,26,26,26,26,1226,26,26,26,1125,1122,26,1126,26,26,26,26,26,26,26,26,26,22,26,26,26,26,26,26],
#[218,26,26,26,26,26,527,26,26,26,823,227,26,26,26,26,26,26,26,26,26,26,26,23,26,26,26,218,26],
#[26,220,26,26,26,26,26,328,26,26,26,228,428,26,26,26,26,26,26,26,26,26,26,26,24,26,26,26,26],
#[418,26,123,26,26,26,26,26,727,26,26,26,427,26,26,26,26,26,26,26,26,26,26,26,26,25,26,418,26],
#[26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[0,119,121,26,421,26,26,26,26,26,821,26,26,26,14,26,26,118,26,26,26,26,26,218,26,418,26,27,26],
#[26,28,26,26,26,26,26,26,26,26,26,26,26,28,26,26,26,26,26,26,26,26,26,26,26,26,26,26,28]
]

def ren (ks : List Nat) (i : Nat) := ks.foldl (fun j k => (stage1.permutations[k]!).getD j j) i
def col (i : Nat) : Signature :=
  let a := rawColumns[0]!
  let b := rawColumns[13]!
  if i == 26 then (a.1 &&& b.1,a.2 &&& b.2)
  else if i == 27 then (a.1 ||| rawColumns[14]!.1,a.2 ||| rawColumns[14]!.2)
  else if i == 28 then (rawColumns[1]!.1 &&& b.1,rawColumns[1]!.2 &&& b.2)
  else rawColumns[i]!

def gate (k : Nat) (ks : List Nat) : Signature :=
  let a := col (ren ks ((k / 29) % 29))
  let b := col (ren ks (k % 29))
  if 841 ≤ k then (a.1 &&& b.1,a.2 &&& b.2) else (a.1 ||| b.1,a.2 ||| b.2)

def dominates (a b : Signature) : Bool :=
  (a.1 &&& b.1 == b.1) && (a.2 &&& b.2 == a.2)

def good (k : Nat) : Bool :=
  let w := (witnesses[k/29]!)[k%29]!
  if w < 29 then dominates (col w) (gate k [])
  else
    let r := (w-29)%100
    let i := (w-29)/100
    decide (r < roots.size ∧ i < words.size) &&
      dominates (gate roots[r]! words[i]!) (gate k [])

set_option maxRecDepth 4096 in
private theorem row0 : ∀ j : Fin 29, good (0*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row1 : ∀ j : Fin 29, good (1*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row2 : ∀ j : Fin 29, good (2*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row3 : ∀ j : Fin 29, good (3*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row4 : ∀ j : Fin 29, good (4*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row5 : ∀ j : Fin 29, good (5*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row6 : ∀ j : Fin 29, good (6*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row7 : ∀ j : Fin 29, good (7*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row8 : ∀ j : Fin 29, good (8*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row9 : ∀ j : Fin 29, good (9*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row10 : ∀ j : Fin 29, good (10*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row11 : ∀ j : Fin 29, good (11*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row12 : ∀ j : Fin 29, good (12*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row13 : ∀ j : Fin 29, good (13*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row14 : ∀ j : Fin 29, good (14*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row15 : ∀ j : Fin 29, good (15*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row16 : ∀ j : Fin 29, good (16*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row17 : ∀ j : Fin 29, good (17*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row18 : ∀ j : Fin 29, good (18*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row19 : ∀ j : Fin 29, good (19*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row20 : ∀ j : Fin 29, good (20*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row21 : ∀ j : Fin 29, good (21*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row22 : ∀ j : Fin 29, good (22*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row23 : ∀ j : Fin 29, good (23*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row24 : ∀ j : Fin 29, good (24*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row25 : ∀ j : Fin 29, good (25*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row26 : ∀ j : Fin 29, good (26*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row27 : ∀ j : Fin 29, good (27*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row28 : ∀ j : Fin 29, good (28*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row29 : ∀ j : Fin 29, good (29*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row30 : ∀ j : Fin 29, good (30*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row31 : ∀ j : Fin 29, good (31*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row32 : ∀ j : Fin 29, good (32*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row33 : ∀ j : Fin 29, good (33*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row34 : ∀ j : Fin 29, good (34*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row35 : ∀ j : Fin 29, good (35*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row36 : ∀ j : Fin 29, good (36*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row37 : ∀ j : Fin 29, good (37*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row38 : ∀ j : Fin 29, good (38*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row39 : ∀ j : Fin 29, good (39*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row40 : ∀ j : Fin 29, good (40*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row41 : ∀ j : Fin 29, good (41*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row42 : ∀ j : Fin 29, good (42*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row43 : ∀ j : Fin 29, good (43*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row44 : ∀ j : Fin 29, good (44*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row45 : ∀ j : Fin 29, good (45*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row46 : ∀ j : Fin 29, good (46*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row47 : ∀ j : Fin 29, good (47*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row48 : ∀ j : Fin 29, good (48*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row49 : ∀ j : Fin 29, good (49*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row50 : ∀ j : Fin 29, good (50*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row51 : ∀ j : Fin 29, good (51*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row52 : ∀ j : Fin 29, good (52*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row53 : ∀ j : Fin 29, good (53*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row54 : ∀ j : Fin 29, good (54*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row55 : ∀ j : Fin 29, good (55*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row56 : ∀ j : Fin 29, good (56*29+j.val) = true := by decide +kernel
set_option maxRecDepth 4096 in
private theorem row57 : ∀ j : Fin 29, good (57*29+j.val) = true := by decide +kernel
private theorem checkRange (k : Nat) (h : k < 1682) : good k = true := by
  have cover (i : Fin 58) : ∀ j : Fin 29, good (i.val*29+j.val) = true := by
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
    | ⟨56,_⟩ => exact row56
    | ⟨57,_⟩ => exact row57
    | ⟨n+58,hn⟩ => omega
  have eq : k/29*29 + k%29 = k := by omega
  simpa only [eq] using cover ⟨k/29,by omega⟩ ⟨k%29,by omega⟩

theorem sound (k : Nat) (hk : k < 1682) :
    (∃ i < 29, dominates (col i) (gate k []) = true) ∨
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

theorem certificate_size : roots.size = 100 ∧ roots.toList.Nodup ∧
    words.all (fun ks => ks.all (fun i => i < 6)) = true := by decide +kernel
end PEqualNP.Research.PlaneFlagFourth

open PEqualNP.Research.PlaneFlagFourth in
theorem PEqualNP.Research.PlaneFlagFourth :
    ∀ k : Nat, k < 1682 →
      (∃ i < 29, dominates (col i) (gate k []) = true) ∨
      ∃ r ∈ roots, ∃ ks : List Nat, (∀ i ∈ ks, i < 6) ∧ (ren ks 0 = 0 ∧ ren ks 1 = 1 ∧ ren ks 13 = 13 ∧ ren ks 14 = 14) ∧
        dominates (gate r ks) (gate k []) = true := by
  have fixed : words.all (fun ks => decide (ren ks 0 = 0 ∧ ren ks 1 = 1 ∧ ren ks 13 = 13 ∧ ren ks 14 = 14)) = true := by decide +kernel
  intro k hk
  rcases sound k hk with old|⟨r,hr,ks,hw,hd⟩
  · exact Or.inl old
  · have goodWord := Array.all_eq_true_iff_forall_mem.mp certificate_size.2.2 ks hw
    have pins := of_decide_eq_true (Array.all_eq_true_iff_forall_mem.mp fixed ks hw)
    exact Or.inr ⟨r,hr,ks,fun i hi => of_decide_eq_true (List.all_eq_true.mp goodWord i hi),pins,hd⟩
