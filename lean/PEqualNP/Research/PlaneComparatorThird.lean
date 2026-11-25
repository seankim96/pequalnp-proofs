import PEqualNP.Research.OrderThreePlanePrefixData

namespace PEqualNP.Research.PlaneComparatorThird
open OrderThreePlanePrefixData
def roots : Array Nat := #[801,826,854,1,2,14,17,30,31,42,43,45,54,55,60,64,70,72,82,83]
def words : Array (List Nat) := #[[],[0],[1],[2],[3],[4],[5],[0,1],[0,2],[0,3],[0,4],[0,5],[1,2],[1,3],[1,4],[1,5],[2,0],[2,3],[2,4],[2,5],[3,0],[3,1],[3,2],[3,3],[3,4],[3,5],[4,1],[4,2],[4,3],[4,5],[5,2],[5,3],[5,4],[5,5],[0,1,2],[0,1,3],[0,1,4],[0,1,5],[0,2,0],[0,2,3],[0,2,5],[0,3,1],[0,3,2],[0,3,5],[0,4,1],[0,4,5],[0,5,2],[0,5,3],[0,5,4],[0,5,5],[1,2,0],[1,2,3],[1,2,4],[1,2,5],[1,3,0],[1,3,1],[1,3,2],[1,3,3],[1,3,5],[1,4,1],[1,4,3],[1,4,5],[1,5,2],[1,5,3],[1,5,4],[2,0,3],[2,0,4],[2,0,5],[2,3,4],[2,3,5],[2,4,1],[2,4,2],[2,4,3],[2,4,5],[2,5,2],[2,5,3],[2,5,4],[2,5,5],[3,0,4],[3,0,5],[3,1,2],[3,1,4],[3,1,5],[3,2,4],[3,2,5],[3,3,1],[3,3,4],[3,3,5],[3,4,1],[3,4,3],[3,4,5],[3,5,2],[3,5,3],[3,5,4],[3,5,5],[4,1,2],[4,1,3],[4,2,5],[4,3,1],[4,3,2],[4,3,5],[4,5,3],[4,5,4],[4,5,5],[5,2,3],[5,3,0],[5,3,1],[5,3,2],[5,3,3],[5,4,1],[5,4,2],[5,4,3],[5,4,5],[5,5,3],[5,5,5],[0,1,2,0],[0,1,2,5],[0,1,3,1],[0,1,3,2],[0,1,3,5],[0,1,4,1],[0,1,4,5],[0,1,5,2],[0,1,5,3],[0,2,0,3],[0,2,0,5],[0,2,5,2],[0,3,1,2],[0,3,1,4],[0,3,2,4],[0,3,5,2],[0,3,5,3],[0,3,5,4],[0,3,5,5],[0,4,1,3],[0,4,5,3],[0,4,5,4],[0,4,5,5],[0,5,2,3],[0,5,3,0],[0,5,3,1],[0,5,3,2],[0,5,3,3],[0,5,4,2],[0,5,4,3],[0,5,4,5],[1,2,0,5],[1,2,3,5],[1,2,4,1],[1,2,4,2],[1,2,5,2],[1,3,0,5],[1,3,1,4],[1,3,2,4],[1,3,3,5],[1,3,5,2],[1,4,1,3],[1,4,3,1],[1,4,3,2],[1,4,5,3],[1,5,3,3],[1,5,4,1],[1,5,4,2],[2,0,4,1],[2,0,4,5],[2,0,5,2],[2,0,5,3],[2,3,4,1],[2,3,4,5],[2,3,5,2],[2,3,5,3],[2,4,1,2],[2,4,1,3],[2,4,3,1],[2,4,3,5],[2,4,5,5],[2,5,3,1],[2,5,5,5],[3,0,4,5],[3,0,5,2],[3,0,5,3],[3,1,5,2],[3,2,4,1],[3,2,4,3],[3,2,5,2],[3,3,4,1],[3,3,4,5],[3,3,5,2],[3,3,5,5],[3,4,3,1],[3,4,3,5],[3,4,5,5],[3,5,5,5],[4,1,2,4],[4,2,5,5],[4,3,1,2],[4,3,1,5],[4,3,5,5],[4,5,4,5],[5,3,3,1],[5,3,3,4],[5,4,1,2],[0,1,2,0,5],[0,2,0,5,2],[0,3,2,4,1],[0,4,5,4,5],[1,2,0,5,2],[1,2,3,5,2],[1,2,4,1,2],[1,3,0,5,2],[1,3,2,4,1],[1,3,3,5,2],[1,4,3,1,2],[1,5,4,1,2],[2,4,1,2,4],[2,4,3,1,5]]
private def witnesses : Array (Array Nat) := #[
#[0,31,32,131,92,112,372,452,1332,551,352,432,472,27,33,133,513,34,113,553,1593,1793,1953,54,433,94,0,27],
#[31,1,35,36,95,115,375,455,1335,76,355,435,475,414,37,38,98,39,117,78,358,278,298,59,437,99,40,41],
#[32,35,2,135,42,142,922,562,43,555,62,242,63,633,44,144,45,338,145,564,65,85,185,1258,245,637,46,47],
#[131,36,135,3,515,395,1395,1655,1695,316,1595,1355,1455,154,138,137,517,139,398,318,1597,698,1078,239,1358,399,140,141],
#[92,95,42,515,4,203,522,103,1942,1795,202,1802,582,153,104,105,424,157,525,285,205,1384,725,618,585,1278,106,107],
#[112,115,142,395,203,5,122,123,222,1955,1962,602,2722,673,405,404,125,677,124,305,225,745,1624,1298,605,3038,126,127],
#[372,375,922,1395,522,122,6,2002,822,3295,363,443,1822,653,165,385,1404,418,384,3304,545,1585,1065,657,1825,2058,386,387],
#[452,455,562,1655,103,123,2002,7,2602,1435,1602,442,862,533,625,1145,1845,537,2005,1424,544,465,865,1498,464,2198,466,467],
#[1332,1335,43,1695,1942,222,822,2602,8,3455,1702,3822,483,1853,785,1325,1545,1198,1344,1645,1704,3424,2585,658,2145,1857,1346,1347],
#[551,76,555,316,1795,1955,3295,1435,3455,9,3475,3375,3675,254,558,1218,2098,259,1958,557,2998,1797,1957,919,1438,959,560,561],
#[352,355,62,1595,202,1962,363,1602,1702,3475,10,503,3682,613,364,365,425,158,1725,1045,1504,1385,3324,617,1605,638,366,367],
#[432,435,242,1355,1802,602,443,442,3822,3375,503,11,482,2073,265,1364,505,678,1485,1125,445,3384,1185,2077,444,1518,446,447],
#[472,475,63,1455,582,2722,1822,862,483,3675,3682,482,12,2193,345,485,1464,1098,665,2405,885,1165,3624,1538,484,2197,486,487],
#[27,414,633,154,153,673,653,533,1853,254,613,2073,2193,13,152,672,412,151,652,1412,532,1372,1612,611,1892,631,13,27],
#[33,37,44,138,104,405,165,625,785,558,364,265,345,152,14,642,162,155,263,962,622,262,942,615,163,635,166,167],
#[133,38,144,137,105,404,385,1145,1325,1218,365,1364,485,672,642,15,423,675,682,2562,543,2762,1002,2075,2082,1515,686,687],
#[513,98,45,517,424,125,1404,1845,1545,2098,425,505,1464,412,162,423,16,415,662,1842,843,842,2902,1535,2202,2235,426,427],
#[34,39,338,139,157,677,418,537,1198,259,158,678,1098,151,155,675,415,17,1555,1415,535,1375,1615,156,1895,336,160,161],
#[113,117,145,398,525,124,384,2005,1344,1958,1725,1485,665,652,263,682,662,1555,18,982,2062,2742,1722,655,983,2055,666,667],
#[553,78,564,318,285,305,3304,1424,1645,557,1045,1125,2405,1412,962,2562,1842,1415,982,19,542,1383,1623,3355,1902,3335,1426,1427],
#[1593,358,65,1597,205,225,545,544,1704,2998,1504,445,885,532,622,543,843,535,2062,542,20,1862,1882,1495,902,1855,546,547],
#[1793,278,85,698,1384,745,1585,465,3424,1797,1385,3384,1165,1372,262,2762,842,1375,2742,1383,1862,21,1783,3555,2162,3415,1386,1387],
#[1953,298,185,1078,725,1624,1065,865,2585,1957,3324,1185,3624,1612,942,1002,2902,1615,1722,1623,1882,1783,22,3315,2882,3615,1626,1627],
#[54,59,1258,239,618,1298,657,1498,658,919,617,2077,1538,611,615,2075,1535,156,655,3355,1495,3555,3315,23,2155,636,620,621],
#[433,437,245,1358,585,605,1825,464,2145,1438,1605,444,484,1892,163,2082,2202,1895,983,1902,902,2162,2882,2155,24,2195,1906,1907],
#[94,99,637,399,1278,3038,2058,2198,1857,959,638,1518,2197,631,635,1515,2235,336,2055,3335,1855,3415,3615,636,2195,25,640,641],
#[0,40,46,140,106,126,386,466,1346,560,366,446,486,13,166,686,426,160,666,1426,546,1386,1626,620,1906,640,26,27],
#[27,41,47,141,107,127,387,467,1347,561,367,447,487,27,167,687,427,161,667,1427,547,1387,1627,621,1907,641,27,27],
#[0,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,28,26,26,26,26,26,48,26,88,26,0],
#[26,1,26,26,26,26,26,26,26,26,26,26,26,408,29,26,26,26,109,26,26,26,26,26,429,26,26,408],
#[26,26,2,26,26,26,26,26,26,26,26,26,26,26,30,130,26,26,26,550,26,26,26,26,26,629,26,26],
#[26,26,26,3,26,26,26,26,26,26,26,26,26,148,26,129,509,26,26,26,1589,26,26,26,26,26,26,148],
#[26,26,26,26,4,26,26,26,26,26,26,26,26,26,90,26,410,149,26,26,26,1370,26,26,26,26,26,26],
#[26,26,26,26,26,5,26,26,26,26,26,26,26,26,26,390,26,669,110,26,26,26,1610,26,26,26,26,26],
#[26,26,26,26,26,26,6,26,26,26,26,26,26,26,26,26,1390,26,370,3290,26,26,26,649,26,26,26,26],
#[26,26,26,26,26,26,26,7,26,26,26,26,26,26,26,26,26,529,26,1410,530,26,26,26,450,26,26,26],
#[26,26,26,26,26,26,26,26,8,26,26,26,26,26,26,26,26,26,1330,26,1690,3410,26,26,26,1849,26,26],
#[26,26,26,26,26,26,26,26,26,9,26,26,26,248,26,26,26,26,26,549,26,1789,1949,26,26,26,26,248],
#[26,26,26,26,26,26,26,26,26,26,10,26,26,26,350,26,26,26,26,26,1490,26,3310,609,26,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,26,11,26,26,26,1350,26,26,26,26,26,3370,26,2069,430,26,26,26],
#[26,26,26,26,26,26,26,26,26,26,26,26,12,26,26,26,1450,26,26,26,26,26,3610,26,470,2189,26,26],
#[26,408,26,148,26,26,26,26,26,248,26,26,26,13,26,26,26,26,26,26,26,26,26,26,26,26,26,13],
#[26,29,30,26,90,26,26,26,26,26,350,26,26,26,14,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[26,26,130,129,26,390,26,26,26,26,26,1350,26,26,26,15,26,26,26,26,26,26,26,26,26,26,26,26],
#[26,26,26,509,410,26,1390,26,26,26,26,26,1450,26,26,26,16,26,26,26,26,26,26,26,26,26,26,26],
#[28,26,26,26,149,669,26,529,26,26,26,26,26,26,26,26,26,17,26,26,26,26,26,26,26,26,26,28],
#[26,109,26,26,26,110,370,26,1330,26,26,26,26,26,26,26,26,26,18,26,26,26,26,26,26,26,26,26],
#[26,26,550,26,26,26,3290,1410,26,549,26,26,26,26,26,26,26,26,26,19,26,26,26,26,26,26,26,26],
#[26,26,26,1589,26,26,26,530,1690,26,1490,26,26,26,26,26,26,26,26,26,20,26,26,26,26,26,26,26],
#[26,26,26,26,1370,26,26,26,3410,1789,26,3370,26,26,26,26,26,26,26,26,26,21,26,26,26,26,26,26],
#[26,26,26,26,26,1610,26,26,26,1949,3310,26,3610,26,26,26,26,26,26,26,26,26,22,26,26,26,26,26],
#[48,26,26,26,26,26,649,26,26,26,609,2069,26,26,26,26,26,26,26,26,26,26,26,23,26,26,26,48],
#[26,429,26,26,26,26,26,450,26,26,26,430,470,26,26,26,26,26,26,26,26,26,26,26,24,26,26,26],
#[88,26,629,26,26,26,26,26,1849,26,26,26,2189,26,26,26,26,26,26,26,26,26,26,26,26,25,26,88],
#[26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26],
#[0,408,26,148,26,26,26,26,26,248,26,26,26,13,26,26,26,28,26,26,26,26,26,48,26,88,26,27]
]

def ren (ks : List Nat) (i : Nat) := ks.foldl (fun j k => (stage1.permutations[k]!).getD j j) i
def col (i : Nat) : Signature :=
  let a := rawColumns[0]!
  let b := rawColumns[13]!
  if i == 26 then (a.1 &&& b.1,a.2 &&& b.2)
  else if i == 27 then (a.1 ||| b.1,a.2 ||| b.2)
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
    let r := (w-28)%20
    let i := (w-28)/20
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

theorem certificate_size : roots.size = 20 ∧ roots.toList.Nodup ∧
    words.all (fun ks => ks.all (fun i => i < 6)) = true := by decide +kernel
end PEqualNP.Research.PlaneComparatorThird

open PEqualNP.Research.PlaneComparatorThird in
theorem PEqualNP.Research.PlaneComparatorThird :
    ∀ k : Nat, k < 1568 →
      (∃ i < 28, dominates (col i) (gate k []) = true) ∨
      ∃ r ∈ roots, ∃ ks : List Nat, (∀ i ∈ ks, i < 6) ∧
        dominates (gate r ks) (gate k []) = true := by
  intro k hk
  rcases sound k hk with old|⟨r,hr,ks,hw,hd⟩
  · exact Or.inl old
  · have goodWord := Array.all_eq_true_iff_forall_mem.mp certificate_size.2.2 ks hw
    exact Or.inr ⟨r,hr,ks,fun i hi => of_decide_eq_true (List.all_eq_true.mp goodWord i hi),hd⟩
