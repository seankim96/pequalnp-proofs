import PEqualNP.Research.PlanePairAndCount
import PEqualNP.Research.PlaneFlagOrTail
import Mathlib.Data.List.Forall2

namespace PEqualNP.Research.PlaneMaskAndCount
open PlanePairAndCount

def positives : Array (BitVec 32) := #[2885689345, 2415927298, 2147491848, 2147492352, 2818588674, 2818588676, 2818588688, 2818589696, 2147516420, 2147516424, 2147516448, 2147518464, 2147549192, 2147549200, 2147549248, 2147553280, 2818703361, 2147614736, 2147614752, 2147614848, 2147745794, 2147745824, 2147745856, 2147746048, 2148007940, 2148008000, 2148008064, 2148008448, 2148532232, 2148532352, 2148532480, 2148533248, 2149580816, 2149581056, 2149581312, 2149582848, 2151677984, 2151678464, 2151678976, 2151682048, 2826960897, 2155872320, 2155873280, 2155874304, 2164260866, 2164260992, 2164262912, 2164264960, 2852126721, 2181038084, 2181038336, 2181042176]
def negatives : Array (BitVec 32) := #[2281763264, 2281793952, 2281816961, 2281863488, 2147661120, 2281886528, 2147691780, 2147714818, 2147792016, 2282017409, 2147822724, 2282048129, 2282063489, 2147892228, 2282117640, 2147945988, 2147953668, 2282256672, 2148054288, 2148085024, 2282325251, 2148154624, 2282379528, 2148177154, 2148207874, 2148285456, 2282510345, 2282525713, 2148416512, 2282780768, 2282803777, 2282834465, 2148677700, 2282904128, 2148731398, 2148808724, 2283035137, 2283049489, 2283080197, 2148939780, 2149070896, 2283311123, 2283341859, 2283542545, 2283573265, 2283827424, 2149627072, 2149655716, 2283897987, 2149725252, 2149749826, 2149856388, 2284081289, 2284098689, 2284127365, 2284160129, 2149979148, 2149987332, 2284343337, 2284360707, 2284389411, 2284422147, 2150241290, 2284590089, 2284622849, 2150641764, 2284884035, 2284912679, 2150764614, 2285375523, 2285408259, 2285436963, 2285922752, 2151719376, 2151754116, 2285994371, 2151819588, 2286045512, 2151876870, 2151950484, 2286176393, 2286225541, 2286438665, 2286453011, 2286487811, 2286518531, 2286684185, 2152736852, 2286977107, 2287011847, 2152859718, 2287208469, 2287273989, 2287470611, 2287501331, 2287536131, 2287732753, 2288009417, 2288025795, 2288058503, 2288091267, 2153906254, 2288255117, 2288320645, 2289041479, 2289074243, 2289106951, 2290119072, 2155917712, 2290144128, 2155946404, 2290172832, 2290242312, 2156040962, 2156069638, 2156102402, 2156146836, 2290373256, 2156179600, 2156270092, 2156409136, 2290635048, 2156433682, 2156531978, 2156564738, 2156933172, 2156958226, 2156986918, 2157056518, 2157089282, 2157117958, 2157187604, 2157195284, 2157318660, 2157449266, 2157981860, 2292207784, 2158035110, 2158104590, 2158243972, 2158366732, 2158628874, 2159022118, 2159153158, 2160075156, 2160099730, 2160132486, 2160197902, 2160263430, 2160328860, 2160337044, 2160591130, 2160722186, 2162163854, 2162294798, 2164303184, 2298528577, 2164335908, 2298561313, 2298578689, 2164401476, 2298626888, 2164434240, 2164459268, 2164466948, 2298775057, 2298807813, 2298840577, 2164655628, 2164794672, 2299019561, 2299036945, 2299069729, 2299102465, 2299266073, 2299298833, 2165317748, 2299544161, 2299560529, 2299593253, 2299789845, 2299822609, 2299855365, 2166367332, 2300592233, 2300642341, 2166490188, 2166498372, 2300838925, 2300904453, 2301101097, 2301166625, 2301363209, 2301624421, 2301689893, 2168463700, 2302689609, 2302706001, 2168594756, 2302935069, 2303197465, 2303230225, 2303459353, 2303721557, 2303754321, 2303983637, 2304770125, 2305032205, 2305818693, 2172657972, 2306884392, 2172723492, 2172781324, 2172846852, 2172912156, 2173043212, 2173182256, 2173698612, 2173706292, 2176844060, 2176852244, 2176975116, 2315282656, 2181080272, 2181115040, 2315340448, 2181138050, 2315405896, 2181203522, 2181238274, 2181268994, 2181311632, 2315537032, 2181334672, 2181342352, 2181377152, 2181434888, 2181500416, 2181573680, 2181631010, 2181696522, 2181762050, 2181827608, 2181835792, 2181958664, 2182097008, 2316323424, 2182120018, 2182220354, 2182251074, 2182285826, 2182613042, 2183144672, 2317369576, 2183169218, 2183201954, 2183267402]
private def compatible (i j : Nat) : Bool :=
  let u := negatives[i]! ||| negatives[j]!
  positives.any fun p => p &&& u == p
set_option maxRecDepth 10000 in
private theorem cert0 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+0 < b.val → compatible (a.val+0) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert1 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+8 < b.val → compatible (a.val+8) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert2 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+16 < b.val → compatible (a.val+16) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert3 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+24 < b.val → compatible (a.val+24) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert4 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+32 < b.val → compatible (a.val+32) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert5 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+40 < b.val → compatible (a.val+40) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert6 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+48 < b.val → compatible (a.val+48) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert7 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+56 < b.val → compatible (a.val+56) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert8 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+64 < b.val → compatible (a.val+64) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert9 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+72 < b.val → compatible (a.val+72) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert10 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+80 < b.val → compatible (a.val+80) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert11 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+88 < b.val → compatible (a.val+88) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert12 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+96 < b.val → compatible (a.val+96) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert13 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+104 < b.val → compatible (a.val+104) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert14 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+112 < b.val → compatible (a.val+112) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert15 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+120 < b.val → compatible (a.val+120) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert16 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+128 < b.val → compatible (a.val+128) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert17 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+136 < b.val → compatible (a.val+136) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert18 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+144 < b.val → compatible (a.val+144) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert19 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+152 < b.val → compatible (a.val+152) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert20 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+160 < b.val → compatible (a.val+160) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert21 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+168 < b.val → compatible (a.val+168) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert22 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+176 < b.val → compatible (a.val+176) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert23 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+184 < b.val → compatible (a.val+184) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert24 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+192 < b.val → compatible (a.val+192) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert25 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+200 < b.val → compatible (a.val+200) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert26 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+208 < b.val → compatible (a.val+208) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert27 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+216 < b.val → compatible (a.val+216) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert28 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+224 < b.val → compatible (a.val+224) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert29 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+232 < b.val → compatible (a.val+232) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert30 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+240 < b.val → compatible (a.val+240) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert31 : ∀ a : Fin 8, ∀ b : Fin 257, a.val+248 < b.val → compatible (a.val+248) b.val = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem cert32 : ∀ a : Fin 1, ∀ b : Fin 257, a.val+256 < b.val → compatible (a.val+256) b.val = true := by decide +kernel
private theorem cert (i j : Fin 257) (lt : i.val < j.val) : compatible i.val j.val = true := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) (hlt : r+8*q.val < j.val) : compatible (r+8*q.val) j.val = true := by
    match q with
    | ⟨0,_⟩ => exact cert0 ⟨r,by omega⟩ j hlt
    | ⟨1,_⟩ => exact cert1 ⟨r,by omega⟩ j hlt
    | ⟨2,_⟩ => exact cert2 ⟨r,by omega⟩ j hlt
    | ⟨3,_⟩ => exact cert3 ⟨r,by omega⟩ j hlt
    | ⟨4,_⟩ => exact cert4 ⟨r,by omega⟩ j hlt
    | ⟨5,_⟩ => exact cert5 ⟨r,by omega⟩ j hlt
    | ⟨6,_⟩ => exact cert6 ⟨r,by omega⟩ j hlt
    | ⟨7,_⟩ => exact cert7 ⟨r,by omega⟩ j hlt
    | ⟨8,_⟩ => exact cert8 ⟨r,by omega⟩ j hlt
    | ⟨9,_⟩ => exact cert9 ⟨r,by omega⟩ j hlt
    | ⟨10,_⟩ => exact cert10 ⟨r,by omega⟩ j hlt
    | ⟨11,_⟩ => exact cert11 ⟨r,by omega⟩ j hlt
    | ⟨12,_⟩ => exact cert12 ⟨r,by omega⟩ j hlt
    | ⟨13,_⟩ => exact cert13 ⟨r,by omega⟩ j hlt
    | ⟨14,_⟩ => exact cert14 ⟨r,by omega⟩ j hlt
    | ⟨15,_⟩ => exact cert15 ⟨r,by omega⟩ j hlt
    | ⟨16,_⟩ => exact cert16 ⟨r,by omega⟩ j hlt
    | ⟨17,_⟩ => exact cert17 ⟨r,by omega⟩ j hlt
    | ⟨18,_⟩ => exact cert18 ⟨r,by omega⟩ j hlt
    | ⟨19,_⟩ => exact cert19 ⟨r,by omega⟩ j hlt
    | ⟨20,_⟩ => exact cert20 ⟨r,by omega⟩ j hlt
    | ⟨21,_⟩ => exact cert21 ⟨r,by omega⟩ j hlt
    | ⟨22,_⟩ => exact cert22 ⟨r,by omega⟩ j hlt
    | ⟨23,_⟩ => exact cert23 ⟨r,by omega⟩ j hlt
    | ⟨24,_⟩ => exact cert24 ⟨r,by omega⟩ j hlt
    | ⟨25,_⟩ => exact cert25 ⟨r,by omega⟩ j hlt
    | ⟨26,_⟩ => exact cert26 ⟨r,by omega⟩ j hlt
    | ⟨27,_⟩ => exact cert27 ⟨r,by omega⟩ j hlt
    | ⟨28,_⟩ => exact cert28 ⟨r,by omega⟩ j hlt
    | ⟨29,_⟩ => exact cert29 ⟨r,by omega⟩ j hlt
    | ⟨30,_⟩ => exact cert30 ⟨r,by omega⟩ j hlt
    | ⟨31,_⟩ => exact cert31 ⟨r,by omega⟩ j hlt
    | ⟨32,_⟩ => exact cert32 ⟨r,by change r + 256 < 257 at hs; omega⟩ j hlt
    | ⟨n+33,hn⟩ => omega
  have ht : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [ht] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega) (by dsimp; omega)

abbrev Sig := OrderThreePlanePrefixData.Signature
def pool (x : Sig) : List Sig := List.ofFn (fun j : Fin 29 => PlaneFlagFourth.col j.val) ++ [x,(0,0),(-1,-1)]
def evalRow (x : Sig) (pos : Bool) (i : Nat) : Row :=
  (pool x).map fun v => if pos then v.1.getLsbD i else v.2.getLsbD i
def mask : BitVec 52 := 0x10100000100f1
def testRow := evalRow (mask,0)
private def indices : Array Nat := #[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 24, 25, 26, 28, 30, 33, 34, 35, 38, 40, 41, 42, 43, 44, 48, 49, 50, 51, 53, 56, 59, 62, 63, 65, 68, 69, 70, 73, 74, 75, 76, 78, 79, 80, 83, 85, 86, 87, 88, 89, 90, 91, 92, 94, 96, 98, 101, 103, 104, 107, 109, 110, 111, 112, 115, 118, 120, 121, 123, 125, 126, 127, 130, 131, 132, 134, 138, 140, 141, 142, 143, 146, 148, 149, 150, 151, 152, 153, 154, 156, 157, 158, 159, 161, 162, 163, 164, 166, 167, 168, 170, 171, 175, 176, 178, 179, 180, 181, 183, 185, 187, 188, 190, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 204, 205, 208, 209, 211, 213, 215, 217, 220, 221, 224, 226, 227, 229, 232, 233, 234, 235, 236, 238, 239, 241, 243, 244, 245, 246, 247, 249, 250, 252, 254, 255, 257, 258, 259, 260, 262, 263, 264, 266, 269, 270, 271, 272, 273, 274, 276, 278, 279, 280, 281, 282, 283, 285, 286, 287, 288, 290, 292, 293, 294, 297, 298, 299, 300, 304, 306, 307, 309, 310, 311, 313, 314, 315, 318, 319, 320, 321, 323, 325, 327, 328, 329, 331, 333, 334, 337, 338, 339, 342, 343, 344, 345, 347, 348, 349, 350, 351, 352, 353, 354, 355, 357, 360, 362, 363, 364, 366, 367, 368, 369, 370, 371, 372, 374, 377, 379, 380, 381, 384, 385, 387, 389, 392]
private theorem posRows : ∀ i : Fin 52, row positives[i.val]! = testRow true i.val := by decide +kernel
private theorem negRows : ∀ i : Fin 257, indices[i.val]! < 468 ∧ row negatives[i.val]! = testRow false indices[i.val]! := by decide +kernel

private abbrev Up (s t : Row) := List.Forall₂ (fun a b : Bool => a = true → b = true) s t
private theorem readUp {s t : Row} (h : Up s t) (i : Nat) : readWire s i = true → readWire t i = true := by
  induction h generalizing i with
  | nil => exact id
  | cons pair rest ih => cases i with
    | zero => exact pair
    | succ j => exact ih j

private theorem memo (gs : List Gate) {s t : Row} (h : Up s t) : Up (gs.foldl step s) (gs.foldl step t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    have hl := readUp h g.2.1
    have hr := readUp h g.2.2
    cases q : g.1 <;> simp_all <;> (try tauto)

private theorem pref (pos : Bool) (i : Nat) (x y : Sig)
    (h : (if pos then x.1.getLsbD i else x.2.getLsbD i) = true →
      (if pos then y.1.getLsbD i else y.2.getLsbD i) = true) : Up (evalRow x pos i) (evalRow y pos i) := by
  simp only [evalRow,pool,List.map_append,List.map_cons,List.map_nil]
  apply List.rel_append _ (List.Forall₂.cons h (List.Forall₂.cons id (List.Forall₂.cons id List.Forall₂.nil)))
  generalize List.map _ (List.ofFn _) = common
  induction common with
  | nil => exact List.Forall₂.nil
  | cons _ _ ih => exact List.Forall₂.cons id ih

end PEqualNP.Research.PlaneMaskAndCount

open PEqualNP.Research.PlanePairAndCount PEqualNP.Research.PlaneMaskAndCount in
private theorem baseBound : ∀ (gs : List Gate) (o : Nat),
    (∀ i : Fin 52, readWire (gs.foldl step (testRow true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (testRow false i.val)) o = false) → 9 ≤ gs.countP Prod.fst := by
  intro gs o hp hn
  have pairs (i j : Fin 257) (lt : i.val < j.val) : ∃ p ∈ positives, p &&& (negatives[i.val]! ||| negatives[j.val]!) = p := by
    obtain ⟨p,mem,h⟩ := Array.any_eq_true'.mp (cert i j lt)
    exact ⟨p,mem,eq_of_beq h⟩
  apply PEqualNP.Research.PlanePairAndCount positives (fun i => negatives[i.val]!) pairs gs o
  · intro p mem
    obtain ⟨i,hi,ep⟩ := Array.getElem_of_mem mem
    have len : positives.size = 52 := rfl
    have eq : positives[i]! = p := by simpa [getElem!_pos,hi] using ep
    rw [← eq,posRows ⟨i,by omega⟩]
    exact hp _
  · intro i
    rw [(negRows i).2]
    exact hn ⟨_,(negRows i).1⟩


open PEqualNP.Research.PlaneMaskAndCount PEqualNP.Research.PlanePairAndCount in
private theorem anyColumn : ∀ (x : Sig) (gs : List Gate) (o : Nat),
    x.1 &&& mask = x.1 →
    (∀ i : Fin 52, readWire (gs.foldl step (evalRow x true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst := by
  intro x gs o sub hp hn
  apply baseBound gs o
  · intro i
    apply readUp (memo gs (pref true i.val x (mask,0) _)) o (hp i)
    intro h
    have hh := congrArg (fun v : BitVec 52 => v.getLsbD i.val) sub
    change (x.1 &&& mask).getLsbD i.val = x.1.getLsbD i.val at hh
    change x.1.getLsbD i.val = true at h
    change mask.getLsbD i.val = true
    simpa only [BitVec.getLsbD_and,h,Bool.true_and] using hh
  · intro i
    cases h : readWire (gs.foldl step (testRow false i.val)) o
    · rfl
    · have up := readUp (memo gs (pref false i.val (mask,0) x (by simp))) o h
      rw [hn i] at up
      contradiction

open PEqualNP.Research PEqualNP.Research.PlaneMaskAndCount PEqualNP.Research.PlanePairAndCount in
set_option maxRecDepth 10000 in
theorem PEqualNP.Research.PlaneMaskAndCount : (((List.range 841).countP (fun r => let p := (PlaneFlagFourth.gate (841+r) []).1; p &&& mask == p)) = 724) ∧
    (∀ (x : Sig) (gs : List Gate) (o : Nat),
    x.1 &&& mask = x.1 →
    (∀ i : Fin 52, readWire (gs.foldl step (evalRow x true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst) := by
  constructor
  · decide +kernel
  · exact anyColumn
