import PEqualNP.Research.PlanePairAndCount
import PEqualNP.Research.PlaneFlagOrTail
import Mathlib.Data.List.Forall2

namespace PEqualNP.Research.PlaneSecondMaskAndCount
open PlanePairAndCount

def positives : Array (BitVec 32) := #[2885689345, 2952798210, 2684362760, 2684363264, 2818588674, 2281717764, 2281717776, 2281718784, 2147516420, 2684387336, 2147516448, 2147518464, 2684420104, 2147549200, 2147549248, 2147553280, 2281832449, 2147614736, 2147614752, 2147614848, 2684616706, 2147745824, 2147745856, 2147746048, 2148007940, 2148008000, 2148008064, 2148008448, 2685403144, 2148532352, 2148532480, 2148533248, 2149580816, 2149581056, 2149581312, 2149582848, 2151677984, 2151678464, 2151678976, 2151682048, 2290089985, 2155872320, 2155873280, 2155874304, 2701131778, 2164260992, 2164262912, 2164264960, 2315255809, 2181038084, 2181038336, 2181042176]
def negatives : Array (BitVec 32) := #[2281763264, 2281793952, 2281816961, 2281863488, 2147661120, 2281886528, 2147691780, 2147714818, 2147792016, 2282017409, 2147822724, 2282048129, 2282063489, 2282078849, 2147892228, 2282117640, 2147945988, 2282256672, 2148054288, 2148085024, 2282309921, 2282325251, 2148154624, 2282379528, 2148177154, 2148207874, 2148238594, 2148285456, 2282510345, 2282525713, 2148408328, 2282641416, 2282780768, 2282803777, 2282834465, 2148677700, 2282904128, 2148700738, 2148731398, 2148808724, 2283035137, 2283049489, 2283065857, 2283080197, 2283096577, 2148932100, 2149070896, 2283296801, 2283311123, 2283341859, 2283542545, 2283827424, 2149627072, 2283851969, 2149655716, 2283897987, 2149725252, 2149749826, 2149856388, 2284081289, 2284098689, 2284127365, 2149979148, 2284343337, 2284360707, 2284389411, 2284422147, 2150241290, 2284605449, 2150641764, 2284867681, 2284884035, 2284912679, 2150764614, 2150797378, 2285436963, 2285922752, 2151719376, 2285945281, 2151754116, 2285980033, 2285994371, 2151819588, 2286045512, 2151876870, 2151950484, 2286176393, 2286225541, 2286438665, 2286453011, 2286518531, 2152335626, 2286684185, 2286700553, 2152736852, 2286977107, 2287011847, 2152859718, 2152925190, 2287208469, 2287501331, 2288009417, 2288058503, 2288091267, 2153906254, 2289041479, 2289074243, 2289106951, 2290119072, 2155917712, 2290144128, 2155946404, 2290172832, 2155971458, 2290242312, 2156069638, 2156102402, 2156146836, 2290373256, 2156171920, 2156270092, 2290504200, 2156409136, 2290635048, 2156433682, 2156531978, 2156933172, 2156958226, 2156986918, 2157117958, 2157187604, 2157449266, 2157482002, 2157981860, 2292207784, 2158035110, 2158104590, 2158235788, 2292469896, 2158497834, 2158628874, 2159022118, 2159083558, 2160075156, 2160099730, 2160132486, 2160165250, 2160197902, 2160328860, 2160591130, 2160722186, 2162163854, 2162294798, 2164303184, 2298528577, 2164335908, 2298561313, 2298578689, 2298594049, 2164401476, 2298626888, 2164426560, 2164459268, 2298775057, 2298807813, 2298840577, 2164655628, 2164794672, 2299019561, 2299036945, 2299069729, 2299266073, 2165317748, 2299544161, 2299560529, 2299576897, 2299593253, 2299609633, 2299789845, 2299822609, 2299855365, 2166367332, 2300592233, 2300642341, 2166490188, 2300838925, 2166752268, 2301624421, 2168463700, 2302689609, 2302706001, 2168586572, 2302820680, 2302935069, 2303721557, 2172657972, 2306884392, 2172715812, 2172912156, 2173174072, 2307408168, 2173698612, 2176844060, 2177105948, 2315282656, 2181080272, 2181115040, 2315340448, 2181138050, 2315405896, 2181203522, 2181238274, 2181268994, 2181311632, 2315537032, 2181334672, 2181369472, 2315667976, 2181573680, 2181631010, 2181696522, 2181827608, 2182097008, 2316323424, 2182120018, 2182154786, 2182251074, 2182613042, 2182678562, 2183144672, 2317369576, 2183169218, 2183201954, 2183234690, 2183267402, 2183660586, 2183791626, 2185242832, 2319468744, 2185265362, 2185365578, 2185496728, 2319730824, 2185758746, 2185889802, 2186283090, 2186313810, 2187329738, 2187460682, 2323661480, 2189460114, 2189525634, 2189951034, 2190475826, 2190508562, 2190541346, 2191524010]
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
def mask : BitVec 52 := 0x10001010121f
def testRow := evalRow (mask,0)
private def indices : Array Nat := #[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 24, 25, 26, 28, 30, 32, 33, 34, 35, 37, 39, 40, 41, 42, 43, 44, 46, 48, 49, 50, 51, 52, 53, 54, 55, 59, 60, 62, 63, 65, 69, 70, 71, 73, 74, 75, 76, 78, 79, 80, 83, 86, 88, 89, 90, 91, 92, 95, 98, 99, 101, 103, 104, 106, 110, 111, 112, 113, 115, 116, 118, 120, 121, 123, 125, 126, 127, 130, 131, 134, 135, 138, 139, 140, 141, 142, 143, 145, 146, 150, 153, 156, 157, 158, 162, 163, 164, 166, 167, 168, 170, 171, 173, 175, 178, 179, 180, 181, 182, 185, 186, 187, 188, 190, 192, 195, 196, 197, 200, 201, 205, 207, 208, 209, 211, 213, 214, 216, 218, 220, 221, 223, 226, 227, 229, 231, 232, 234, 236, 238, 239, 241, 243, 244, 245, 246, 247, 248, 249, 250, 251, 254, 257, 258, 259, 260, 262, 263, 264, 266, 270, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 285, 287, 289, 294, 298, 299, 300, 303, 305, 306, 311, 320, 321, 322, 328, 330, 332, 333, 337, 340, 342, 343, 344, 345, 347, 348, 349, 350, 351, 352, 353, 354, 356, 361, 363, 364, 366, 368, 371, 372, 374, 375, 379, 381, 383, 384, 385, 387, 389, 391, 392, 394, 396, 397, 398, 400, 402, 404, 406, 407, 408, 410, 412, 415, 418, 419, 420, 423, 427, 428, 429, 430, 432]
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

end PEqualNP.Research.PlaneSecondMaskAndCount

open PEqualNP.Research.PlanePairAndCount PEqualNP.Research.PlaneSecondMaskAndCount in
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


open PEqualNP.Research.PlaneSecondMaskAndCount PEqualNP.Research.PlanePairAndCount in
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

open PEqualNP.Research PEqualNP.Research.PlaneSecondMaskAndCount PEqualNP.Research.PlanePairAndCount in
set_option maxRecDepth 10000 in
theorem PEqualNP.Research.PlaneSecondMaskAndCount : (((List.range 841).countP (fun r => let p := (PlaneFlagFourth.gate (841+r) []).1; p &&& mask == p)) = 717) ∧
    (∀ (x : Sig) (gs : List Gate) (o : Nat),
    x.1 &&& mask = x.1 →
    (∀ i : Fin 52, readWire (gs.foldl step (evalRow x true i.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst) := by
  constructor
  · decide +kernel
  · exact anyColumn
