import PEqualNP.Research.PlaneSingleFlagBound

namespace PEqualNP.Research.PlaneFlagFamilyB
open PlaneSingleFlagBound PlanePairAndCount

private def ps : Array (BitVec 32) := #[2348818433, 2415927298, 2147491848, 2147492352, 2281717762, 2281717764, 2281717776, 2281718784, 2147516420, 2147516424, 2147516448, 2147518464, 2147549192, 2147549200, 2147549248, 2147553280, 2281832449, 2147614736, 2147614752, 2147614848, 2147745794, 2147745824, 2147745856, 2147746048, 2148007940, 2148008000, 2148008064, 2148008448, 2148532232, 2148532352, 2148532480, 2148533248, 2149580816, 2149581056, 2149581312, 2149582848, 2151677984, 2151678464, 2151678976, 2151682048, 2290089985, 2155872320, 2155873280, 2155874304, 2164260866, 2164260992, 2164262912, 2164264960, 2315255809, 2181038084, 2181038336, 2181042176]
private def ns : Array (BitVec 32) := #[2281894208, 2147714818, 2147792016, 2282017409, 2282063489, 2282078849, 2147892228, 2147953668, 2282256672, 2148054288, 2148085024, 2282309921, 2148154624, 2282387712, 2148285456, 2282510345, 2148408328, 2282641416, 2282780768, 2282803777, 2148677700, 2282904128, 2282911808, 2148700738, 2148808724, 2283035137, 2283049489, 2283080197, 2283096577, 2148932100, 2283166208, 2148993540, 2149070896, 2283296801, 2283311123, 2283341859, 2283358241, 2283827424, 2149627072, 2149655716, 2283897987, 2149856388, 2284081289, 2284098689, 2284114049, 2284160129, 2284360707, 2284389411, 2284422147, 2150241290, 2150274050, 2284590089, 2284605449, 2284622849, 2150503432, 2150641764, 2284884035, 2284900417, 2284912679, 2150797378, 2285375523, 2285391905, 2151719376, 2151754116, 2285994371, 2286010753, 2286053696, 2151950484, 2286176393, 2286241921, 2286438665, 2286453011, 2286487811, 2152335626, 2286569736, 2152401154, 2286684185, 2152736852, 2286977107, 2287011847, 2152925190, 2287470611, 2287732753, 2288009417, 2288025795, 2288042177, 2288058503, 2153906254, 2288255117, 2288320645, 2289041479, 2154954822, 2290119072, 2290151808, 2155946404, 2290172832, 2290180512, 2290205568, 2156040962, 2290275072, 2156069638, 2156102402, 2156146836, 2290373256, 2156171920, 2156179600, 2290406016, 2156270092, 2156409136, 2156433682, 2156531978, 2290766088, 2156933172, 2156958226, 2156986918, 2157056518, 2157117958, 2157187604, 2292207784, 2158104590, 2158243972, 2158366732, 2158497834, 2292731944, 2159083558, 2159153158, 2159546402, 2160075156, 2160165250, 2160197902, 2160328860, 2160591130, 2162163854, 2162229382, 2162425996, 2164335908, 2298561313, 2298594049, 2164434240, 2298659648, 2164459268, 2164466948, 2164492032, 2298807813, 2298840577, 2164655628, 2299019561, 2299102465, 2299266073, 2299298833, 2165317748, 2299544161, 2299560529, 2299593253, 2299789845, 2166367332, 2300592233, 2166490188, 2166498372, 2300838925, 2300904453, 2166752268, 2301101097, 2301166625, 2301640801, 2301689893, 2302689609, 2302706001, 2302722369, 2168586572, 2168594756, 2302820680, 2302935069, 2303197465, 2303230225, 2304770125, 2305818693, 2172715812, 2172723492, 2306949920, 2172781324, 2307015432, 2172846852, 2172912156, 2173174072, 2307408168, 2173698612, 2176844060, 2176852244, 2181080272, 2181115040, 2315348128, 2181138050, 2315405896, 2181203522, 2181334672, 2181342352, 2181369472, 2315602560, 2315667976, 2181696522, 2181762050, 2181835792, 2181958664, 2182097008, 2316331104, 2182154786, 2316388896, 2316454464, 2182285826, 2182613042, 2183144672, 2317377760, 2183234690, 2183267402, 2183300162, 2183660586, 2183726114, 2183791626, 2185242832, 2319468744, 2319476928, 2185365578, 2185496728, 2185504912, 2319730824, 2185758746, 2186020888, 2186313810, 2186414146, 2187329738, 2321563848, 2187362498, 2323661480, 2189492898, 2189525634, 2189689496, 2189722256, 2189951034, 2190475826, 2190508562, 2191524010, 2325758120, 2191589538, 2192048170, 2193621146, 2193653906, 2197824624, 2332050024, 2197857360, 2197947976, 2197980736, 2198111760, 2198210056, 2198340664, 2198348848, 2198864496]
private def ix : Array (Nat) := #[6, 8, 9, 10, 13, 14, 15, 18, 19, 20, 21, 22, 25, 27, 33, 34, 37, 39, 40, 41, 43, 44, 45, 46, 49, 50, 51, 53, 54, 55, 57, 58, 59, 60, 62, 63, 64, 69, 70, 73, 74, 78, 79, 80, 82, 85, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 101, 102, 103, 106, 107, 108, 112, 115, 118, 119, 122, 125, 126, 129, 130, 131, 132, 135, 136, 137, 138, 140, 141, 142, 145, 149, 152, 153, 154, 155, 156, 158, 159, 161, 162, 165, 166, 169, 170, 171, 172, 174, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 187, 190, 192, 193, 195, 196, 197, 198, 200, 201, 209, 213, 215, 217, 218, 219, 223, 224, 225, 226, 231, 232, 234, 236, 239, 240, 242, 245, 246, 248, 252, 253, 254, 255, 256, 258, 259, 260, 263, 269, 270, 271, 272, 273, 274, 276, 278, 281, 282, 285, 286, 287, 288, 289, 290, 292, 296, 297, 299, 300, 302, 303, 304, 305, 306, 307, 309, 315, 319, 322, 323, 324, 325, 326, 327, 328, 330, 332, 333, 337, 338, 343, 344, 346, 347, 348, 349, 354, 355, 356, 358, 361, 366, 367, 369, 370, 371, 373, 375, 376, 378, 380, 381, 384, 386, 391, 392, 393, 394, 395, 396, 397, 398, 399, 402, 404, 405, 406, 407, 409, 412, 413, 415, 416, 417, 419, 421, 423, 424, 426, 427, 428, 429, 432, 433, 434, 435, 436, 437, 441, 442, 444, 445, 447, 449, 450, 451, 452, 454]
def group : BitVec 52 := 0x4caf2a9aa6800
private def compatible (i j : Nat) := robust ps (ns[i]! ||| ns[j]!) group
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

private theorem pRows : ∀ j : Fin 52, row ps[j.val]! = evalRow (0,0) true j.val := by decide +kernel
private theorem nRows : ∀ i : Fin 257, ix[i.val]! < 468 ∧ row ns[i.val]! = evalRow (0,0) false ix[i.val]! := by decide +kernel
end PEqualNP.Research.PlaneFlagFamilyB

open PEqualNP.Research.PlaneFlagFamilyB PEqualNP.Research.PlaneSingleFlagBound PEqualNP.Research.PlanePairAndCount in
theorem PEqualNP.Research.PlaneFlagFamilyB : ∀ (x : Sig) (e : Fin 52) (gs : List Gate) (o : Nat), group.getLsbD e.val = true →
    (∀ j : Fin 52, j ≠ e → x.1.getLsbD j.val = false) →
    (∀ j : Fin 52, readWire (gs.foldl step (evalRow x true j.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst := bound ps ns ix group pRows nRows cert
