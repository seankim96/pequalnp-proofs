import PEqualNP.Research.PlaneSingleFlagBound

namespace PEqualNP.Research.PlaneFlagFamilyA
open PlaneSingleFlagBound PlanePairAndCount

private def ps : Array (BitVec 32) := #[2348818433, 2415927298, 2147491848, 2147492352, 2281717762, 2281717764, 2281717776, 2281718784, 2147516420, 2147516424, 2147516448, 2147518464, 2147549192, 2147549200, 2147549248, 2147553280, 2281832449, 2147614736, 2147614752, 2147614848, 2147745794, 2147745824, 2147745856, 2147746048, 2148007940, 2148008000, 2148008064, 2148008448, 2148532232, 2148532352, 2148532480, 2148533248, 2149580816, 2149581056, 2149581312, 2149582848, 2151677984, 2151678464, 2151678976, 2151682048, 2290089985, 2155872320, 2155873280, 2155874304, 2164260866, 2164260992, 2164262912, 2164264960, 2315255809, 2181038084, 2181038336, 2181042176]
private def ns : Array (BitVec 32) := #[2281763264, 2281793952, 2281816961, 2147661120, 2281886528, 2281894208, 2147691780, 2147714818, 2282048129, 2282063489, 2282078849, 2282117640, 2147945988, 2147953668, 2148054288, 2148085024, 2282325251, 2148154624, 2282379528, 2282387712, 2148238594, 2148285456, 2282510345, 2282525713, 2148416512, 2282641416, 2282834465, 2282911808, 2148731398, 2148808724, 2283035137, 2283049489, 2283065857, 2283080197, 2148932100, 2148939780, 2283166208, 2149070896, 2283311123, 2283341859, 2283358241, 2283542545, 2283558913, 2283573265, 2283827424, 2283897987, 2149749826, 2284081289, 2284098689, 2284114049, 2284127365, 2149979148, 2149987332, 2284343337, 2284360707, 2284389411, 2150241290, 2284590089, 2150503432, 2150641764, 2284884035, 2284900417, 2284912679, 2150797378, 2285375523, 2285391905, 2285922752, 2151719376, 2285945281, 2151754116, 2285980033, 2285994371, 2286010753, 2151819588, 2286045512, 2286053696, 2151876870, 2151950484, 2286225541, 2286241921, 2286438665, 2286453011, 2286487811, 2152335626, 2152401154, 2286684185, 2286700553, 2286977107, 2287011847, 2287208469, 2287273989, 2287470611, 2287732753, 2288025795, 2288042177, 2288058503, 2153906254, 2288255117, 2288271497, 2289041479, 2154954822, 2155917712, 2290144128, 2290151808, 2155946404, 2290172832, 2290180512, 2155971458, 2290242312, 2156040962, 2290275072, 2156069638, 2156171920, 2156179600, 2290406016, 2156270092, 2290504200, 2156409136, 2290635048, 2290643232, 2156531978, 2156564738, 2156933172, 2156958226, 2157056518, 2157187604, 2157195284, 2157318660, 2157482002, 2157981860, 2292215968, 2158104590, 2158235788, 2158243972, 2292469896, 2158497834, 2292731944, 2159083558, 2159546402, 2160099730, 2160132486, 2160197902, 2160263430, 2160337044, 2160591130, 2160722186, 2162163854, 2162229382, 2162294798, 2162425996, 2164303184, 2298528577, 2164335908, 2298561313, 2298578689, 2164401476, 2298626888, 2164426560, 2298659648, 2164492032, 2298775057, 2298807813, 2164721156, 2299019561, 2299069729, 2299085089, 2299266073, 2299298833, 2299544161, 2299560529, 2299593253, 2299789845, 2299855365, 2300592233, 2300642341, 2166498372, 2300838925, 2166752268, 2301101097, 2301166625, 2301624421, 2168463700, 2302689609, 2168586572, 2168594756, 2302820680, 2302935069, 2303197465, 2303230225, 2303459353, 2303754321, 2303983637, 2304770125, 2304786505, 2170683468, 2305818693, 2172657972, 2306884392, 2172781324, 2172846852, 2172912156, 2173043212, 2173174072, 2173182256, 2307408168, 2173698612, 2173764132, 2173960724, 2176844060, 2176852244, 2176975116, 2177105948, 2177368344, 2315282656, 2181115040, 2315340448, 2315348128, 2181138050, 2315405896, 2181203522, 2181238274, 2181268994, 2181311632, 2315537032, 2181334672, 2181342352, 2181369472, 2181377152, 2315602560, 2181400192, 2181434888, 2181573680, 2181696522, 2181762050, 2181827608, 2181958664, 2182097008, 2316323424, 2316331104, 2182120018, 2182154786, 2316388896, 2182220354, 2182251074, 2182678562, 2317369576, 2183169218, 2183267402, 2183660586, 2183726114, 2185242832, 2319476928, 2185265362, 2185365578, 2319599688, 2185496728, 2319730824]
private def ix : Array (Nat) := #[0, 1, 2, 4, 5, 6, 7, 8, 12, 13, 14, 16, 17, 18, 20, 21, 24, 25, 26, 27, 32, 33, 34, 35, 38, 39, 42, 45, 48, 49, 50, 51, 52, 53, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 79, 80, 82, 83, 86, 87, 88, 89, 90, 92, 94, 97, 98, 101, 102, 103, 106, 107, 108, 111, 112, 113, 115, 116, 118, 119, 120, 121, 122, 123, 125, 127, 129, 130, 131, 132, 135, 137, 138, 139, 141, 142, 146, 148, 149, 152, 154, 155, 156, 158, 159, 160, 162, 165, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 182, 183, 184, 185, 186, 187, 188, 189, 192, 194, 195, 196, 198, 201, 202, 204, 207, 208, 210, 213, 214, 215, 216, 218, 219, 223, 225, 227, 229, 232, 233, 235, 236, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 249, 250, 251, 253, 256, 257, 258, 261, 263, 266, 268, 270, 271, 273, 274, 276, 278, 280, 282, 283, 286, 287, 289, 290, 292, 294, 298, 299, 303, 304, 305, 306, 307, 309, 310, 313, 314, 315, 316, 317, 319, 320, 321, 325, 327, 328, 329, 330, 331, 332, 333, 335, 336, 337, 338, 339, 340, 341, 342, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 363, 366, 367, 368, 370, 371, 372, 373, 374, 375, 376, 377, 379, 383, 385, 387, 392, 394, 395, 397, 399, 400, 402, 403, 404, 406]
def group : BitVec 52 := 0xa240d46448500
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
end PEqualNP.Research.PlaneFlagFamilyA

open PEqualNP.Research.PlaneFlagFamilyA PEqualNP.Research.PlaneSingleFlagBound PEqualNP.Research.PlanePairAndCount in
theorem PEqualNP.Research.PlaneFlagFamilyA : ∀ (x : Sig) (e : Fin 52) (gs : List Gate) (o : Nat), group.getLsbD e.val = true →
    (∀ j : Fin 52, j ≠ e → x.1.getLsbD j.val = false) →
    (∀ j : Fin 52, readWire (gs.foldl step (evalRow x true j.val)) o = true) →
    (∀ i : Fin 468, readWire (gs.foldl step (evalRow x false i.val)) o = false) →
    9 ≤ gs.countP Prod.fst := bound ps ns ix group pRows nRows cert
