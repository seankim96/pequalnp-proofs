import PEqualNP.Research.PlanePairAndCount
import PEqualNP.Research.PlaneFlagOrTail

namespace PEqualNP.Research.PlaneCode858AndCount
open PlanePairAndCount

def positives : Array (BitVec 32) := #[2348818433, 2415927298, 2147491848, 2147492352, 2281717762, 2281717764, 2281717776, 2281718784, 2147516420, 2147516424, 2147516448, 2147518464, 2147549192, 2147549200, 2147549248, 2147553280, 2818703361, 2147614736, 2147614752, 2147614848, 2147745794, 2147745824, 2147745856, 2147746048, 2148007940, 2148008000, 2148008064, 2148008448, 2148532232, 2148532352, 2148532480, 2148533248, 2149580816, 2149581056, 2149581312, 2149582848, 2151677984, 2151678464, 2151678976, 2151682048, 2290089985, 2155872320, 2155873280, 2155874304, 2164260866, 2164260992, 2164262912, 2164264960, 2315255809, 2181038084, 2181038336, 2181042176]
def negatives : Array (BitVec 32) := #[2281763264, 2281793952, 2281816961, 2281863488, 2147661120, 2281886528, 2281894208, 2147691780, 2147714818, 2147792016, 2282017409, 2147822724, 2282048129, 2282063489, 2282078849, 2147892228, 2282117640, 2147945988, 2147953668, 2282256672, 2148054288, 2148085024, 2282309921, 2282325251, 2148154624, 2282379528, 2282387712, 2148177154, 2148207874, 2148285456, 2282510345, 2282525713, 2148408328, 2148416512, 2282780768, 2282803777, 2282834465, 2148677700, 2282904128, 2282911808, 2148700738, 2148731398, 2148808724, 2283035137, 2283049489, 2283065857, 2283080197, 2283096577, 2148932100, 2148939780, 2149070896, 2283296801, 2283311123, 2283341859, 2283358241, 2283542545, 2283558913, 2283573265, 2283827424, 2149627072, 2283851969, 2149655716, 2283897987, 2149725252, 2149749826, 2149856388, 2284081289, 2284098689, 2284114049, 2284127365, 2284160129, 2149979148, 2149987332, 2284343337, 2284360707, 2284389411, 2284422147, 2150241290, 2284590089, 2284605449, 2284622849, 2150641764, 2284867681, 2284884035, 2284900417, 2284912679, 2150764614, 2285375523, 2285391905, 2285408259, 2285436963, 2285922752, 2151719376, 2285945281, 2151754116, 2285980033, 2285994371, 2286010753, 2151819588, 2286045512, 2286053696, 2151876870, 2151950484, 2286176393, 2286225541, 2286241921, 2286438665, 2286453011, 2286487811, 2286504193, 2286518531, 2152335626, 2286684185, 2286700553, 2152736852, 2286977107, 2287011847, 2152859718, 2287208469, 2287273989, 2287470611, 2287501331, 2287536131, 2287732753, 2288009417, 2288025795, 2288042177, 2288058503, 2288091267, 2153906254, 2288255117, 2288271497, 2288320645, 2289041479, 2289074243, 2289106951, 2290119072, 2155917712, 2290144128, 2290151808, 2155946404, 2290172832, 2290180512, 2155971458, 2290205568, 2290242312, 2156040962, 2290275072, 2156069638, 2156102402, 2156146836, 2290373256, 2156171920, 2156179600, 2290406016, 2156270092, 2290504200, 2156409136, 2290635048, 2290643232, 2156433682, 2156531978, 2290766088, 2156564738, 2156933172, 2156958226, 2156986918, 2157056518, 2157089282, 2157117958, 2157187604, 2157195284, 2157220368, 2157318660, 2157449266, 2157482002, 2157981860, 2292207784, 2292215968, 2158035110, 2158104590, 2158235788, 2158243972, 2292469896, 2158366732, 2158497834, 2292731944, 2158628874, 2159022118, 2159083558, 2159153158, 2159546402, 2160075156, 2160099730, 2160132486, 2160165250, 2160197902, 2160263430, 2160328860, 2160337044, 2160591130, 2160623890, 2160722186, 2162163854, 2162229382, 2162294798, 2162425996, 2164303184, 2298528577, 2164335908, 2298561313, 2298578689, 2298594049, 2164401476, 2298626888, 2164426560, 2164434240, 2164459268, 2164466948, 2298775057, 2298807813, 2298840577, 2164655628, 2164794672, 2299019561, 2299036945, 2299069729, 2299085089, 2299102465, 2299266073, 2299298833, 2165317748, 2299544161, 2299560529, 2299576897, 2299593253, 2299609633, 2299789845, 2299822609, 2299855365, 2166367332, 2300592233, 2300642341, 2166490188, 2166498372, 2300838925, 2300904453, 2301101097, 2301116457, 2301166625, 2301363209, 2301624421, 2301640801, 2301689893, 2168463700, 2302689609, 2302706001]
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

def testRow (pos : Bool) (i : Nat) : Row :=
  (PlaneFlagOrTail.start 858).map fun x => if pos then x.1.getLsbD i else x.2.getLsbD i

private def indices : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 33, 34, 35, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 59, 60, 62, 63, 64, 65, 67, 68, 69, 70, 71, 73, 74, 75, 76, 78, 79, 80, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 98, 99, 101, 102, 103, 104, 107, 108, 109, 110, 111, 112, 113, 115, 116, 118, 119, 120, 121, 122, 123, 125, 126, 127, 129, 130, 131, 132, 133, 134, 135, 138, 139, 140, 141, 142, 143, 146, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 223, 224, 225, 226, 227, 229, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 254, 255, 257, 258, 259, 260, 262, 263, 264, 266, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 285, 286, 287, 288, 290, 291, 292, 293, 294, 296, 297, 298, 299, 300]
private theorem posRows : ∀ i : Fin 52, row positives[i.val]! = testRow true i.val := by decide +kernel
private theorem negRows : ∀ i : Fin 257, indices[i.val]! < 468 ∧ row negatives[i.val]! = testRow false indices[i.val]! := by decide +kernel

end PEqualNP.Research.PlaneCode858AndCount

open PEqualNP.Research.PlanePairAndCount PEqualNP.Research.PlaneCode858AndCount in
theorem PEqualNP.Research.PlaneCode858AndCount : ∀ (gs : List Gate) (o : Nat),
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
