import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.PlaneCase35FirstOrFree

def positive : Array Nat := #[
    8193, 8194, 8200, 8704, 16386, 16388, 16400, 17408, 32772, 32776, 32800, 34816, 65544, 65552,
    65600, 69632, 131073, 131088, 131104, 131200, 262146, 262176, 262208, 262400, 524292, 524352, 524416, 524800,
    1048584, 1048704, 1048832, 1049600, 2097168, 2097408, 2097664, 2099200, 4194336, 4194816, 4195328, 4198400, 8388609, 8388672,
    8389632, 8390656, 16777218, 16777344, 16779264, 16781312, 33554433, 33554436, 33554688, 33558528]

def negative : Array Nat := #[
    61888, 92576, 115585, 162112, 177472, 185152, 192832, 208132, 231170, 308368, 316033, 339076, 346753, 362113,
    377473, 408580, 416264, 462340, 470020, 555296, 570640, 601376, 608545, 616736, 623875, 670976, 678152, 686336,
    693506, 701696, 724226, 732416, 754946, 801808, 808969, 824337, 832528, 924680, 932864, 940040, 1079392, 1102401,
    1133089, 1194052, 1202752, 1210432, 1217090, 1233472, 1247750, 1325076, 1333761, 1348113, 1364481, 1378821, 1395201, 1448452,
    1456132, 1464832, 1509892, 1587248, 1595425, 1603616, 1609747, 1640483, 1656865, 1841169, 1849360, 1857537, 1871889, 2126048,
    2143424, 2150593, 2158784, 2172068, 2196611, 2241604, 2266178, 2274368, 2372740, 2379913, 2397313, 2405504, 2412673, 2425989,
    2434180, 2458753, 2495500, 2503684, 2641961, 2659331, 2688035, 2720771, 2757642, 2790402, 2888713, 2904073, 2921473, 3019784,
    3158116, 3166305, 3174496, 3182659, 3199041, 3211303, 3280966, 3289156, 3313730, 3674147, 3690529, 3706883, 3735587, 4221376,
    4235728, 4243905, 4252096, 4270468, 4278657, 4286848, 4292995, 4309377, 4335940, 4344136, 4352320, 4393222, 4401412, 4466836,
    4475017, 4524165, 4532356, 4540545, 4737289, 4751635, 4786435, 4802817, 4817155, 4851978, 4868360, 4917506, 4982809, 4999177,
    5253204, 5275731, 5310471, 5376070, 5384260, 5441542, 5507093, 5515284, 5572613, 5769235, 5799955, 5834755, 6031377, 6308041,
    6324419, 6340801, 6357127, 6389891, 6422606, 6553741, 6570121, 6619269, 7340103, 7372867, 7405575, 7471174, 8417696, 8434064,
    8442752, 8450432, 8462756, 8471456, 8479136, 8487810, 8504192, 8540936, 8557314, 8573696, 8585990, 8618754, 8663188, 8671880,
    8688272, 8695952, 8704640, 8786444, 8802824, 8925488, 8933672, 8941856, 8950034, 8958224, 9048330, 9064712, 9081090, 9449524,
    9474578, 9503270, 9572870, 9605634, 9634310, 9703956, 9711636, 9736720, 9835012, 9965618, 9973808, 9998354, 10498212, 10506408,
    10514592, 10551462, 10559652, 10620942, 10752140, 10760324, 10768520, 10883084, 11014186, 11030568, 11145226, 11538470, 11546660, 11599910,
    11669510, 12062754, 12591508, 12616082, 12624272, 12648838, 12657028, 12681602, 12714254, 12779782, 12845212, 12853396, 13107482, 13140242,
    13238538, 14680206, 14745734, 14811150, 14942348, 16819536, 16827201, 16852260, 16859937, 16877313, 16892673, 16917828, 16925512, 16942912,
    16950592, 16958272, 16975620, 16983300, 17008384, 17073681, 17106437, 17139201, 17171980, 17237508, 17311024, 17318185, 17335569, 17343760,
    17368353, 17376544, 17383713, 17401089, 17564697, 17597457, 17834100, 17842785, 17859153, 17875521, 17891877, 17908257, 18088469, 18121233,
    18153989, 18883684, 18890857, 18940965, 18949156, 19006540, 19014724, 19137549, 19203077, 19268620, 19399721, 19415081, 19465249, 19661833,
    19923045, 19931236, 19939425, 19988517, 20980052, 20988233, 21004625, 21012816, 21020993, 21102924, 21111108, 21119304, 21233693, 21496089,
    21512457, 21528849, 21757977, 22020181, 22028372, 22052945, 22282261, 23068749, 23085129, 23199820, 23330829, 24117317, 25174324, 25183016,
    25232164, 25239844, 25248544, 25297676, 25314056, 25363204, 25428508, 25559564, 25690424, 25698608, 25706792, 26214964, 26222644, 26280484,
    26477076, 29360412, 29368596, 29491468, 29622300, 29884696, 33581280, 33596624, 33631392, 33639072, 33646752, 33654402, 33704520, 33719874,
    33754626, 33785346, 33827984, 33835656, 33851024, 33858704, 33885824, 33893504, 33901184, 33916544, 33951240, 33966600, 34016768, 34090032,
    34147362, 34155552, 34212874, 34278402, 34343960, 34352144, 34475016, 34613360, 34622048, 34629728, 34636370, 34671138, 34687520, 34736706,
    34753088, 34767426, 34802178, 35129394, 35137584, 35194914, 35661024, 35668200, 35676384, 35685570, 35693760, 35718306, 35726496, 35751042,
    35783754, 35816514, 36176938, 36242466, 36307978, 37759184, 37767368, 37775552, 37781714, 37789904, 37881930, 37898312, 38013080, 38021264,
    38029448, 38275098, 38406154, 38537240, 38799442, 38807632, 38830162, 38930498, 39323666, 39846090, 39862472, 39878850, 39977034, 41960104,
    41976466, 42009250, 42025632, 42041986, 42205848, 42222216, 42238608, 42467386, 42992178, 43024914, 43057698, 43515954, 44040362, 44056744,
    44105890, 44564522, 46137498, 46170258, 46399640, 46661658, 48234634, 50340976, 50348648, 50366032, 50373712, 50464328, 50479688, 50497088,
    50595352, 50628112, 50726408, 50857016, 50865200, 51119128, 51380848, 51388528, 51397216, 51413584, 52429928, 52438112, 52445288, 52560968,
    52954152, 58720824, 58737192, 58982936, 59244600, 59769392]

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) := s ++ [fun r => wire s g.1 r || wire s g.2 r]
abbrev Gate := Bool × Nat × Nat
def step (s : List Column) (g : Gate) : List Column :=
  if g.1 then s ++ [both (wire s g.2.1) (wire s g.2.2)] else addOr s g.2

def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 ||| b 1) <<< 26) ||| ((b 3 ||| b 9) <<< 27)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def mix (op : Bool) (a b : Column) : Column := fun r =>
  if op then a r && b r else a r || b r
def base (i : Fin 30) : Column :=
  if i.val < 28 then input i.val
  else if i.val = 28 then mix true (input 15) (input 27)
  else mix true (input 17) (input 26)

private def negatives : Array (Fin 468) := #[421, 270, 41, 158, 135]
private def positives : Array (Array (Fin 52)) := #[
  #[1, 4, 10, 12, 13, 14, 15, 18, 21, 26, 29, 34, 36, 42, 43, 44, 48, 49, 50],
  #[2, 7, 9, 12, 17, 21, 23, 24, 25, 27, 28, 32, 38, 42, 44, 45, 46, 47, 48],
  #[0, 4, 6, 8, 10, 11, 15, 16, 22, 25, 28, 29, 30, 31, 34, 39, 41, 47, 51],
  #[1, 4, 8, 14, 16, 18, 19, 20, 25, 28, 32, 33, 34, 35, 38, 39, 41, 44, 49],
  #[1, 4, 11, 12, 16, 17, 20, 24, 25, 26, 27, 28, 35, 36, 38, 39, 43, 46, 50]]
private def negRow (t : Fin 5) := 52 + (negatives[t.val]!).val
private def flag (t : Fin 5) (i : Fin 19) : Fin 52 := positives[t.val]![i.val]!
variable (t : Fin 5)
private def supp (x : Column) : Finset (Fin 19) :=
  if x (negRow t) then ∅ else Finset.univ.filter (fun i => x (flag t i).val)
private def Count (s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp t (s.getD j (fun _ => false)))).card ≤ q + W.card

private theorem cutOr (x y : Column) : supp t (mix false x y) ⊆ supp t x ∪ supp t y := by
  cases hx : x (negRow t) <;> cases hy : y (negRow t) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp t (mix true x y) ⊆ supp t (if x (negRow t) then y else x) := by
  cases hx : x (negRow t) <;> cases hy : y (negRow t) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Column} {q c : Nat} (h : Count t s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp t v ⊆ parents.biUnion (fun j => supp t (s.getD j (fun _ => false)))) : Count t (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp t ((s ++ [v]).getD j (fun _ => false))) ⊆
        U.biUnion (fun j => supp t (s.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp t v := by simpa using hij
        obtain ⟨a,ha,hai⟩ := Finset.mem_biUnion.mp (sub hv)
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_right _ ha,hai⟩
      · have hd : (s ++ [v]).getD j (fun _ => false) = s.getD j (fun _ => false) := by
          by_cases hj : j < s.length
          · exact List.getD_append _ _ _ _ hj
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩),hd ▸ hij⟩
    have hc := Finset.card_union_le (W.erase s.length) parents
    rw [Finset.card_erase_of_mem incl] at hc
    have hw := Finset.card_pos.mpr ⟨_,incl⟩
    have hU := h U
    have := Finset.card_le_card hs
    change U.card ≤ _ at hc
    omega
  · have eq : W.biUnion (fun j => supp t ((s ++ [v]).getD j (fun _ => false))) =
        W.biUnion (fun j => supp t (s.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega


private theorem appendGate {s : List Column} {q : Nat} (h : Count t s q) (op : Bool) (i j : Nat) :
    Count t (s ++ [mix op (wire s i) (wire s j)]) (q+(!op).toNat) := by
  cases op
  · apply grow t h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
    simpa [wire] using cutOr t (wire s i) (wire s j)
  · let k := if wire s i (negRow t) then j else i
    apply grow t h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd t (wire s i) (wire s j)
    change _ ⊆ supp t (wire s k)
    cases e : wire s i (negRow t) <;> simpa only [k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) {s : List Column} {q : Nat} (h : Count t s q) :
    Count t (gs.foldl step s) (q+gs.countP (fun g => !g.1)) := by
  induction gs generalizing s q with
  | nil => simpa using h
  | cons g gs ih =>
    obtain ⟨op,i,j⟩ := g
    have next := appendGate t h op i j
    have eq : step s (op,i,j) = s ++ [mix op (wire s i) (wire s j)] := by cases op <;> rfl
    simp only [List.foldl_cons,eq]
    cases op <;> simpa [List.countP_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih next

private theorem orSmall (x y : Column)
    (hx : x (negRow t) = true ∨ ∀ f : Fin 19, x (flag t f).val = false)
    (hy : (supp t y).card ≤ 1) : (supp t (mix false x y)).card ≤ 1 := by
  rcases hx with h | h
  · simp [supp,mix,h]
  · apply le_trans (Finset.card_le_card (show supp t (mix false x y) ⊆ supp t y from ?_)) hy
    cases he : x (negRow t) <;> cases hf : y (negRow t) <;>
      simp [supp,mix,he,hf,Finset.subset_iff,h]

private theorem addSmall {s : List Column} (h : Count t s 0) (v : Column)
    (hv : (supp t v).card ≤ 1) : Count t (s ++ [v]) 0 := by
  have small (i : Nat) : (supp t (wire s i)).card ≤ 1 := by
    simpa [wire] using h {i}
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i < s.length
  · rw [List.getD_append _ _ _ _ hi]; exact small i
  · by_cases he : i = s.length
    · subst i; simpa using hv
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [supp]

-- A signature records all 52 positive rows and the five selected negative rows.
private def signatures : Array Nat := #[
  0x0, 0x1, 0x2, 0x3, 0x4, 0x8,
  0xc, 0xf, 0x10, 0x20, 0x40, 0x80,
  0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000,
  0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000,
  0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000,
  0x4000000, 0x8000000, 0x10000000, 0x20000000, 0x40000000, 0x80000000,
  0x100000000, 0x200000000, 0x400000000, 0x800000000, 0x1000000000, 0x2000000000,
  0x4000000000, 0x8000000000, 0x10000000000, 0x20000000000, 0x40000000000, 0x80000000000,
  0x100000000000, 0x200000000000, 0x400000000000, 0x800000000000, 0x1000000000000, 0x2000000000000,
  0x4000000000000, 0x8000000000000, 0x10000000000000, 0x10000000001000, 0x1000000000f000, 0x10001000240400,
  0x10010000000000, 0x100f0000000000, 0x10200024080000, 0x11000000000000, 0x1f000000000000, 0x20000000000000,
  0x20000000100000, 0x20000000f00000, 0x20000100022040, 0x20044080000080, 0x20100000000000, 0x20f00000000000,
  0x40000000000000, 0x40000000000010, 0x400000000000f0, 0x40000000000200, 0x40000000000f00, 0x40000010000000,
  0x400000f0000000, 0x48808000008000, 0x50000000000000, 0x50002408000008, 0x60000000000000, 0x61010000010001,
  0x80000000000000, 0x80000400000000, 0x80000f00000000, 0x82000001000120, 0xc0000000000000, 0xc0020002404000,
  0x100000000000000, 0x100480800000800, 0x104000240800000, 0x120000000000000, 0x120000008000000, 0x12000000f000000,
  0x180000000000000, 0x180000000010000, 0x1800000000f0000, 0x180002000000000, 0x18000f000000000, 0x190000000000000,
  0x190100000100012, 0x1a0000000000000, 0x1a0000010001204, 0x1f0000000000000, 0x1f000241800120c, 0x1f1110000110013,
  0x1ffffffffffffff]
private def word (i : Fin 109) : Nat := signatures[i.val]!
private def generators : Array (Fin 109) := #[
  83, 102, 87, 104, 68, 59,
  89, 62, 92, 81, 69, 91,
  79, 7, 74, 76, 58, 98,
  67, 95, 78, 86, 100, 61,
  71, 64, 107, 106, 75, 97]
-- Each seven-bit field indexes the intersection of two signatures.
private def intersections : Array Nat := #[
  0x53a74a94182000000050a00830608000024480000000a74a4489122448912244883060c183060b4680162c000000000000340000000000002c00000000000000000000000000000000000000001400000000000000000000002000000200080,
  0x66cd972e0c19b2e0c183060b56ad5ab56aa54a952a540001c380000000002040060c0000306003870e1c3870e1c3800000000000030000000000000000000000000000000000000000018000000000000000000000000000804000000408000,
  0x57a952a54a952a54a952a5438000000002a54af52a540000000000000c002400000000000000035000000000000000001a8000000000000000000000000000000000000000001c000000000000000000000000000c000048000000000000000,
  0x68cfa33e8cf83060c183060bb76edab56aa54a952a548304000008100d1a0000083060c183060800000000004080000000000000000000000000000000000000000002000000000000000000000000000100000680000000008100040000000,
  0x4483060c18200000005400083060800000000009000083040000000000002800083060c4830608000000000044000000000000000000000000000000000000240000000000000000000000000a8000008800000000002800000000000000000,
  0x3b70e1c0000e1c2800580000000000000000000000000001c38000000e00000000000000320003870e1c3876e1c3800000000000000000000000000280000000000000000000000000c80005800000000000038000000000000000000000000,
  0x59b162c54a952a54a952a543a000000002cd8a952a5491224489122448912244800000003400000000168000480000000000000000000016800000000000000000000000000e800068000000000000480000000000000000000000000000000,
  0x3e70e1c0000e1c00005c0003c00000000000000000000001c38008400000000006200000000003870f9c3870e1c38000000000018800000000000000000000000001080007800000000002e0000000000000000000000000000000000000000,
  0x5cb56ad5ab56ad5ab56ad5ab56ad5cb5680000094000000000000880000000000000000036000360000000000000000d80000000000000000000000000001280008800000000003600000000000000000000000000000000000000000000000,
  0x51a14680000e1c2952000003e7c0000002448009930091228d0912244891224480000000000003870e1c3870e1c380000000000000000000000001480009800000000003e00000000000000000000000000000000000000000a142800000000,
  0x4583060c1820002a00000008306080000000000000008304000008c000002c00083062c18306080000170000000000000000000000000b800000a80000000000460000000000000000000000000000000000000000160000000000000000000,
  0x5bb56ad5ab56ad5ab56ad5ab56ad5ab768000009c0000000000000000f00000006400000000000000017800000000000000000c80005e0000000000004e00000000000000000000000000000000000000001e00000000000000000000000000,
  0x4f9122400000002b000000000000000002448000000091224489f224489122448660000000000370000000004c0006e000006600000000000056000000000000000000000000000000000000000026000000000000000000000000000000000,
  0x706180040008000000000000000000000000000000002002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e182840608080,
  0x4a93224000020000000000000000000002448120000091224489122448912a4c8000058a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000162848800000000000000,
  0x4c912e40d0000000000000000000001e0244818000009122448912244c97224480000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000000000000001e3868c000000000000000000000,
  0x3a70e5c1000e1c0000000000000000000090000000000001c38260000000000000000011000003870e1c3870e9cb800000000000000000000000000000000000000000000000000000000000000026488900000000000000000000000000000,
  0x62c383060c183060c18b0e0b56ad5ab56aa54a952a5428000000000000000000000000150000000005c0002c00000000000000000000000000000000000000000000000000000000000002e58a9400000000000000000000000000000000000,
  0x4385060c182600000000000830609b0000d00000000083040000000000000000083060c1870a0800000000320000000000000000000000000000000000000000000000000000003668c98000000000000000000000000000000000000000000,
  0x5fbb7aeddbb6ad5ab56ad5abf7aedab568e8038000008304f800000000000000083060c18306080007800000000000000000000000000000000000000000000000000003e78e9c0000000000000000000000000000000000000000000000000,
  0x4e9136420000000000000000000022000244800000009122448913a6c8912244800011800000000008400000000000000000000000000000000000000000000046890a000000000000000000000000000000000000000000000000000000000,
  0x56a956a54a952a54a952a5400000254e02a54a95aad4000130000000000000000000002400000000000000000000000000000000000000000000000004e992a4000000000000000000000000000000000000000000000000000000000000000,
  0x64c18f060c183064c783060b56ad5ab56aa54a952a54000148056000000000000000150000000000000000500000000000000000000000000056a94a80000000000000000000000000000000000000000000000000000000000000000000000,
  0x3d78e1c0000e1c00000000000000005e0168000000005801c38000000000000000001700000003870e1ebc70e1c38000000000000005eb96ac00000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x478d060c182c000000000008306080640000000000008304000660000000000008f1a0c1830608000c40000000000000000066c98b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x407ee1c0000e1c000000000000003600000006a000006801c386e000000000000000000000000407ee1c3870e1c386ed9ab40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x6bd7a74e7cf9b2e0c1870e0bb76edab56ac58a952a54a74a850912244891264c88d1a0c1850a0bf7ee1e3c70e1c3800000340000030000002c00000000000000000000000000000000018000001400000000000000000000806000000608080,
  0x6ad3ab4e8cf972e3c783060bd7aedab56ac58a956ad4a54a8d091366cb972244883060c183060b870e1c3870e5cb80000000000000000000000001480009800000000203e00000000000000000000000010000068000000000c182840000000,
  0x4b912e40d000000000000000000000000244800000009122448912244b9722448000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000680000000000000000000000,
  0x61c383060c183060c1870e0b56ad5ab56aa54a952a54280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001400000000000000000000000000000000000]
private def witnesses : Array (Fin 5) := #[
  0, 0, 1, 1, 0, 0,
  0, 0, 1, 0, 0, 0,
  0, 0, 1, 0, 2, 1,
  1, 1, 0, 0, 1, 0,
  0, 2, 0, 0, 0, 0,
  1, 0, 0, 1, 0, 0,
  0, 0, 1, 0, 1, 0,
  0, 0, 0, 0, 2, 1,
  2, 0, 0, 0, 2, 1,
  1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 1, 1, 1, 1, 1,
  0, 1, 2, 0, 2, 0,
  2, 2, 0, 0, 0, 1,
  0, 1, 3, 3, 0, 2,
  0, 4, 4, 0, 0, 1,
  0, 0, 3, 0, 3, 0,
  0, 0, 1, 0, 0, 0,
  0]

private def meetIndex (i : Fin 30) (j : Fin 109) : Fin 109 :=
  Fin.ofNat 109 ((intersections[i.val]! >>> (7*j.val)) &&& 127)
private theorem row0 : ∀ j : Fin 109, word (meetIndex 0 j) = word (generators[0]!) &&& word j := by decide +kernel
private theorem row1 : ∀ j : Fin 109, word (meetIndex 1 j) = word (generators[1]!) &&& word j := by decide +kernel
private theorem row2 : ∀ j : Fin 109, word (meetIndex 2 j) = word (generators[2]!) &&& word j := by decide +kernel
private theorem row3 : ∀ j : Fin 109, word (meetIndex 3 j) = word (generators[3]!) &&& word j := by decide +kernel
private theorem row4 : ∀ j : Fin 109, word (meetIndex 4 j) = word (generators[4]!) &&& word j := by decide +kernel
private theorem row5 : ∀ j : Fin 109, word (meetIndex 5 j) = word (generators[5]!) &&& word j := by decide +kernel
private theorem row6 : ∀ j : Fin 109, word (meetIndex 6 j) = word (generators[6]!) &&& word j := by decide +kernel
private theorem row7 : ∀ j : Fin 109, word (meetIndex 7 j) = word (generators[7]!) &&& word j := by decide +kernel
private theorem row8 : ∀ j : Fin 109, word (meetIndex 8 j) = word (generators[8]!) &&& word j := by decide +kernel
private theorem row9 : ∀ j : Fin 109, word (meetIndex 9 j) = word (generators[9]!) &&& word j := by decide +kernel
private theorem row10 : ∀ j : Fin 109, word (meetIndex 10 j) = word (generators[10]!) &&& word j := by decide +kernel
private theorem row11 : ∀ j : Fin 109, word (meetIndex 11 j) = word (generators[11]!) &&& word j := by decide +kernel
private theorem row12 : ∀ j : Fin 109, word (meetIndex 12 j) = word (generators[12]!) &&& word j := by decide +kernel
private theorem row13 : ∀ j : Fin 109, word (meetIndex 13 j) = word (generators[13]!) &&& word j := by decide +kernel
private theorem row14 : ∀ j : Fin 109, word (meetIndex 14 j) = word (generators[14]!) &&& word j := by decide +kernel
private theorem row15 : ∀ j : Fin 109, word (meetIndex 15 j) = word (generators[15]!) &&& word j := by decide +kernel
private theorem row16 : ∀ j : Fin 109, word (meetIndex 16 j) = word (generators[16]!) &&& word j := by decide +kernel
private theorem row17 : ∀ j : Fin 109, word (meetIndex 17 j) = word (generators[17]!) &&& word j := by decide +kernel
private theorem row18 : ∀ j : Fin 109, word (meetIndex 18 j) = word (generators[18]!) &&& word j := by decide +kernel
private theorem row19 : ∀ j : Fin 109, word (meetIndex 19 j) = word (generators[19]!) &&& word j := by decide +kernel
private theorem row20 : ∀ j : Fin 109, word (meetIndex 20 j) = word (generators[20]!) &&& word j := by decide +kernel
private theorem row21 : ∀ j : Fin 109, word (meetIndex 21 j) = word (generators[21]!) &&& word j := by decide +kernel
private theorem row22 : ∀ j : Fin 109, word (meetIndex 22 j) = word (generators[22]!) &&& word j := by decide +kernel
private theorem row23 : ∀ j : Fin 109, word (meetIndex 23 j) = word (generators[23]!) &&& word j := by decide +kernel
private theorem row24 : ∀ j : Fin 109, word (meetIndex 24 j) = word (generators[24]!) &&& word j := by decide +kernel
private theorem row25 : ∀ j : Fin 109, word (meetIndex 25 j) = word (generators[25]!) &&& word j := by decide +kernel
private theorem row26 : ∀ j : Fin 109, word (meetIndex 26 j) = word (generators[26]!) &&& word j := by decide +kernel
private theorem row27 : ∀ j : Fin 109, word (meetIndex 27 j) = word (generators[27]!) &&& word j := by decide +kernel
private theorem row28 : ∀ j : Fin 109, word (meetIndex 28 j) = word (generators[28]!) &&& word j := by decide +kernel
private theorem row29 : ∀ j : Fin 109, word (meetIndex 29 j) = word (generators[29]!) &&& word j := by decide +kernel
private theorem meetWord (i : Fin 30) (j : Fin 109) :
    word (meetIndex i j) = word (generators[i.val]!) &&& word j := by
  fin_cases i
  · exact row0 j
  · exact row1 j
  · exact row2 j
  · exact row3 j
  · exact row4 j
  · exact row5 j
  · exact row6 j
  · exact row7 j
  · exact row8 j
  · exact row9 j
  · exact row10 j
  · exact row11 j
  · exact row12 j
  · exact row13 j
  · exact row14 j
  · exact row15 j
  · exact row16 j
  · exact row17 j
  · exact row18 j
  · exact row19 j
  · exact row20 j
  · exact row21 j
  · exact row22 j
  · exact row23 j
  · exact row24 j
  · exact row25 j
  · exact row26 j
  · exact row27 j
  · exact row28 j
  · exact row29 j
private def Rep (x : Column) (i : Fin 109) :=
  (∀ p : Fin 52, x p.val = (word i).testBit p.val) ∧
  (∀ t : Fin 5, x (negRow t) = (word i).testBit (52+t.val))
private theorem rawRep : ∀ j : Fin 30, Rep (base j) (generators[j.val]!) := by
  unfold Rep
  decide +kernel
private theorem falseRep : Rep (fun _ => false) 0 := by unfold Rep; decide +kernel
private theorem trueRep : Rep (fun _ => true) 108 := by unfold Rep; decide +kernel
-- A conjunction acts on every previously certified signature. Composition
-- handles arbitrary AND gates using associativity and only 30 generator rows.
private def Acts (x : Column) := ∀ y : Column, ∀ i : Fin 109, Rep y i →
  ∃ j : Fin 109, Rep (mix true x y) j
private theorem rawActs (j : Fin 30) : Acts (base j) := by
  intro y i hy
  refine ⟨meetIndex j i, ?_⟩
  have hx := rawRep j
  constructor
  · intro p; simp [mix,meetWord,Nat.testBit_and,hx.1 p,hy.1 p]
  · intro k; simp [mix,meetWord,Nat.testBit_and,hx.2 k,hy.2 k]
private theorem falseActs : Acts (fun _ => false) := by
  intro y i _
  have e : mix true (fun _ => false) y = fun _ => false := by funext r; simp [mix]
  exact ⟨0,e ▸ falseRep⟩
private theorem trueActs : Acts (fun _ => true) := by
  intro y i hy
  have e : mix true (fun _ => true) y = y := by funext r; simp [mix]
  exact ⟨i,e ▸ hy⟩
private theorem signature {x : Column} (h : Acts x) : ∃ i : Fin 109, Rep x i := by
  obtain ⟨i,hi⟩ := h _ _ trueRep
  have e : mix true x (fun _ => true) = x := by funext r; simp [mix]
  exact ⟨i,e ▸ hi⟩
private theorem andActs {x y : Column} (hx : Acts x) (hy : Acts y) : Acts (mix true x y) := by
  intro z i hz
  obtain ⟨j,hj⟩ := hy z i hz
  obtain ⟨k,hk⟩ := hx _ j hj
  have e : mix true (mix true x y) z = mix true x (mix true y z) := by
    funext r; exact Bool.and_assoc ..
  exact ⟨k, e ▸ hk⟩
private def mask (k : Fin 5) (i : Fin 109) : Finset (Fin 19) :=
  if (word i).testBit (52+k.val) then ∅ else
    Finset.univ.filter (fun f => (word i).testBit (flag k f).val)
private theorem smallMask : ∀ i : Fin 109, ∀ k : Fin 5, (mask k i).card ≤ 1 := by decide +kernel
private theorem repSmall {i : Fin 109} {x : Column} (h : Rep x i) (k : Fin 5) :
    (supp k x).card ≤ 1 := by
  have eq : supp k x = mask k i := by simp only [supp,mask,h.1,h.2]
  rw [eq]; apply smallMask
private def Easy (x : Column) (k : Fin 5) :=
  x (negRow k) = true ∨ ∀ f : Fin 19, x (flag k f).val = false
private theorem canChoose : ∀ i : Fin 109, i ≠ 7 →
    let k := witnesses[i.val]!
    (word i).testBit (52+k.val) = true ∨ ∀ f : Fin 19, (word i).testBit (flag k f).val = false := by
  decide +kernel
private theorem easy {x : Column} {i : Fin 109} (h : Rep x i) (ne : i ≠ 7) :
    Easy x (witnesses[i.val]!) := by
  simpa only [Easy,h.1,h.2] using canChoose i ne
private theorem freeOr {x y : Column} {i j : Fin 109} (hx : Rep x i) (hy : Rep y j) :
    ∃ k : Fin 5, (supp k (mix false x y)).card ≤ 1 := by
  by_cases hi : i = 7
  · by_cases hj : j = 7
    · subst i; subst j
      have rep : Rep (mix false x y) 7 := by
        constructor
        · intro p; simp [mix,hx.1 p,hy.1 p]
        · intro k; simp [mix,hx.2 k,hy.2 k]
      exact ⟨0,repSmall rep 0⟩
    · have comm : mix false x y = mix false y x := by funext r; exact Bool.or_comm ..
      rw [comm]
      exact ⟨_,orSmall _ _ _ (easy hy hj) (repSmall hx _)⟩
  · exact ⟨_,orSmall _ _ _ (easy hx hi) (repSmall hy _)⟩

private def Closed (s : List Column) := ∀ j : Nat, Acts (wire s j)
private theorem appendActs {s : List Column} (h : Closed s) (v : Column) (hv : Acts v) :
    Closed (s ++ [v]) := by
  intro j
  by_cases lt : j < s.length
  · simpa only [wire,List.getD_append _ _ _ _ lt] using h j
  · by_cases eq : j = s.length
    · subst j; simpa [wire] using hv
    · rw [wire,List.getD_eq_default _ _ (show (s++[v]).length ≤ j by simp; omega)]; exact falseActs
private theorem beginClosed : Closed (List.ofFn base) := by
  intro j
  by_cases lt : j < 30
  · rw [wire,List.getD_eq_getElem _ _ (show j < (List.ofFn base).length by simpa using lt), List.getElem_ofFn]; exact rawActs ⟨j,lt⟩
  · rw [wire,List.getD_eq_default _ _ (show (List.ofFn base).length ≤ j by simpa using Nat.le_of_not_gt lt)]; exact falseActs
private theorem start {s : List Column} (hs : Closed s) (k : Fin 5) : Count k s 0 := by
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨_,h⟩ := signature (hs j)
  exact repSmall h k
private theorem finish (k : Fin 5) (gs : List Gate) {s : List Column} (h : Count k s 0) (o : Nat)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52+n.val) = false) :
    18 ≤ gs.countP (fun g => !g.1) := by
  have cost := run k gs h {o}
  have full : supp k (wire (gs.foldl step s) o) = Finset.univ := by
    have nh : wire (gs.foldl step s) o (negRow k) = false := hn (negatives[k.val]!)
    simp only [supp,nh,Bool.false_eq_true,ite_false]
    exact Finset.filter_true_of_mem (fun i _ => hp (flag k i))
  simp only [Finset.singleton_biUnion,Finset.card_singleton] at cost
  change (supp k (wire _ o)).card ≤ _ at cost
  rw [full] at cost
  simp only [Finset.card_univ,Fintype.card_fin] at cost
  omega

private theorem beforeFirstOr (gs : List Gate) {s : List Column} (h : Closed s) (o : Nat)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52+n.val) = false) :
    19 ≤ gs.countP (fun g => !g.1) := by
  induction gs generalizing s with
  | nil => have bad := finish 0 [] (start h 0) o hp hn; simp at bad
  | cons g gs ih =>
    obtain ⟨op,a,b⟩ := g
    cases op
    · obtain ⟨_,hi⟩ := signature (h a)
      obtain ⟨_,hj⟩ := signature (h b)
      obtain ⟨k,hk⟩ := freeOr hi hj
      have cost := finish k gs (addSmall k (start h k) _ hk) o hp hn
      simp; omega
    · have next := appendActs h _ (andActs (h a) (h b))
      simpa [List.countP_cons] using ih next hp hn
end PEqualNP.Research.PlaneCase35FirstOrFree
open PEqualNP.Research.PlaneCase35FirstOrFree in
theorem PEqualNP.Research.PlaneCase35FirstOrFree : ∀ (gs : List Gate) (o : Nat),
    let pool := List.ofFn base ++ [fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    19 ≤ gs.countP (fun g => !g.1) := by
  intro gs o pool hp hn
  have h : Closed pool := by
    simpa [pool,List.append_assoc] using
      appendActs (appendActs beginClosed _ falseActs) _ trueActs
  exact beforeFirstOr gs h o hp hn
