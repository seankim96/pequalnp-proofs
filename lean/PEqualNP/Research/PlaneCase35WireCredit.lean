import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace PEqualNP.Research.PlaneCase35WireCredit
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
def wire (s : List Column) (i : Nat) := s.getD i (fun _ => false)
def fixed (k : Fin 32) : Column :=
  if h : k.val < 30 then base ⟨k.val,h⟩
  else if k.val = 30 then mix true (input 13) (input 26) else mix true (input 13) (input 27)
def cheap (g : Bool × Nat × Nat) := g.1 && (g.2.1 == 32 || g.2.2 == 32)
def step (s : List Column) (g : Bool × Nat × Nat) :=
  if g.1 then s ++ [fun r => wire s g.2.1 r && wire s g.2.2 r]
  else s ++ [fun r => wire s g.2.1 r || wire s g.2.2 r]
abbrev G := Bool × Nat × Nat
def value (s : List Column) (g : G) (r : Nat) :=
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def possible (pred : G → Bool) (s : List Column) (g : G) := ∃ alt : G, pred alt = true ∧ ∀ r : Fin 520, value s alt r.val = value s g r.val
def free (g : G) := !g.1 || cheap g
noncomputable def credit (s : List Column) (g : G) : Nat := by
  classical
  exact if possible Prod.fst s g ∧ possible free s g then 1 else 0
noncomputable def auditStep (state : List Column × Nat) (g : G) := (step state.1 g,state.2 + credit state.1 g)
def pairs : List (G × Nat) := [((true,0,13),30), ((true,13,0),30), ((false,0,29),0), ((false,29,0),0), ((true,0,30),30), ((true,30,0),30), ((true,1,13),30), ((true,13,1),30), ((true,1,30),30), ((true,30,1),30), ((true,3,13),31), ((true,13,3),31), ((false,3,28),3), ((false,28,3),3), ((true,3,31),31), ((true,31,3),31), ((true,9,13),31), ((true,13,9),31), ((true,9,31),31), ((true,31,9),31), ((true,24,26),33), ((true,26,24),33)]
def replacement (g : G) := (pairs.find? (fun z => z.1 == g)).map Prod.snd
def charged (g : G) := cheap g || (replacement g).isSome
private abbrev eight := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
private def translate (g : G) : G := match replacement g with
  | some i => (false,i,i)
  | none => g
private abbrev better (a b : Column) :=
  (∀ p : Fin 52, a p.val = true → b p.val = true) ∧
  (∀ j : Fin 468, b (52+j.val) = true → a (52+j.val) = true)
private theorem transB {a b c : Column} (h : better a b) (k : better b c) : better a c :=
  ⟨fun p v => k.1 p (h.1 p v),fun j v => h.2 j (k.2 j v)⟩
private theorem combine {a b c d : Bool} (op : Bool) (h : a = true → c = true) (k : b = true → d = true) :
    (if op then a && b else a || b) = true → (if op then c && d else c || d) = true := by
  cases op <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.and_eq_true,Bool.or_eq_true]
  · exact Or.imp h k
  · exact fun z => ⟨h z.1,k z.2⟩
private def raw (k : Nat) (r : Nat) := if h : k < 32 then fixed ⟨k,h⟩ r
  else if k = 32 then fixed 2 r || fixed 6 r else fixed 1 r && fixed 24 r
private theorem rawEq (k : Fin 34) (r : Nat) : raw k.val r = wire eight k.val r := by
  have f : ∀ i : Fin 34, raw i.val r = wire eight i.val r := by
    intro i
    match i with
    | ⟨0,_⟩ => rfl
    | ⟨1,_⟩ => rfl
    | ⟨2,_⟩ => rfl
    | ⟨3,_⟩ => rfl
    | ⟨4,_⟩ => rfl
    | ⟨5,_⟩ => rfl
    | ⟨6,_⟩ => rfl
    | ⟨7,_⟩ => rfl
    | ⟨8,_⟩ => rfl
    | ⟨9,_⟩ => rfl
    | ⟨10,_⟩ => rfl
    | ⟨11,_⟩ => rfl
    | ⟨12,_⟩ => rfl
    | ⟨13,_⟩ => rfl
    | ⟨14,_⟩ => rfl
    | ⟨15,_⟩ => rfl
    | ⟨16,_⟩ => rfl
    | ⟨17,_⟩ => rfl
    | ⟨18,_⟩ => rfl
    | ⟨19,_⟩ => rfl
    | ⟨20,_⟩ => rfl
    | ⟨21,_⟩ => rfl
    | ⟨22,_⟩ => rfl
    | ⟨23,_⟩ => rfl
    | ⟨24,_⟩ => rfl
    | ⟨25,_⟩ => rfl
    | ⟨26,_⟩ => rfl
    | ⟨27,_⟩ => rfl
    | ⟨28,_⟩ => rfl
    | ⟨29,_⟩ => rfl
    | ⟨30,_⟩ => rfl
    | ⟨31,_⟩ => rfl
    | ⟨32,_⟩ => rfl
    | ⟨33,_⟩ => rfl
    | ⟨i+34,h⟩ => omega
  exact f k
private def rowGood (r : Nat) (pos : Bool) (g : G) (k : Nat) :=
  let v := if g.1 then raw g.2.1 r && raw g.2.2 r else raw g.2.1 r || raw g.2.2 r
  if pos then v = true → raw k r = true else raw k r = true → v = true
private def rowsGood (r : Nat) (pos : Bool) : Prop :=
  ∀ z ∈ pairs, rowGood r pos z.1 z.2
private theorem positiveRows : ∀ p : Fin 52, rowsGood p.val true := by unfold rowsGood rowGood; decide +kernel
private def silent (r : Nat) := raw 30 r = false ∧ raw 31 r = false ∧ raw 33 r = false
private theorem neg0 : ∀ t : Fin 12, silent (52+(12*0+t.val)) := by unfold silent; decide +kernel
private theorem neg1 : ∀ t : Fin 12, silent (52+(12*1+t.val)) := by unfold silent; decide +kernel
private theorem neg2 : ∀ t : Fin 12, silent (52+(12*2+t.val)) := by unfold silent; decide +kernel
private theorem neg3 : ∀ t : Fin 12, silent (52+(12*3+t.val)) := by unfold silent; decide +kernel
private theorem neg4 : ∀ t : Fin 12, silent (52+(12*4+t.val)) := by unfold silent; decide +kernel
private theorem neg5 : ∀ t : Fin 12, silent (52+(12*5+t.val)) := by unfold silent; decide +kernel
private theorem neg6 : ∀ t : Fin 12, silent (52+(12*6+t.val)) := by unfold silent; decide +kernel
private theorem neg7 : ∀ t : Fin 12, silent (52+(12*7+t.val)) := by unfold silent; decide +kernel
private theorem neg8 : ∀ t : Fin 12, silent (52+(12*8+t.val)) := by unfold silent; decide +kernel
private theorem neg9 : ∀ t : Fin 12, silent (52+(12*9+t.val)) := by unfold silent; decide +kernel
private theorem neg10 : ∀ t : Fin 12, silent (52+(12*10+t.val)) := by unfold silent; decide +kernel
private theorem neg11 : ∀ t : Fin 12, silent (52+(12*11+t.val)) := by unfold silent; decide +kernel
private theorem neg12 : ∀ t : Fin 12, silent (52+(12*12+t.val)) := by unfold silent; decide +kernel
private theorem neg13 : ∀ t : Fin 12, silent (52+(12*13+t.val)) := by unfold silent; decide +kernel
private theorem neg14 : ∀ t : Fin 12, silent (52+(12*14+t.val)) := by unfold silent; decide +kernel
private theorem neg15 : ∀ t : Fin 12, silent (52+(12*15+t.val)) := by unfold silent; decide +kernel
private theorem neg16 : ∀ t : Fin 12, silent (52+(12*16+t.val)) := by unfold silent; decide +kernel
private theorem neg17 : ∀ t : Fin 12, silent (52+(12*17+t.val)) := by unfold silent; decide +kernel
private theorem neg18 : ∀ t : Fin 12, silent (52+(12*18+t.val)) := by unfold silent; decide +kernel
private theorem neg19 : ∀ t : Fin 12, silent (52+(12*19+t.val)) := by unfold silent; decide +kernel
private theorem neg20 : ∀ t : Fin 12, silent (52+(12*20+t.val)) := by unfold silent; decide +kernel
private theorem neg21 : ∀ t : Fin 12, silent (52+(12*21+t.val)) := by unfold silent; decide +kernel
private theorem neg22 : ∀ t : Fin 12, silent (52+(12*22+t.val)) := by unfold silent; decide +kernel
private theorem neg23 : ∀ t : Fin 12, silent (52+(12*23+t.val)) := by unfold silent; decide +kernel
private theorem neg24 : ∀ t : Fin 12, silent (52+(12*24+t.val)) := by unfold silent; decide +kernel
private theorem neg25 : ∀ t : Fin 12, silent (52+(12*25+t.val)) := by unfold silent; decide +kernel
private theorem neg26 : ∀ t : Fin 12, silent (52+(12*26+t.val)) := by unfold silent; decide +kernel
private theorem neg27 : ∀ t : Fin 12, silent (52+(12*27+t.val)) := by unfold silent; decide +kernel
private theorem neg28 : ∀ t : Fin 12, silent (52+(12*28+t.val)) := by unfold silent; decide +kernel
private theorem neg29 : ∀ t : Fin 12, silent (52+(12*29+t.val)) := by unfold silent; decide +kernel
private theorem neg30 : ∀ t : Fin 12, silent (52+(12*30+t.val)) := by unfold silent; decide +kernel
private theorem neg31 : ∀ t : Fin 12, silent (52+(12*31+t.val)) := by unfold silent; decide +kernel
private theorem neg32 : ∀ t : Fin 12, silent (52+(12*32+t.val)) := by unfold silent; decide +kernel
private theorem neg33 : ∀ t : Fin 12, silent (52+(12*33+t.val)) := by unfold silent; decide +kernel
private theorem neg34 : ∀ t : Fin 12, silent (52+(12*34+t.val)) := by unfold silent; decide +kernel
private theorem neg35 : ∀ t : Fin 12, silent (52+(12*35+t.val)) := by unfold silent; decide +kernel
private theorem neg36 : ∀ t : Fin 12, silent (52+(12*36+t.val)) := by unfold silent; decide +kernel
private theorem neg37 : ∀ t : Fin 12, silent (52+(12*37+t.val)) := by unfold silent; decide +kernel
private theorem neg38 : ∀ t : Fin 12, silent (52+(12*38+t.val)) := by unfold silent; decide +kernel
private theorem negativeRows (j : Fin 468) : rowsGood (52+j.val) false := by
  have bat (i : Fin 39) (t : Fin 12) : silent (52+(12*i.val+t.val)) := by
    match i with
    | ⟨0,_⟩ => exact neg0 t
    | ⟨1,_⟩ => exact neg1 t
    | ⟨2,_⟩ => exact neg2 t
    | ⟨3,_⟩ => exact neg3 t
    | ⟨4,_⟩ => exact neg4 t
    | ⟨5,_⟩ => exact neg5 t
    | ⟨6,_⟩ => exact neg6 t
    | ⟨7,_⟩ => exact neg7 t
    | ⟨8,_⟩ => exact neg8 t
    | ⟨9,_⟩ => exact neg9 t
    | ⟨10,_⟩ => exact neg10 t
    | ⟨11,_⟩ => exact neg11 t
    | ⟨12,_⟩ => exact neg12 t
    | ⟨13,_⟩ => exact neg13 t
    | ⟨14,_⟩ => exact neg14 t
    | ⟨15,_⟩ => exact neg15 t
    | ⟨16,_⟩ => exact neg16 t
    | ⟨17,_⟩ => exact neg17 t
    | ⟨18,_⟩ => exact neg18 t
    | ⟨19,_⟩ => exact neg19 t
    | ⟨20,_⟩ => exact neg20 t
    | ⟨21,_⟩ => exact neg21 t
    | ⟨22,_⟩ => exact neg22 t
    | ⟨23,_⟩ => exact neg23 t
    | ⟨24,_⟩ => exact neg24 t
    | ⟨25,_⟩ => exact neg25 t
    | ⟨26,_⟩ => exact neg26 t
    | ⟨27,_⟩ => exact neg27 t
    | ⟨28,_⟩ => exact neg28 t
    | ⟨29,_⟩ => exact neg29 t
    | ⟨30,_⟩ => exact neg30 t
    | ⟨31,_⟩ => exact neg31 t
    | ⟨32,_⟩ => exact neg32 t
    | ⟨33,_⟩ => exact neg33 t
    | ⟨34,_⟩ => exact neg34 t
    | ⟨35,_⟩ => exact neg35 t
    | ⟨36,_⟩ => exact neg36 t
    | ⟨37,_⟩ => exact neg37 t
    | ⟨38,_⟩ => exact neg38 t
    | ⟨v+39,h⟩ => omega
  have hz : silent (52+j.val) := by simpa only [Nat.div_add_mod] using bat ⟨j.val/12,by omega⟩ ⟨j.val%12,by omega⟩
  obtain ⟨a,b,c⟩ := hz
  simp [rowsGood,pairs,rowGood,a,b,c]; exact ⟨Or.inl,Or.inr,Or.inl,Or.inr⟩
private theorem witness (g : G) (k : Nat) (h : replacement g = some k) :
    g.2.1 < 34 ∧ g.2.2 < 34 ∧ k < 34 ∧ better (value eight g) (wire eight k) := by
  have mem : (g,k) ∈ pairs := by
    unfold replacement at h
    cases e : pairs.find? (fun z => z.1 == g) with
    | none => simp [e] at h
    | some z =>
      have eq : z.1 = g := beq_iff_eq.mp (List.find?_some (p := fun z : G × Nat => z.1 == g) e)
      have ek : z.2 = k := by simpa [e] using h
      simpa only [←eq,←ek] using List.mem_of_find?_eq_some e
  have canonical (r : Nat) (pos : Bool) (hr : rowsGood r pos) : rowGood r pos g k := hr (g,k) mem
  have bounded : ∀ z ∈ pairs, z.1.2.1 < 34 ∧ z.1.2.2 < 34 ∧ z.2 < 34 := by decide +kernel
  have bounds := bounded (g,k) mem
  obtain ⟨l,u,v⟩ := bounds
  refine ⟨l,u,v,?_,?_⟩
  · intro p
    simpa only [rowGood,ite_true,rawEq ⟨_,l⟩,rawEq ⟨_,u⟩,rawEq ⟨_,v⟩,value] using canonical p.val true (positiveRows p)
  · intro j
    simpa only [rowGood,Bool.false_eq_true,ite_false,rawEq ⟨_,l⟩,rawEq ⟨_,u⟩,rawEq ⟨_,v⟩,value] using canonical (52+j.val) false (negativeRows j)
private theorem snoc (s : List Column) (x : Column) (j : Nat) :
    wire (s ++ [x]) j = if j = s.length then x else wire s j := by
  by_cases h : j < s.length
  · rw [ite_eq_right (show j ≠ s.length by omega)]; exact List.getD_append _ _ _ _ h
  · rw [wire,List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : j = s.length
    · simp [e]
    · rw [ite_eq_right e,wire,List.getD_eq_default _ _ (show [x].length ≤ j-s.length by simp; omega),
          List.getD_eq_default _ _ (show s.length ≤ j by omega)]
private theorem stepEq (s : List Column) (g : G) : step s g = s ++ [value s g] := by
  cases g with | mk op ab => cases op <;> rfl
private theorem sim (gs : List G) (s t : List Column) (len : s.length = t.length)
    (large : 34 ≤ s.length) (fixedCols : ∀ j < 34, wire s j = wire eight j)
    (h : ∀ j, better (wire s j) (wire t j)) : ∀ j,
    better (wire (gs.foldl step s) j) (wire ((gs.map translate).foldl step t) j) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step s g) (step t (translate g)) (by simp [stepEq,len]) (by simp [stepEq]; omega)
    · intro j hj; rw [stepEq,snoc,ite_eq_right (show j ≠ s.length by omega),fixedCols j hj]
    · intro j
      simp only [stepEq,snoc,len]
      split
      · cases e : replacement g with
        | none =>
          simp only [translate,e]
          exact ⟨fun p => combine g.1 ((h g.2.1).1 p) ((h g.2.2).1 p),
                 fun i => combine g.1 ((h g.2.1).2 i) ((h g.2.2).2 i)⟩
        | some k =>
          obtain ⟨a,b,c,w⟩ := witness g k e
          have v : value s g = value eight g := by funext r; simp only [value,fixedCols _ a,fixedCols _ b]
          rw [v]
          rw [← fixedCols _ c] at w
          have idcopy : value t (translate g) = wire t k := by
            funext r
            simp [translate,e,value]
          rw [idcopy]
          exact transB w (h k)
      · exact h j
private theorem counted (s : List Column) (g : G) (hit : charged g = true) :
    credit s (translate g) = 1 := by
  classical
  cases e : replacement g with
  | some i =>
    have a : possible Prod.fst s (false,i,i) := ⟨(true,i,i),rfl,by simp [value]⟩
    have b : possible free s (false,i,i) := ⟨(false,i,i),rfl,fun _ => rfl⟩
    simp [credit,translate,e,a,b]
  | none =>
    have ch : cheap g = true := by simpa [charged,e] using hit
    have a : possible Prod.fst s g := ⟨g,(Bool.and_eq_true_iff.mp ch).1,fun _ => rfl⟩
    have b : possible free s g := ⟨g,by simp [free,ch],fun _ => rfl⟩
    simp [credit,translate,e,a,b]
private theorem count (gs : List G) (s : List Column) (n : Nat) :
    n + gs.countP charged ≤ ((gs.map translate).foldl auditStep (s,n)).2 := by
  induction gs generalizing s n with
  | nil => simp
  | cons g gs ih =>
    have z := ih (step s (translate g)) (n + credit s (translate g))
    simp only [List.map_cons,List.foldl_cons,auditStep,List.countP_cons]
    cases e : charged g <;> simp only [e,Bool.false_eq_true,ite_false,ite_true] at ⊢ <;>
      first | omega | rw [counted s g e] at z ⊢; omega
end PEqualNP.Research.PlaneCase35WireCredit
open PEqualNP.Research.PlaneCase35WireCredit in
theorem PEqualNP.Research.PlaneCase35WireCredit (sizeBound : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + (gs.foldl auditStep (pool,0)).2 ≤ 8 + gs.length) : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := step (step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
  (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
  35 + gs.countP charged ≤ 8 + gs.length := by
  intro gs o pool hp hn
  have tr := sim gs pool pool rfl (by decide) (fun _ _ => rfl) (fun _ => ⟨fun _ => id,fun _ => id⟩) o
  have bound := sizeBound (gs.map translate) o (fun p => (tr.1 p) (hp p)) (fun j => by
    cases e : wire ((gs.map translate).foldl step pool) o (52+j.val) with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (((tr.2 j) e).symm.trans (hn j))))
  have z := count gs pool 0
  change 35 + ((gs.map translate).foldl auditStep (pool,0)).2 ≤ 8 + (gs.map translate).length at bound
  simp only [List.length_map] at bound
  omega
