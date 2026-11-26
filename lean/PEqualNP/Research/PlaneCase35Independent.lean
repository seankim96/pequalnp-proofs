import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace PEqualNP.Research.PlaneCase35Independent.Separation

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) : List Column :=
  s ++ [fun r => wire s g.1 r || wire s g.2 r]
def good (p a b : Nat) (w : Column) := w p = true → w a = true ∨ w b = true

def separated (s : List Column) :=
  ∃ n : Fin 257 → Fin 468, ∀ i j : Fin 257, i.val < j.val →
    ∃ p : Fin 52, ∀ w ∈ s, good p.val (52 + (n i).val) (52 + (n j).val) w

end PEqualNP.Research.PlaneCase35Independent.Separation

namespace PEqualNP.Research.PlaneCase35Independent.AndCount
open Separation
abbrev Gate := Bool × Nat × Nat
def step (s : List Column) (g : Gate) : List Column :=
  if g.1 then s ++ [both (wire s g.2.1) (wire s g.2.2)] else addOr s g.2

private def trace (s : List Column) (r : Nat) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let tail := trace (step s g) r gs
    if g.1 then 2 * tail + (wire s g.2.1 r).toNat else tail

private theorem trace_lt (s : List Column) (r : Nat) (gs : List Gate) :
    trace s r gs < 2 ^ (gs.countP Prod.fst) := by
  induction gs generalizing s with
  | nil => simp [trace]
  | cons g gs ih =>
    have h := ih (step s g)
    cases op : g.1
    · simpa [trace,List.countP_cons,op] using h
    · have count : (g :: gs).countP Prod.fst = gs.countP Prod.fst + 1 := by simp [op]
      simp only [trace,op,ite_true,count,Nat.pow_succ]
      cases hx : wire s g.2.1 r <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

private theorem readGood {s : List Column} {p a b : Nat} (all : ∀ w ∈ s, good p a b w) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases h : s[j]? with
  | none => simp [good]
  | some w => exact all w (List.mem_of_getElem? h)

private theorem preserve (gs : List Gate) (s : List Column) (p a b : Nat)
    (h : ∀ w ∈ s, good p a b w) (eq : trace s a gs = trace s b gs) :
    ∀ w ∈ gs.foldl step s, good p a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace (step s g) a gs = trace (step s g) b gs := by
      cases op : g.1 <;> simp [trace,op] at eq <;>
        cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all <;> omega
    apply ih _ _ tail
    intro w hw
    have l := readGood h g.2.1
    have r := readGood h g.2.2
    cases op : g.1
    · simp only [step,op,Bool.false_eq_true,ite_false,addOr,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · unfold good at *
        simp only [Bool.or_eq_true] at *
        tauto
    · simp only [step,op,ite_true,List.mem_append,List.mem_singleton] at hw
      rcases hw with old | rfl
      · exact h _ old
      · have same : wire s g.2.1 a = wire s g.2.1 b := by
          simp [trace,op,tail] at eq
          cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all
        unfold good both at *
        simp only [Bool.and_eq_true] at *
        rw [same] at l ⊢
        tauto

theorem separated_bound (s : List Column) (gs : List Gate) (o : Nat)
    (sep : separated s)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52 + n.val) = false) :
    9 ≤ gs.countP Prod.fst := by
  obtain ⟨n,h⟩ := sep
  let f (i : Fin 257) : Fin (2 ^ (gs.countP Prod.fst)) :=
    ⟨trace s (52 + (n i).val) gs,trace_lt _ _ _⟩
  have distinct (i j : Fin 257) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,hp0⟩ := h i j lt
    have remain := preserve gs s _ _ _ hp0 (congrArg Fin.val eq)
    have bad := (readGood remain o) (hp p)
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Fin.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at card
  by_contra h
  have le : gs.countP Prod.fst ≤ 8 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP Prod.fst ≤ 256 at bound
  omega
end PEqualNP.Research.PlaneCase35Independent.AndCount

namespace PEqualNP.Research.PlaneCase35Independent.Data
open Separation AndCount
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


def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 ||| b 1) <<< 26) ||| ((b 3 ||| b 9) <<< 27)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def mix (op : Bool) (a b : Column) : Column := fun r =>
  if op then a r && b r else a r || b r
def source (c : Column) (k : Fin 29) := if k.val < 28 then input k.val else c

end PEqualNP.Research.PlaneCase35Independent.Data

namespace PEqualNP.Research.PlaneCase35Independent.Certificate
open Separation AndCount Data
set_option maxRecDepth 8192
set_option maxHeartbeats 0
-- Each bit marks one of the first eight positive flags, grouped on lines 0 and 1.
private def omittedFlags : Nat := 255
private def indices (i : Nat) : Nat :=
  (0x190c6e33178ac4e230f85c1e02ff7dbe5eef377bb5cee570b7dbad96bb55a2cf64b1582bf5eaed72b758abd5aab54a9d46a14fa6d2a9348a3d1685409fcfa7b3b9d4e66f369acce652f964aa532692c9245219047e3b1b8cc622f168a44a210f8743615088341609038140600fe7dbe5eef579bc9e2f077bb9daec753a5d0e772b8dc4e17037dbadc6d365acd569b419ecd6632d92c863b198ac461b0980be5dae56cb459ac960af56aa94ea652a9146a250a7d3c9d4e26932984ba592a94492451e8e46a31148943a190883411fcfa7b3c1d8e670379b8da6b351a0ce6531184c05e2e970b65a2c960ac55299409c4c25928924622910823f1f0ec74371a8cc6230170ac54291409446211007838190c05428130883c1a0b048200e04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0x64080d224028d0e2a040a6290422e28042a6228442e22044a621848262104a262084c222024e061908226180832e130a02e128242e120a42e110a22e1082522102870a0e0c08a0c0c1860b0c02e0a0c0a6090c222082c30a070e00a060e08a058680a050e80a0486902042c90e038602e030e02e028642a024a48e0186822012ca0200a4d020068e09c801189c4001c9c2010c9c0011c9940214991022499002349880138986020c984021c9830304982030c981032418021345700045d64000d962004cd60004d554001555080515500055d4c00195488111d480119d44001d942014c5408151140215453100255300065d2c04095290421d280429926040c5250405d24040d922044c52104251202464d150205d148211d140215d110225d108251110207450c8411d0c041950985015090521508851110825309070604906060cd058601d050605d0486119038700903070490287401022544d0187011012524100a5508e4008cce2000e4e10086ce0008ecca010a4c88112cc8011a8c4009c4c30106cc2010e4c181824c101864c081920c021944b810224b210064b100264b01026caa100aca8102a8a6100c8a4108cca2100e4a100a60a030a449890124981032896120489492108941214c930206c929202c921206c910226c909212090303448a9102c8a110a48891120883130886120c88492900843094c838302c830306c8293028825308c81838208121a4080b19008071a047200464710007470804347000474650085c64008dc62004e4618083461008746080c3c6040c945c08114590803458801345808134550805454081545308064520846451080745080530502854c4c081944b0902c4a090a449810344909034488113c484909445088504428944430906042294444181830412984040a1d004069c04390023438900343810234329042432104643100274309043030306482e140842c9401c2c140942a9402c2a140a429840342904234289403c285029826140c425848142504854249481024348442294420223444421848302124a4020b4c002070e041c901141c18114190823418901301838308170a048161a04c150a05c1492110143814c130a06c1292420123844c114a21c10d241010786080e1c0840c941100c3c1040b850240b0d0240a950200a3d0040985030092d20008b51000879208070e040063c04c0586810052c84004b490c0387020032d04002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x8000200800000840000024000001200000010000000800000040000002000000100000008000000400000020000001000000080000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x7c07df01df0000003e03fd00000007f837c000000000000000001ed80052215000d1010f1d1c5c2d8020801b6807c000904018800a20001518000001000002ff7f1c07400000000000000007efbf363ee1d1e79cf3e28fe1f02830301d00800000000000000dfebed7df1c200000000000007dff9a7c47333dc478c3208204fffffffffe0000000000000000000000000000000000000000000000000000000000000000fffffffffffffffe0000000000000000000000000000000000000000000000007ffe000000000000ffffffffffffe000000000000000000000000018000000003c00fffc000000007ffe000000000fffffffff800000000000000003fe00000000007801ffc000003c00ffe0000007ff0000003ffffffc000000000000ff000000e02380c01f80000000780ffe0003c07ff0001fe00001fffe000000e0607e00040800381c003f0000e0230600f000003c07f00e0ff800f800ffe000000030fc0123049209c7187c04080060e007000c118206000703e063e0700f8026071661e041610080900031e12304a84e3278410030c0c062610c018e27863c08ca42accc04280009252196cc4161020480331262545959080c6184a48332d9a15090055500000910004aa2d5042800492a554428810a0a52552aa90925545aa00000000000000000000000000001bf7edff330000000003dfce79ed6df33499401dbfeaaa0000000000000000000000000000000dfbd7d40000001bdb6aae951ff00fffee00000003fe07fffe000000000000000000000001feffc0001ffbfc0001f01f7c077c000000f80ff40000001fe0df0000000000000000007b60014880000000002c4f00dc0000783f877e0000078ff000001f9f800000000000ff07fc1e0001e1e0000000000000002c4f01600018786f000033c0000f3c0000001c3e331b000330002d8740a1800320000000000002c980b00263600066003600006462e28600283860006c31450020002d1a05100a000000000a502805280500a0058010d10c0b6d10fec003798408386003619b0200168e12100000006c603020802a001a2021e3a38b85b00410036d00f8001208031001440002a300000020000000000000007effe8dc7f681a55e3ab9f2da15137a07d01e81a00aa80ed0003482ff7f1c07400000000000000007efbf363ee1d1e79cf3e28fe1f02830301d00800000000000000dfebed7df1c200000000000007dff9a7c47333dc478c3208204 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0x97ffffffffff83f6bfffffff2e6ff2ffffffff1ff0ffffffffffff8ff6bf4ff2fffe6ff2fff93fff1ffffffffffffabffffffffff2738ffffffd94bfff1ff0fccffffffffffffffffff2b38fffff6bffe0ff1ff0ffffffffffffffffff48c2b38ffff2fd9fffff1ff0889ffffffffffdf67ffffff3fffff24fffffff1ffffffffffffffffff67ffff27f8ffff24fffffff1fff8bfffffffffffff6bffffffffffff2fce2a0ff1ff0fffffffffffffff6bffff2bf8ffff2fcefffff1fff8bffffffffe6fff6bf4ceff3fffffffff2a0ff1fffffffffffffe6fff6bf4ce2b38fffffffffffff1fff6ffffffffffffffffffff2f3fdfff2fd9fcdff1ff0fffffffffffffffffffcd2f3fdfff2fd9fffff1ff0fffffffffffffff6fffff2fffdfffffce4bf731ffffffffffffffffff6fffffff32dfff277ffd1ff1ff0fffffffffffffff6fffce2fffffff277f4bf731ffffffffffffffffff6ff4bf2fffdfff2fcefffff1ff0fffffffffffffff6ff47fff3fffff277f2bfff1ff0fffffffffffffff67f48e2f3ffffff77ffffff1ffffff53fffffe68ffffffff2f3fff6fffff551ff1ffffffff0ffffe6ffffff47f2f3ffffff6bf57fff1fff6ccfffffffe6ffffd4fff2fffffff2fff4bfff1fffffffffffffff8fffd4fcc2fffffff2fd94bfff1ff0fccfffffffff8dffff4bf2fffffff26bffcdff1ffffffffffeefe68dffd548d2f3fffffffd9fffff1ffffff53ffffffffff6fffff2ffffffff4d657f331ffffffffffffffffff6fffcc2fffffff24d6fffff1ffffff530fffffffff6ffffffff2ffff2fd6fcdff1ffffffffffffffffff6ff4ff2fffffffffd654dff1ffffffffffedffffff6fffcdff32ffff2fd6fffff1ffffffffffffffffff6bf4cd2fffffff2fd6fffff1ffffffffffffffffdf6d4ffffff2ffff24cefffff1ffffffffffffffffdf6d4fff2fffffffffce4bf331fffffffffffffff89f6fffcefff2ffff24fffffff1ff0ffffffffffff8dc6d6fce2fffffff24fffffff1fffffffffffffff8bf6d44ffff32ffff2fcefffff1fffffffffffffff8df6954ff2fffffff2fcefffff1fffffffffffffe681f6964ceff3fffff2fff2bfff1fffffffffffffe48dd6964ce2f3ffffffffffffff1ffffffb28ffffff87ffff47f27fbbfffffff93ffd8ffffffb28fffffffdcfff47fffffea957b7fffffffffffffb3fffffffffffd7fccfffbbf97ffe9911fffffffffb3ffffffffff61747fffffeafffb6993ffffffffffb28ffffe5ffffff47ffeffeaffffff57f73fffffffb28ffffff8bffd5ffffffbbffdefe9fcdfffffffffb3fffffffffffd5fcdfeffeafdefe9fffffffffffffffffffe487fffffff2afbaaffffffffffd8ffffffb28fffffffffffffccfeffeafd7b69fd1fffffffffb3fffffe5fdcfff47ffeffeafd7fe9ffffffffffffb3fffffffffffd7fffffffeafffb6949133fffffffb3fffffe5ffffd7fccfefbbfffffe9491fffffffffb3ffffffffde6d74bfffffeafffb69fcdfffffffffb3fffffe4fde61748dfeffffffffe9ffffffffffdcfffffffffffffd643ffefffffe1b7f920fffb3ffffffffffa3ffffffffccfffba6fffb56920fffb3ffffb10fffffffdcfd6fffffffe6961b7f93ffffffffffffffffffffdcfd643ffffffffe1b7f93ffffb3f95cffffffa3ffffffffcd23fba6ffffd6ffffffb3f97fffffffffffff67fffffffffffdeb7f93ffc8b3fffffffffffff83ffd6fff23fbbffdefff93ffffb3fffffffffffff83fffffff27fba6fd7fffffffd8b3f949fffffffffffffffffffefba6ffffd9ffffd8b3ffffffffffa3f87ffd7fff27fba6ffffffffffd8ffffffffffffa3f81c63f47fffffe6fd7b7fffffffb3ffffb3ffffa7f87ffd7fff27fba6ffffff911ffffff97fffffffffffde67fffffffba6fffb7fffffc8b3ffffb3ffffa7f85e65747f23fffffffb7f93fffffff8bffffffffffffffd5ffffeffdffe1fceffffffb3fffffffffffe4ffffd6fcefefb9ffe1ffffe0fffb3fffffffffffffffffff43f26fbbfffffd9560fd8ffffccffffffffffffffffff2bfbbffe1fd9ffffd8b3fffffffffffffffffd5fcc2afbbffe1fd9ffffd8b3ffffb10ffffe6fffffffccfefbbf8bffd6fe0ffffff88cffffffffffdffff43f23fffffffb7f560fffb3fffffffffffe6fff63f40cfeffffffffd6fe0fffb3ffffb3fffffe6ffffd6ffffeffff8a1fff4a0fffffffffffffffffffdf615ffffffffffe1b4effffffb3ffffb3fffffe6fdf65648efffffffe1b7ffffffffffffffffffffffffffff43ffffb9ffffb5654d73fb3ffffffffffffffff6fffcdfeffdfffffd6ffffc8b3ffffffffffa25fffffffcd22ffdfffffff57f73fb3ffffffffffa3f8bffd5ffffffbbffdefcefcdfffb3fffffffffffe5fff6d647ffefffffdeb7f2bffc8b3ffffb3ffffa6483ffd6fce2bfbbffdeffffffffffff6c9fffffffffffffffffffefbbffd7b5957ffd8b3fffffffffffe683fffffff27fbbffd7fffffffd8b3f6fffffffffff87ffffffffefbbfffffff28dfd8b3ffffffffffabf87fffffff2bfbbffffffffcdfd8fffffffffffffe6ffffd7fcdfeffffffffd92bffd8b3ffffffffffaa687ffd7fcd2bfbbfffffffffffd8ffffffb10fffabf8bffffffffffbbffd7b7ffd133fffffffb3ffffabf8bfffffccfefbbffd7fd6fd1fffffffffffffffffffdf6ff43ffffffffd7b56fcdfc8fffffffffffffff89ffff43f23fbbffd7ffffcdfffb3ffffffffffffffdf6fffcdfefffffffb56fff248ffffffb10fffffffff6d7ffffffffffffb4efff308ffffffb3ffffabfffffd7fff23fbbfffffce49133fffffffb10fffffffdf6fffcefefbbffffb7ffd1fc8ffffffb3ffffaa687ffd7fce23fbbfffffff4bffffffffffffffffffffdf6d743ffffffffffb4effffc8ffffffb3ffffabf85f6174bf2bfffffffb4efffffffffffffffffffe6fdf65744efffffffffb7fffffc8ffffff528ffffffffffff4fffe7feafe1fff920fffffffffffffffffffdcfd4ffffe7feafe14e9ffffffffffccffffffffffddffffffffffeafe1fff920ffffe8fffffffffffffddfd44ccfe7feafe1fe9fffffffffffffffffffff87fffffff267afffffffffd1fd8fe8fc9ffffffffffdeffffcdfe7feafff6bfffffd8fe8fffffffecfff87ffff47f267affffffffffffd8ffffff53ffedfff81dfffffffe7aeafd7ffffffffffff94cffffecffffde63fffffffaeafff4ffffffffffffffffffecfff85e63ffccfffaea97f4fffffffffff97fffffffffffff6bffffffffeaffffe990dfc8fe8fccfffffffff85efff4ff23faeaffffff90dffffff97fffffffffffff6bffcdfe7feaffffe9ffffc8fffffffe8fedfff85e6974cd23ffeaffffe993ffffffffdcffffffffffffffffff2bfaeafff77ffe0fd8fe889cfffffffe7ffffd4fff23ffeaffffe94bfffffff8bfffffecfe4ffffffffffcfaeafff77ffffffffe88bffffffffe7fff63f48fffffeafff769fe0fffffffffffffffffffffffffff27faeafe1fff4bffd8fe8fffffffffffffdcfff4bf2bfaeafe1fe9ffffd8fe8fff528fffffffffffffffffffea8a14e9fe0fffffffff528ffffe7ffffff4ffffffeafe1fff560ffffffffffffffffe7fdc614fffffffea8a14ffffffffffffccfffffffe4fddfffffffcffeafe1fe9fffffffffffffffffffe7fdd6954cfffffeafe1fe9fffffffff6fffffffffffffffff47fffffeafdefe92bffd8fe8ffffffffffff83fffffff2bfafffdefffffffd8fe8fff528ffffffffffffffffffaeafdefff55173fffffff528fffffffff6ff44ffffffffff769ffffc8ffffff53ffeffe7ffffff47f23faeafff77f57ffffffffffffffecfe5fffffffff20faeafdefff4bffffffffffffffffffffff6fffcfffffeafdefe9fd1fc8fffffffffffffe78bffd4fcf23faeaffffff4bf73fffffffffffecfe58bffff4bffcfaeafdefe9ffffffffffffffffffffffff6d444ffffffffdefe9ffffc8fffffffe8feffe783f61548f2bffeafff769fffffffff6c9fffffffe7fdeffffffffffeaffffe9491fd8fffffffffffffe787fffffff27faff6fffff491fd8fffffffffffffe7fdefff47fffffeafff6bf2bffd8ffffffffffeffe785efff4bf2bfafffff6bfffffd8ffffff528feffff89cffffffffffeafd7fe9fd1fffffffffffffffffffdd6fffcfffffeafd7fe9ffffc8ffffff53ffeffe781dfff4ff23ffeafd7fff57ffffffffffffffffffffde6ffffffcffeafff4e9ffffc8ffffffffffecfe5fdeffffff20ffeaffffff4bf33fffffffffffffffffde6fffcffffffffff4e9fd1248ffffffffffeffe789e6d7fcf27ffeaffffe94bfffffffffffffffffe5fff6ff4fffcfaeaffffe9ffffc8fe8fffffffedfe485efff4ff28faeafffffffffffffffffffffffffe7fde6974cfffffffffffe92bffc8ffffffffffeffe785e6974cf2bfaeaffffffffffffffffdcffffeca7ffffffffff2278e6fffffffffffffd0fffffffffa3fffffd4fff23f8e6fff74e920ffffff97fffffffffffff67fffffe7fe6fff77ffe0fc8ffffffffffeca7fffffff40e23f8e6fff77f93ffffffffccffffeda3fffffffffffff8e6fe1fd6fe0fff53ffffffffeda3ffffffffccfff8e6ffffd6920fff53ffffffffeca7ffdcfd6ffffe78e6fe14fffffffffff97fffffffffffff6bffffffffe6fe1fceffffc8ffffccffffffa3ffddfd4fff23ffe6fe1fff920ffffff949fffc3fffffdd6bffceffffe6fe1fff93ffc8fffffffffc2da7ffddfd64ce27ffe6fe1fff93ffffffffdcffffffffffffffffff2e7fe6ffffd993ffd853ffdcfffffffffffffff43f2ffffffde77f90dfd8fffffffffffffffffffd4fcdfe72e6fdefd9ffffd8ffffdcfffffffffffffd4fcd2ffffffdefd993ffd8fff95cffffffafffffffffffffffe6fff75690dfff53ffffffffeeffffff63ffcdfe7fe6fff756ffffff53f97fffffffaffffffd4fffffffe6fdefce93fffffd0ffffffc7faff8ffffffcefe7fe6fdeffffd1ffffd0fffffffffaff8ff61443fffffe6fff74e93fffffff97fffffecfff83f67fffffe7fe6fff77f93ffc8ffffffffffeeaff8ff65644e2fffe6fde77f93ffffffffffffffeeffffdcfff47f2fffe6fd7fd993ffd8ffffccffffffffffdeffffff2fffe6ffffd993ffd8fd0fffffffffafffffffffcc2fffe6ffffd993ffd8fd0fffffffffa3ffdefffffffff2e6fff6bf90dfd8ffffccffffffffffdefff43f2ffffffff6bf90dfd8ffffffffffeca3ffdeffffcdfff2e6fff6bf93ffd8ffffffffffeeafffdefd740c2fffffffffd993ffd8ffffffffffffaff8ddffffffffffe6fd7fd6fcdfff53ffff53ffeeaff8dd6bffcdffffe6fd7fd6ffffffffffffffffffafffde63ffffffffe6fff4cefffffffd0ffffd0caeaff8de67ffcefe7fe6fff4fffffffffff97fffffffa3f87f6bffffffffe6ffffce93ffc8ffffffffffffaff8de6974ff2fffe6ffffce93fffffff97ffffcada7f85e6bffcefe72ffffffffffffc8fffffffffcaeaff8de6974ce2e7fe6ffffffffffffffffdcffffffffffffffffff28f8dfffffffffffd8fffffffffffffffffffff40fffffdffe1fd92a0fd8ffffdcffffffa3ffffffffcf2bf8dfffffd9ffffd8fff8bfffffffffffff67fffffff8dffff77fffffc8fd0fffffffffa67fffffffff23f8dfffffff4bfffffd08bfffffeca24fff63fffffcf8dffffffffffffffff8bffffffffe7fff67f43ffffffffff77f2a0fc8ffffffffffefa67fff67f48f2bf8dffff77fffffffffffff510fffffffffffffff27f8fffe1fff57ffd8ffffc9ffffffffffffffffcffffffffe1699fe0fd853ffffffffeffffffffff43f27f8ffffffd9560fd8ffffc9fffcffffffdffd4ffffffffffe1fd9ffffd8fd0ffffffcffabfffffd4fff27f8ffffffff4bffd8fd0fffffffffffffdffd443ffcfffffe16bf2a0fd8ffffccfffc2cffffdfffffff28f8ffffffffffffd8ffffffffffffffffdffd440ffffffffe1fd92a0fd8fffffffffcefa3ffdcfd548f2bf8ffffffd9ffffd8ffffff53ffefabffff63fffffff8fffff4d6fe0ffffff8bfffffffffffff6bfffffcf8ffffffd6ffffc853ffffffffedfe6fffffffff20f8ffffffff57ffff53f8bfffffffffffff6bffcfffffffffffd6560fc8ffffff53ffefaa7fff6bf4cf23f8ffffffff57fffffff8bffffcffffffdf67fffffffffffe14ffffffc8fffffffffcefaa7fdf656fcf23f8fffff4fffe0ffffff8bffffc3ffe6fff694ffffffffffe1fceffffc8fffffffffc6daa6fdf6954ff2bfffffe1fcefe0ffffff8bffffcfffe7fdf6964cffffffffe1fff2bffc8fffffffffcefa67fdd6964cf2bfffffffffffe0ffffff6dcfffffffffffffffffffff2dffdefd9ffffd853ffdcfffffffe7fffffffff2fffdfffffd957ffd853f6fffffc3ffe48ffffffff2fffdffdefd9fcdfd8ffffffffffffa2783ffd4ffffff2dffdefd92bffd8fffffffffcffae78fffd5fcf2fffdffdefd9ffffd8ffffff510ffffffffffffffffcffdffdefff55173fffffff510fffafffffffffcfffffdffdefd6fd1fffffffffffffeeae5ffffff43fffffdffff75654dfff53ffffffffefa3ffff6fffcfffffdfffffd6ffffc8ffffff53ffefae7fff63f44f2fffdfffffff57fffffffffffffc7fae5ffffd4ffffcffdfffffff4bfffffd0ffffffcffa7f8bf6ffffffff2dffff77fffffc8fd0ffffd0cffae78fffd6fcf2fffdffdefff4bfffffffffffffc2eae58ff6d54bffcffdffff77ffffffffffffffffcefa678bf6d643ffffffffff77f2bffc8fffffffffcefae78ff65648f2fffdfffffffffffffffffff53fcfffff8ffffffff2ffffffd7fff551fd8fff6ffffffeffff81ffffffffff2fffd76bfffffd853fffffffceffe78dffff47f2fffffffffff57ffd8fff6fffffcacfe6ffffffffffcf2ffffffffffffd8fd0fccfffcbffe6fffffffff2cffffffffff4bffd8fffffffffcffabf87fffffcffff2ffffffd9fd1fd8fd0ffffffcffae78fffd7fcf2fffffffffd94bffd8ffffffffffecfe687ffff43ffff2fffff699fcdfd8ffffccfffcaefe68dffff4bf2cfffffff6bfffffd8ffffc9ffffefaa785ffd744fffffffffffd92bffd8fffffffffcefae78defd748f2fffffffffd9ffffd8ffffff53fc6effffdf6ffffffcfffffd74ffffffffffffff53fcefaff8df63ffcffffffffff4d6fffffffffffffffc2dfff8bf6ffffffff2fffd7fd6fcdfc853ffff53fc6efe68dffff4ff2cffffffffff57fffffffffffffcefabf81f6bffcfffffffffffd6ffffc8fffffffffcacabffdf6d7ffffffffffff4ceffffc8fffffffd0caeae6fdf617fff2fffffffffce4bfffffffffffffcefabf85f67ffcffff2fffff4ffffffc8fffffffffcefae78de657fcf2ffffffffffffd1ffffffffffffcada258bf6d74ffffffffffffce2bffc8fffffffffcaeae48de6974ff2ffffffffffffcdffffffffffffcefa6785e6974cfffffffffffff2bffc8fff >>> (168*i)) &&& 0xffffffffffffffffffffffffffffffffffffffffff

-- For a left row and residual mask, the six-bit entry names a positive witness.
-- A sentinel of 63 contributes an empty board. Board bits index right rows.
private def flag (i w : Nat) := ((packed (i)) >>> (6*w)) &&& 63
private def contribution (i w : Nat) : Nat :=
  let k := flag i w
  if k < 52 ∧ omittedFlags.testBit k = false ∧
     (positiveWords (k)) &&& ((negativeWords (i)) ||| (mins (w))) = (positiveWords (k))
  then (boards (w)) else 0

private def union (i : Nat) (ws : List Nat) : Nat :=
  ws.foldr (fun w b => contribution i w ||| b) 0

private theorem member {i j : Nat} (ws : List Nat) (yes : (union i ws).testBit j = true) :
    ∃ w ∈ ws, (contribution i w).testBit j = true := by
  induction ws with
  | nil => simp [union] at yes
  | cons w ws ih =>
    change (contribution i w ||| union i ws).testBit j = true at yes
    rw [Nat.testBit_or,Bool.or_eq_true] at yes
    rcases yes with head | tail
    · exact ⟨w,by simp,head⟩
    · obtain ⟨v,hv,on⟩ := ih tail
      exact ⟨v,List.mem_cons_of_mem _ hv,on⟩

set_option maxRecDepth 12000 in
private theorem bits0 : ∀ j : Fin 257, (boards (0)).testBit j.val = true → (mins (0)) &&& (negativeWords (j.val)) = (mins (0)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits1 : ∀ j : Fin 257, (boards (1)).testBit j.val = true → (mins (1)) &&& (negativeWords (j.val)) = (mins (1)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits2 : ∀ j : Fin 257, (boards (2)).testBit j.val = true → (mins (2)) &&& (negativeWords (j.val)) = (mins (2)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits3 : ∀ j : Fin 257, (boards (3)).testBit j.val = true → (mins (3)) &&& (negativeWords (j.val)) = (mins (3)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits4 : ∀ j : Fin 257, (boards (4)).testBit j.val = true → (mins (4)) &&& (negativeWords (j.val)) = (mins (4)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits5 : ∀ j : Fin 257, (boards (5)).testBit j.val = true → (mins (5)) &&& (negativeWords (j.val)) = (mins (5)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits6 : ∀ j : Fin 257, (boards (6)).testBit j.val = true → (mins (6)) &&& (negativeWords (j.val)) = (mins (6)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits7 : ∀ j : Fin 257, (boards (7)).testBit j.val = true → (mins (7)) &&& (negativeWords (j.val)) = (mins (7)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits8 : ∀ j : Fin 257, (boards (8)).testBit j.val = true → (mins (8)) &&& (negativeWords (j.val)) = (mins (8)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits9 : ∀ j : Fin 257, (boards (9)).testBit j.val = true → (mins (9)) &&& (negativeWords (j.val)) = (mins (9)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits10 : ∀ j : Fin 257, (boards (10)).testBit j.val = true → (mins (10)) &&& (negativeWords (j.val)) = (mins (10)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits11 : ∀ j : Fin 257, (boards (11)).testBit j.val = true → (mins (11)) &&& (negativeWords (j.val)) = (mins (11)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits12 : ∀ j : Fin 257, (boards (12)).testBit j.val = true → (mins (12)) &&& (negativeWords (j.val)) = (mins (12)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits13 : ∀ j : Fin 257, (boards (13)).testBit j.val = true → (mins (13)) &&& (negativeWords (j.val)) = (mins (13)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits14 : ∀ j : Fin 257, (boards (14)).testBit j.val = true → (mins (14)) &&& (negativeWords (j.val)) = (mins (14)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits15 : ∀ j : Fin 257, (boards (15)).testBit j.val = true → (mins (15)) &&& (negativeWords (j.val)) = (mins (15)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits16 : ∀ j : Fin 257, (boards (16)).testBit j.val = true → (mins (16)) &&& (negativeWords (j.val)) = (mins (16)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits17 : ∀ j : Fin 257, (boards (17)).testBit j.val = true → (mins (17)) &&& (negativeWords (j.val)) = (mins (17)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits18 : ∀ j : Fin 257, (boards (18)).testBit j.val = true → (mins (18)) &&& (negativeWords (j.val)) = (mins (18)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits19 : ∀ j : Fin 257, (boards (19)).testBit j.val = true → (mins (19)) &&& (negativeWords (j.val)) = (mins (19)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits20 : ∀ j : Fin 257, (boards (20)).testBit j.val = true → (mins (20)) &&& (negativeWords (j.val)) = (mins (20)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits21 : ∀ j : Fin 257, (boards (21)).testBit j.val = true → (mins (21)) &&& (negativeWords (j.val)) = (mins (21)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits22 : ∀ j : Fin 257, (boards (22)).testBit j.val = true → (mins (22)) &&& (negativeWords (j.val)) = (mins (22)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits23 : ∀ j : Fin 257, (boards (23)).testBit j.val = true → (mins (23)) &&& (negativeWords (j.val)) = (mins (23)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits24 : ∀ j : Fin 257, (boards (24)).testBit j.val = true → (mins (24)) &&& (negativeWords (j.val)) = (mins (24)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits25 : ∀ j : Fin 257, (boards (25)).testBit j.val = true → (mins (25)) &&& (negativeWords (j.val)) = (mins (25)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits26 : ∀ j : Fin 257, (boards (26)).testBit j.val = true → (mins (26)) &&& (negativeWords (j.val)) = (mins (26)) := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits27 : ∀ j : Fin 257, (boards (27)).testBit j.val = true → (mins (27)) &&& (negativeWords (j.val)) = (mins (27)) := by decide +kernel
private theorem boardOK (w : Fin 28) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
  match w with
  | ⟨0,_⟩ => exact bits0 j
  | ⟨1,_⟩ => exact bits1 j
  | ⟨2,_⟩ => exact bits2 j
  | ⟨3,_⟩ => exact bits3 j
  | ⟨4,_⟩ => exact bits4 j
  | ⟨5,_⟩ => exact bits5 j
  | ⟨6,_⟩ => exact bits6 j
  | ⟨7,_⟩ => exact bits7 j
  | ⟨8,_⟩ => exact bits8 j
  | ⟨9,_⟩ => exact bits9 j
  | ⟨10,_⟩ => exact bits10 j
  | ⟨11,_⟩ => exact bits11 j
  | ⟨12,_⟩ => exact bits12 j
  | ⟨13,_⟩ => exact bits13 j
  | ⟨14,_⟩ => exact bits14 j
  | ⟨15,_⟩ => exact bits15 j
  | ⟨16,_⟩ => exact bits16 j
  | ⟨17,_⟩ => exact bits17 j
  | ⟨18,_⟩ => exact bits18 j
  | ⟨19,_⟩ => exact bits19 j
  | ⟨20,_⟩ => exact bits20 j
  | ⟨21,_⟩ => exact bits21 j
  | ⟨22,_⟩ => exact bits22 j
  | ⟨23,_⟩ => exact bits23 j
  | ⟨24,_⟩ => exact bits24 j
  | ⟨25,_⟩ => exact bits25 j
  | ⟨26,_⟩ => exact bits26 j
  | ⟨27,_⟩ => exact bits27 j
  | ⟨a+28,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 28) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 28) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 28) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 28) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 28) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 28) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 28) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 28) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 28) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 28) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 28) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 28) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 28) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 28) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 28) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 28) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 28) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 28) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 28) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 28) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 28) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 28) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 28) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 28) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 28) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 28) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 28) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 28) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 28) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 28) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 28) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 28) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 28) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 28) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 28) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
    match q with
    | ⟨0,_⟩ => exact block0 ⟨r,hr⟩
    | ⟨1,_⟩ => exact block1 ⟨r,hr⟩
    | ⟨2,_⟩ => exact block2 ⟨r,hr⟩
    | ⟨3,_⟩ => exact block3 ⟨r,hr⟩
    | ⟨4,_⟩ => exact block4 ⟨r,hr⟩
    | ⟨5,_⟩ => exact block5 ⟨r,hr⟩
    | ⟨6,_⟩ => exact block6 ⟨r,hr⟩
    | ⟨7,_⟩ => exact block7 ⟨r,hr⟩
    | ⟨8,_⟩ => exact block8 ⟨r,hr⟩
    | ⟨9,_⟩ => exact block9 ⟨r,hr⟩
    | ⟨10,_⟩ => exact block10 ⟨r,hr⟩
    | ⟨11,_⟩ => exact block11 ⟨r,hr⟩
    | ⟨12,_⟩ => exact block12 ⟨r,hr⟩
    | ⟨13,_⟩ => exact block13 ⟨r,hr⟩
    | ⟨14,_⟩ => exact block14 ⟨r,hr⟩
    | ⟨15,_⟩ => exact block15 ⟨r,hr⟩
    | ⟨16,_⟩ => exact block16 ⟨r,hr⟩
    | ⟨17,_⟩ => exact block17 ⟨r,hr⟩
    | ⟨18,_⟩ => exact block18 ⟨r,hr⟩
    | ⟨19,_⟩ => exact block19 ⟨r,hr⟩
    | ⟨20,_⟩ => exact block20 ⟨r,hr⟩
    | ⟨21,_⟩ => exact block21 ⟨r,hr⟩
    | ⟨22,_⟩ => exact block22 ⟨r,hr⟩
    | ⟨23,_⟩ => exact block23 ⟨r,hr⟩
    | ⟨24,_⟩ => exact block24 ⟨r,hr⟩
    | ⟨25,_⟩ => exact block25 ⟨r,hr⟩
    | ⟨26,_⟩ => exact block26 ⟨r,hr⟩
    | ⟨27,_⟩ => exact block27 ⟨r,hr⟩
    | ⟨28,_⟩ => exact block28 ⟨r,hr⟩
    | ⟨29,_⟩ => exact block29 ⟨r,hr⟩
    | ⟨30,_⟩ => exact block30 ⟨r,hr⟩
    | ⟨31,_⟩ => exact block31 ⟨r,hr⟩
    | ⟨32,_⟩ => exact block32 ⟨r,by change r + 256 < 257 at hs; omega⟩
    | ⟨a+33,ha⟩ => omega
  have eq : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [eq] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega)

private theorem positiveRows : ∀ p : Fin 52, (positiveWords (p.val)) = pos p.val := by decide +kernel
private abbrev rowMatches (v : Nat) := (indices (v)) < 468 ∧ (negativeWords (v)) = neg (indices (v))
private theorem negBlock0 : ∀ r : Fin 8, rowMatches (r.val+0) := by decide +kernel
private theorem negBlock1 : ∀ r : Fin 8, rowMatches (r.val+8) := by decide +kernel
private theorem negBlock2 : ∀ r : Fin 8, rowMatches (r.val+16) := by decide +kernel
private theorem negBlock3 : ∀ r : Fin 8, rowMatches (r.val+24) := by decide +kernel
private theorem negBlock4 : ∀ r : Fin 8, rowMatches (r.val+32) := by decide +kernel
private theorem negBlock5 : ∀ r : Fin 8, rowMatches (r.val+40) := by decide +kernel
private theorem negBlock6 : ∀ r : Fin 8, rowMatches (r.val+48) := by decide +kernel
private theorem negBlock7 : ∀ r : Fin 8, rowMatches (r.val+56) := by decide +kernel
private theorem negBlock8 : ∀ r : Fin 8, rowMatches (r.val+64) := by decide +kernel
private theorem negBlock9 : ∀ r : Fin 8, rowMatches (r.val+72) := by decide +kernel
private theorem negBlock10 : ∀ r : Fin 8, rowMatches (r.val+80) := by decide +kernel
private theorem negBlock11 : ∀ r : Fin 8, rowMatches (r.val+88) := by decide +kernel
private theorem negBlock12 : ∀ r : Fin 8, rowMatches (r.val+96) := by decide +kernel
private theorem negBlock13 : ∀ r : Fin 8, rowMatches (r.val+104) := by decide +kernel
private theorem negBlock14 : ∀ r : Fin 8, rowMatches (r.val+112) := by decide +kernel
private theorem negBlock15 : ∀ r : Fin 8, rowMatches (r.val+120) := by decide +kernel
private theorem negBlock16 : ∀ r : Fin 8, rowMatches (r.val+128) := by decide +kernel
private theorem negBlock17 : ∀ r : Fin 8, rowMatches (r.val+136) := by decide +kernel
private theorem negBlock18 : ∀ r : Fin 8, rowMatches (r.val+144) := by decide +kernel
private theorem negBlock19 : ∀ r : Fin 8, rowMatches (r.val+152) := by decide +kernel
private theorem negBlock20 : ∀ r : Fin 8, rowMatches (r.val+160) := by decide +kernel
private theorem negBlock21 : ∀ r : Fin 8, rowMatches (r.val+168) := by decide +kernel
private theorem negBlock22 : ∀ r : Fin 8, rowMatches (r.val+176) := by decide +kernel
private theorem negBlock23 : ∀ r : Fin 8, rowMatches (r.val+184) := by decide +kernel
private theorem negBlock24 : ∀ r : Fin 8, rowMatches (r.val+192) := by decide +kernel
private theorem negBlock25 : ∀ r : Fin 8, rowMatches (r.val+200) := by decide +kernel
private theorem negBlock26 : ∀ r : Fin 8, rowMatches (r.val+208) := by decide +kernel
private theorem negBlock27 : ∀ r : Fin 8, rowMatches (r.val+216) := by decide +kernel
private theorem negBlock28 : ∀ r : Fin 8, rowMatches (r.val+224) := by decide +kernel
private theorem negBlock29 : ∀ r : Fin 8, rowMatches (r.val+232) := by decide +kernel
private theorem negBlock30 : ∀ r : Fin 8, rowMatches (r.val+240) := by decide +kernel
private theorem negBlock31 : ∀ r : Fin 8, rowMatches (r.val+248) := by decide +kernel
private theorem negBlock32 : ∀ r : Fin 1, rowMatches (r.val+256) := by decide +kernel
private theorem negativeRows (i : Fin 257) : rowMatches i.val := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : rowMatches (r+8*q.val) := by
    match q with
    | ⟨0,_⟩ => exact negBlock0 ⟨r,hr⟩
    | ⟨1,_⟩ => exact negBlock1 ⟨r,hr⟩
    | ⟨2,_⟩ => exact negBlock2 ⟨r,hr⟩
    | ⟨3,_⟩ => exact negBlock3 ⟨r,hr⟩
    | ⟨4,_⟩ => exact negBlock4 ⟨r,hr⟩
    | ⟨5,_⟩ => exact negBlock5 ⟨r,hr⟩
    | ⟨6,_⟩ => exact negBlock6 ⟨r,hr⟩
    | ⟨7,_⟩ => exact negBlock7 ⟨r,hr⟩
    | ⟨8,_⟩ => exact negBlock8 ⟨r,hr⟩
    | ⟨9,_⟩ => exact negBlock9 ⟨r,hr⟩
    | ⟨10,_⟩ => exact negBlock10 ⟨r,hr⟩
    | ⟨11,_⟩ => exact negBlock11 ⟨r,hr⟩
    | ⟨12,_⟩ => exact negBlock12 ⟨r,hr⟩
    | ⟨13,_⟩ => exact negBlock13 ⟨r,hr⟩
    | ⟨14,_⟩ => exact negBlock14 ⟨r,hr⟩
    | ⟨15,_⟩ => exact negBlock15 ⟨r,hr⟩
    | ⟨16,_⟩ => exact negBlock16 ⟨r,hr⟩
    | ⟨17,_⟩ => exact negBlock17 ⟨r,hr⟩
    | ⟨18,_⟩ => exact negBlock18 ⟨r,hr⟩
    | ⟨19,_⟩ => exact negBlock19 ⟨r,hr⟩
    | ⟨20,_⟩ => exact negBlock20 ⟨r,hr⟩
    | ⟨21,_⟩ => exact negBlock21 ⟨r,hr⟩
    | ⟨22,_⟩ => exact negBlock22 ⟨r,hr⟩
    | ⟨23,_⟩ => exact negBlock23 ⟨r,hr⟩
    | ⟨24,_⟩ => exact negBlock24 ⟨r,hr⟩
    | ⟨25,_⟩ => exact negBlock25 ⟨r,hr⟩
    | ⟨26,_⟩ => exact negBlock26 ⟨r,hr⟩
    | ⟨27,_⟩ => exact negBlock27 ⟨r,hr⟩
    | ⟨28,_⟩ => exact negBlock28 ⟨r,hr⟩
    | ⟨29,_⟩ => exact negBlock29 ⟨r,hr⟩
    | ⟨30,_⟩ => exact negBlock30 ⟨r,hr⟩
    | ⟨31,_⟩ => exact negBlock31 ⟨r,hr⟩
    | ⟨32,_⟩ => exact negBlock32 ⟨r,by change r + 256 < 257 at hs; omega⟩
    | ⟨a+33,ha⟩ => omega
  have eq : i.val%8+8*(i.val/8) = i.val := by omega
  simpa only [eq] using h ⟨i.val/8,by omega⟩ (i.val%8) (by omega) (by dsimp; omega)

private def idx (i : Fin 257) : Fin 468 := ⟨(indices (i.val)), (negativeRows i).1⟩

private theorem bitLift (p a m b : Bool) (c : (p && (a || m)) = p) (d : (m && b) = m) : (p && (a || b)) = p := by
  cases p <;> cases a <;> cases m <;> cases b <;> simp_all

private theorem retained (i j : Fin 257) (lt : i.val < j.val) :
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
      pos p.val &&& (neg (idx i).val ||| neg (idx j).val) = pos p.val := by
  have full := congrArg (fun x : Nat => x.testBit j.val) (checked i)
  have one : (1 <<< i.val : Nat).testBit j.val = false := by
    rw [Nat.one_shiftLeft,Nat.testBit_two_pow]
    simp [show i.val ≠ j.val by omega]
  have bit : ((2:Nat)^257-1).testBit j.val = true := by
    rw [Nat.testBit_two_pow_sub_one]
    simp [j.isLt]
  simp only [Nat.testBit_or,one,Bool.or_false,bit] at full
  obtain ⟨w,hw,on⟩ := member (List.range 28) full
  let k := flag i.val w
  by_cases ok : k < 52 ∧ omittedFlags.testBit k = false ∧ (positiveWords (k)) &&& ((negativeWords (i.val)) ||| (mins (w))) = (positiveWords (k))
  · simp only [contribution,← show k = flag i.val w from rfl,ite_eq_left ok] at on
    obtain ⟨bound,off,cov⟩ := ok
    let p : Fin 52 := ⟨k,bound⟩
    have sub := boardOK ⟨w,List.mem_range.mp hw⟩ j on
    refine ⟨p,off,?_⟩
    change pos p.val &&& (neg (indices (i.val)) ||| neg (indices (j.val))) = pos p.val
    rw [← positiveRows p,← (negativeRows i).2,← (negativeRows j).2]
    apply Nat.eq_of_testBit_eq
    intro b
    have c := congrArg (fun t : Nat => t.testBit b) cov
    have d := congrArg (fun t : Nat => t.testBit b) sub
    simp only [Nat.testBit_and,Nat.testBit_or] at c d ⊢
    change ((positiveWords (k)).testBit b && ((negativeWords (i.val)).testBit b || (negativeWords (j.val)).testBit b)) = (positiveWords (k)).testBit b
    exact bitLift _ _ _ _ c d
  · simp only [contribution,← show k = flag i.val w from rfl,ite_eq_right ok,Nat.zero_testBit] at on
    contradiction

def ix (i : Fin 257) := indices i.val
theorem neg_match (i : Fin 257) : ix i < 468 := (negativeRows i).1
private theorem beyond : ∀ p : Fin 52, omittedFlags.testBit p.val = false → 8 ≤ p.val := by decide +kernel
/-- The selected negative rows share a positive witness outside lines 0 and 1 for every pair. -/
theorem pairCertificate (i j : Fin 257) (lt : i < j) :
    ∃ p : Fin 52, 8 ≤ p.val ∧ pos p.val &&& (neg (ix i) ||| neg (ix j)) = pos p.val := by
  obtain ⟨p,off,h⟩ := retained i j lt
  exact ⟨p,beyond p off,h⟩

def initial : List Column := List.ofFn (fun k : Fin 28 => input k.val)

theorem initial_good (p : Fin 52) (a b : Fin 468)
    (h : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ initial, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hw
  have e := congrArg (fun x : Nat => x.testBit k.val) h
  simp only [Nat.testBit_and,Nat.testBit_or] at e
  intro hp
  have yes : (pos p.val).testBit k.val = true := by simpa [input,p.isLt] using hp
  rw [yes,Bool.true_and,Bool.or_eq_true] at e
  simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using e
end PEqualNP.Research.PlaneCase35Independent.Certificate



namespace PEqualNP.Research.PlaneCase35Independent.Transport
open PEqualNP.Research.PlaneCase35Independent.Data PEqualNP.Research.PlaneCase35Independent.Certificate
-- Each triple selects part of a word and shifts it to its new coordinates.
private def permute : List (Nat × Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (mask,l,r)::tail, x => (((x &&& mask) <<< l) >>> r) ||| permute tail x
private def segments : Array (List (Nat × Nat × Nat)) := #[[(0x1ffefff,1,0), (0x2001000,0,12)], [(0x2001,0,0), (0x4002,2,0), (0x8004,4,0), (0x10008,6,0), (0x20010,8,0), (0x40020,0,3), (0x80040,0,1), (0x100080,1,0), (0x200100,3,0), (0x400200,0,8), (0x800400,0,6), (0x1000800,0,4), (0x2001000,0,2)], [(0x68220b,0,0), (0x8024,5,0), (0x10,7,0), (0x140140,0,4), (0x10080,0,1), (0x800400,2,0), (0x800,0,3), (0x1000,0,7), (0x4000,10,0), (0x20000,6,0), (0x1000000,0,6), (0x2000000,0,8)]]
private def act (g : Fin 3) (x : Nat) := extend (permute segments[g.val]! x)
private theorem permJoin (s : List (Nat × Nat × Nat)) (x y : Nat) :
    permute s (x ||| y) = permute s x ||| permute s y := by
  induction s with
  | nil => simp [permute]
  | cons h t ih =>
    rcases h with ⟨m,l,r⟩
    simp only [permute,Nat.and_or_distrib_right,Nat.shiftLeft_or_distrib,Nat.shiftRight_or_distrib,ih]
    ac_rfl
private def Hom (f : Nat → Nat) := ∀ x y, f (x ||| y) = f x ||| f y
private theorem glue {f g : Nat → Nat} (hf : Hom f) (hg : Hom g) : Hom (fun v => f v ||| g v) := by
  intro x y
  change f _ ||| g _ = (f x ||| g x) ||| (f y ||| g y)
  rw [hf,hg]
  ac_rfl
private theorem pushed {f : Nat → Nat} (h : Hom f) (k : Nat) : Hom (fun v => f v <<< k) := by
  intro x y
  exact (congrArg (fun z => z <<< k) (h x y)).trans Nat.shiftLeft_or_distrib
private theorem bitHom (k : Nat) : Hom (fun x => (x >>> k) &&& 1) := by
  intro x y
  simp only [Nat.shiftRight_or_distrib,Nat.and_or_distrib_right]
private theorem extendJoin : Hom extend :=
  glue (glue (fun _ _ => rfl) (pushed (glue (bitHom 0) (bitHom 1)) 26))
    (pushed (glue (bitHom 3) (bitHom 9)) 27)
private theorem join (g : Fin 3) (x y : Nat) : act g (x ||| y) = act g x ||| act g y := by
  exact (congrArg extend (permJoin _ x y)).trans (extendJoin _ _)

private def pm : Array Nat := #[0x3081c33cb1beeb6ca2baa99e69648e28607de75c6da6585d65544134913ce34c2ca2481c6144, 0xaaba687dd79c4d14901c6105b6cbaf8238625175562ca209cb1cf09a49e56986d934f38c043080, 0x4914d0557594cb3c709279668628233cd38c6d961a1851c4a6aae82882c979f71dbeeb6c0c2040]
private def nm : Array Nat := #[0xe5f1f89bcdce6f2b91c7e370d84c1602fd75b9dc6db6bb2d8ec15aac55ead52a752e87409c4c25b2a93c7a39198842e13067fbf1f2f579badcce471379aed4693419cca61afd7abb5bad158aa54a9d4c9348231007d3e1e8f075399c8e06f34990c4572a1449c4d259249046229087a3b1c0c45a2b1409848210f87436190b85428130903c160903818080300803a7d2e8f439fcee6f3395c9e471b8bc3e170781bfdf6f777badc6df6db5da6cf65b1d86bf5dadd66af55a9d469f4da5d268f45a1d067f3d9dce66b3398cbe5b2993c96431d8cc5e2b1388c3e170781bfdf6f97bbd5e6f177bb5d2e570b7dbad96ab4da2cf66b258ac35faf576b95bacd56a953a8d429f4da652a9348a3d1a8b44a15067f3e9ecf2773a9ccde6d359a4ce653197cba592b94ca24d259248e45219047e3b1b8d4622f168ac52271288c3e1d0d8642a110782c12070280c01fcfd7dbe9f0f77b3d1e4f1783bddced763a9d2e873b95c6e17037dbadc6db69b2d86b355a6d167b3598cb64b218ec662b1184c1602f978ba5cae16cb559ac962b057ab95aab5429548a351285409f4f275389b4d26530974b255289248a3d1c8d45a29128843a190a8441a09027f3f1ecf2773b1d0e26e369b0d66a3419ccc6531984c05f2f174b85b2d164b0562a94ca4502793094472210c82401f8f8783a1c8dc6c351a0cc6430178b8582a1489c4a23110803c1c0d0602c11080381a0c050200a02, 0x703318ec863543a74fa7535c2df6f37596ca64eb59ec4d7ebb58ce66b1587465d2c582afa4d4e8f456cbc5b8d55cb0966b0773a5d0c0597429944a0b6362db6934571a95aab952a8d368d7abc562ad4dd1aa523a5cfaad4aa34ba550e85407935dadb8d9ecb60f077b69a8d3686a96eb6db6a1d6ea5a6d74fa476b9dc8e35faf95aa7dbed357a576399cae25daa8722fbd0b4586a529a4d03a1c0def62ecedf2f2914823c602b9444f911588998d864318d08636190a6f175ba1007a3c150a27f2993c9a2f3a8c45b93398971f8d389bc5220a33699548a2371acce62220cd309449a4884411a8c739764b2347d9ecde6aff7ebeddee6974aa39183f1dbf77d317d5a44e1003017275c441e8f21b0d00e43cd9ec7a3bc282c137f007e3ef7b3097bfdfcf93095cad892e93499a2c66213c5c25dcad56813094241107d7eba200e8701004cc64adf6eaf2250e7c3d9e03e1e0c81f993c91c6a5cf87a6ea692b8641dec525017c9e9b2411f4182c0a64b0450702b2d66b0a2d027e11030ee7238808018fc756ab35642a08ea743785c2c1300cfa4b208ff3b97ca9dc92451c8dc67830f81c078bc09b4ca1d02de6ee6b2d9643613087bbcf89c3dccce550b85419ea602a944a0a14f978a853276870f84c1a75345b2c9288d9fc5e2b0d85c0270b449b3d8ec424118341399cae52e370b2d92c08a401fcfa2105e47215baba190676380602997c6db6d96bac210e615, 0xb55cad3c2b4185b3212b9587505090444e2612ae872106652572381bc101fa2cc64f3b92c66279b88b7d7ef95eb75eb7d5cbdefebb79debc54b3d4f225d2913e1ed10ee43cc4f479a9ba1208f984bcf0dc2e971c0d53513498693447a3a4b1007c3cb36451d6500040c1fefe03b04361a613003a1c0cac68caf17bf40c05168b1f40363ac18d45173f1f60415be73396db6572966b3d96c9c5b8dc35361d574751c1b1d8b816050a81e53e4fa0528803fa2d3136451faa8eb754e92692991f4ab202a14cbe6092979b05227b5dac512847c9c0e1b032060d8c0d6040b21888890f1208c84418708570b51a02864cb5badaa0ca64d21691719c04131618e8371a1cfedf3d97c7e3b6bb4ce647219bcd63717b2c3e1b0bb3e762b63ccc16076184c1f2f9580bfdb6d9a6bc56ab3a7d7696b777ac6bfa5abbf5f789c3b5f4347c8badd37556d6e93a7ace7f26edbcddd5f8fc6b9ee5e09d52271373c4cbbd469a9fa8a76854325d08773a9d1cee6729d91c739a209db557625a6a834acce5c7238cacdee471d4aa2e29ca365b2c384e26e8c9516cdd242d37da8d3254a4cf1c8d925b66c91961c2da36964d72269344cc4823ca0c8638d115bcdd681948d279318a32408605c2d0d0c0fe170a0aaba88ac55be00515153d802ada7b168742553de28f5a62f5783d1e41c26cf5faf99ccda5d29763e84c20283b832a551415344c52f40044450c453d3a9ac3a0449e710]
private def lm : Array Nat := #[0xcba987654321, 0xa741b852c9630, 0x45c98361a27b0]
private def imageP (g : Fin 3) (p : Fin 52) : Fin 52 :=
  Fin.ofNat 52 (((pm[g.val]! >>> (6*p.val)) &&& 63))
private def imageN (g : Fin 3) (n : Fin 468) : Fin 468 :=
  Fin.ofNat 468 (((nm[g.val]! >>> (9*n.val)) &&& 511))
private def line (g : Fin 3) (a : Nat) := (lm[g.val]! >>> (4*a)) &&& 15
set_option maxRecDepth 16000 in
private theorem posOK : ∀ (g : Fin 3) (p : Fin 52), pos (imageP g p).val = act g (pos p.val) ∧
    (imageP g p).val / 4 = line g (p.val/4) := by decide +kernel
private def nw (i : Fin 468) := (0xb900230b880038b840218b804228b800238b280428b220448b2040683202460b200468b108250b1042603102070b100270b0c04183082430b080438b060608b048610b040618b028640b024248b020648300a450b008650b0042683002470ee0008aec8001aac400986c08092ec0009aea8002a6a100a2aa040a8ea000aa6980032e910222e908212e900232e88003aa848290a844288a840298e818282a8142a0e8102a2e808292a8042a8e62004a66080c2a6040c8e6000ca65808126520842650805225028506500852a4c0818e4a080ae48081aa4448882442890a440898a424848e42084a240a0d064080d224068c0a4048c824028d0e2a040a6290422e28042a6228442e22044a621848222124a062104a2220a4c062084c222060e0a2040e822024e0619082221828306180832e130a02e128242a124a40e120a42a114a20e110a22e1082522106860a104a602102870a0e0c0820c2c10a0c0c1860b0c02e0a0c0a2092c206090c222082c30a070e00a064a08a060e08a058680a054a802052c80a050e80204a490a048690a044a882042c90e038602e030e02e028642a024a48e01868220168a0a014aa02012ca0200a4d020068e09c801189c4001c9c2010c1c021149c0011c9940214991022419020349900234988412818821309880138986020c984021c98303049824308982030c981432018121249810324980432818021345700045d64000d962004cd604049d60004d5540015550805115020545500055d4c00195488111d484109d480119d44001d94241481422144942014c540c141140a1505408151d40414914021545310025530406113020645300065d2c04095290421d284029d280429926040c5250405d24040d1222444922044c12124245210425d2040691202464d150205d148211d140215d114221d110225d10c241d108251d104261110207450c8411d0c04195098501509412110925205090521108a5105088511d08412910825309070604906060cd058601d050605d048611903870010325049030704902c340102a540902874090243481022544d01c301d018701d0143211012524d00c341100a5508e4008cce2000e4e10086ce0008ecca010a4c88112cc8011a0c420948c4009c4c30106cc2010e4c181820c121844c101860c0a1904c081920c021944b810224b210064b100260b030244b01026caa100a8a85028ca8102a8a6100c8a450880a430848a4108cca2100e0a120a44a100a60a070a08a050a80a030a44989012098303049810328961204894921009430148941214c930206c929202c921206c910226c909212090303448a910288a5108c8a110a088b11048891120887120888512808831308865208886120c884d280084b090884929088452880843094c838302c830306882d300c8293028825308881c380c81838208161a088143a008121a4080f180880d380080b19008071a047200464710007470804347000474650085c644089c64008dc62004e46180834610087460c0c146080c3c6040c945c0811459080345880134580813455080505428144540815453080605228444520846451080745080530502854c4c4809c4c081944b090284a4908c4a090a4498103449490144909034488113c484909445488104528844450885c444889044289404329044430906042694084249480422944441c1814418183041698044149810412984040e1c0440c1c1040a1d004069c043900234389003438502143810234329042032304443210464310027430d041430904303070604305061030306482e140842c9401c2c5009c2c140942a9402c2a140a429840342904234289403c2850290263404826140c425848102524844250485424d081024b4804249481c2450890243484022b44042294420223444421848302124a4020f0c0420d0c1020b4c002070e041c901141c580101c381041c18114194821419082341890130187820418582101838308170a048165a0001638048161a04c154a01c150a05c14d201c149211c145a010143814c130a06812d240c12924201278408125a400123844c114a21c10d241010786080e580800e3c0080e1c0800cb41040c9411c0c580900c3c1040b850200b2d0040b0d0200ab50040a950200a790080a590800a3d004098503009692040949210092d20008b51000879200072c048070e048065a080063c04c05c281c058681c054a810052c84c04d281004b490c0387020032d04002f140802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i.val)) &&& 0xfffffff
set_option maxRecDepth 8192 in
private theorem original : ∀ i : Fin 468, nw i = neg i.val := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
private theorem n0 (n : Fin 468) : nw (imageN 0 n) = act 0 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n1b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
private theorem n1 (n : Fin 468) : nw (imageN 1 n) = act 1 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n2b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
private theorem n2 (n : Fin 468) : nw (imageN 2 n) = act 2 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b442 j
  omega
private theorem negOK (g : Fin 3) (n : Fin 468) : neg (imageN g n).val = act g (neg n.val) := by
  rw [←original,←original n]
  match g with
  | ⟨0,_⟩ => exact n0 n
  | ⟨1,_⟩ => exact n1 n
  | ⟨2,_⟩ => exact n2 n
  | ⟨m+3,hm⟩ => omega
private theorem inj : ∀ (g : Fin 3) (a b : Fin 13), line g a.val = line g b.val → a=b := by decide +kernel
theorem cover (x y : Nat) : x &&& y = x ↔ x ||| y = y := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
    have e := congrArg (fun v : Nat => v.testBit k) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and] at e ⊢ <;>
    cases ex : x.testBit k <;> cases ey : y.testBit k <;> simp_all

private def W (a b : Nat) := ∃ f : Fin 257 → Fin 468, ∀ i j, i < j →
    ∃ p : Fin 52, p.val/4 ≠ a ∧ p.val/4 ≠ b ∧
      pos p.val ||| (neg (f i).val ||| neg (f j).val) = neg (f i).val ||| neg (f j).val
private theorem start : W 0 1 := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j h
  obtain ⟨p,lo,ok⟩ := pairCertificate i j h
  exact ⟨p,by omega,by omega,(cover _ _).mp ok⟩
private theorem hop {a b : Fin 13} (g : Fin 3) (old : W a.val b.val) : W (line g a.val) (line g b.val) := by
  obtain ⟨f,h⟩ := old
  refine ⟨fun i => imageN g (f i),?_⟩
  intro i j lt
  obtain ⟨p,ha,hb,ok⟩ := h i j lt
  let t : Fin 13 := ⟨p.val/4,by omega⟩
  have distinct (k : Fin 13) (off : p.val / 4 ≠ k.val) : (imageP g p).val / 4 ≠ line g k.val := by
    rw [(posOK g p).2]
    exact fun eq => off (congrArg Fin.val (inj g t k eq))
  refine ⟨imageP g p,distinct a ha,distinct b hb,?_⟩
  simpa only [(posOK g p).1,negOK,join] using congrArg (act g) ok

private theorem within : ∀ (g : Fin 3) (a : Fin 13), line g a.val < 13 := by decide +kernel
private def shift (g : Fin 3) (a : Fin 13) : Fin 13 := ⟨_,within g a⟩
private def walk : Nat → Nat → Fin 13 × Fin 13 → Fin 13 × Fin 13
  | 0,_,x => x
  | k+1,z,(a,b) => if z%4 = 0 then (a,b) else
    let g := Fin.ofNat 3 (z%4-1)
    walk k (z/4) (shift g a,shift g b)
private theorem follow (k z : Nat) (x : Fin 13 × Fin 13) (h : W x.1.val x.2.val) :
    W (walk k z x).1.val (walk k z x).2.val := by
  induction k generalizing z x with
  | zero => exact h
  | succ k ih =>
    rcases x with ⟨a,b⟩
    simp only [walk]
    split
    · exact h
    · exact ih _ _ (hop _ h)
private def target (a b : Fin 13) := walk 7 ((0x1d8675076c01d099c36901dc99e07782552b64266036800000d8275036c00d037c2b500dc36e037826d2b5c7e902740001bd43dd09d80690d9c65703641e90d5419502543e902980000bd41b51be4029029c2570a7c0e91ad82b602b42b701b400007e40b50be426501d4375075c2d702dc2db01943bd00b400003e417d02d819600d40d6035c2e607dc37d009425f0e5800002e407d1ae40960ee409703d8e6d03dc1dd01643de05540000f6803d0ae40a50a5c19b019c19e0b640dd006419f01540002d541570ddc066009809b009c09e03b40f5002409f005400036580570f5c0e701680d502f43ed017c03900580e600140000e7c017001c3a5006806b006c06e007e6f9001801e000400015d8176000c976002802b002c02e003cd76000800e0000000 >>> (14*(13*a.val+b.val))) &&& (2^14-1)) (0,1)
set_option maxRecDepth 12000 in
private theorem found : ∀ a b : Fin 13, a ≠ b → target a b = (a,b) ∨ target a b = (b,a) := by decide +kernel
theorem allPairs (a b : Fin 13) (ne : a ≠ b) : W a.val b.val := by
  have h : W (target a b).1.val (target a b).2.val := follow _ _ (0,1) start
  rcases found a b ne with eq | eq <;> rw [eq] at h
  · exact h
  · obtain ⟨f,hf⟩ := h
    refine ⟨f,?_⟩
    intro i j lt
    obtain ⟨p,hb,ha,ok⟩ := hf i j lt
    exact ⟨p,ha,hb,ok⟩
end PEqualNP.Research.PlaneCase35Independent.Transport

open PEqualNP.Research.PlaneCase35Independent.Separation PEqualNP.Research.PlaneCase35Independent.AndCount
  PEqualNP.Research.PlaneCase35Independent.Data PEqualNP.Research.PlaneCase35Independent.Certificate in
theorem PEqualNP.Research.PlaneCase35Independent.Transport : ∀ (A B : Fin 13), A ≠ B → ∀ (extra : List Column) (gs : List Gate) (o : Nat),
    (∀ w ∈ extra, ∀ p : Fin 52, p.val / 4 ≠ A.val → p.val / 4 ≠ B.val → w p.val = true →
      ∃ v ∈ initial, v p.val = true ∧ ∀ n : Fin 468, v (52+n.val) = true → w (52+n.val) = true) →
    (∀ p : Fin 52, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro A B ne extra gs o h hp hn
  obtain ⟨f,hf⟩ := PEqualNP.Research.PlaneCase35Independent.Transport.allPairs A B ne
  apply separated_bound _ gs o _ hp hn
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,ha,hb,hp'⟩ := hf i j lt
  refine ⟨p,?_⟩
  have good0 := initial_good p (f i) (f j) ((PEqualNP.Research.PlaneCase35Independent.Transport.cover _ _).mpr hp')
  intro w mem
  rcases List.mem_append.mp mem with prev | const
  · rcases List.mem_append.mp prev with raw | ext
    · exact good0 w raw
    · intro on
      obtain ⟨v,hv,hit,down⟩ := h w ext p ha hb on
      rcases good0 v hv hit with x | y
      · exact Or.inl (down (f i) x)
      · exact Or.inr (down (f j) y)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at const
    rcases const with rfl | rfl <;> simp [good]

namespace PEqualNP.Research.PlaneCase35Independent.OrCount
open PEqualNP.Research.PlaneCase35Independent.AndCount PEqualNP.Research.PlaneCase35Independent.Separation PEqualNP.Research.PlaneCase35Independent.Data

private def flags : Array (Fin 52) := #[20,32,21,22,23,34,38,35,39,0,5,8,12,16,24,28,40,45,48]
private def supp (x : Column) : Finset (Fin 19) :=
  if x (52+159) then ∅ else Finset.univ.filter (fun i => x (flags[i.val]!).val)
private def Count (s : List Column) (q : Nat) : Prop :=
  ∀ W : Finset Nat, (W.biUnion (fun j => supp (s.getD j (fun _ => false)))).card ≤ q + W.card

private theorem cutOr (x y : Column) : supp (mix false x y) ⊆ supp x ∪ supp y := by
  cases hx : x (52+159) <;> cases hy : y (52+159) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff]
private theorem cutAnd (x y : Column) : supp (mix true x y) ⊆ supp (if x (52+159) then y else x) := by
  cases hx : x (52+159) <;> cases hy : y (52+159) <;>
    simp [supp,mix,hx,hy,Finset.subset_iff] <;> grind

private theorem grow {s : List Column} {q c : Nat} (h : Count s q) (v : Column)
    (parents : Finset Nat) (bound : parents.card ≤ c+1)
    (sub : supp v ⊆ parents.biUnion (fun j => supp (s.getD j (fun _ => false)))) : Count (s ++ [v]) (q+c) := by
  intro W
  by_cases incl : s.length ∈ W
  · let U := W.erase s.length ∪ parents
    have hs : W.biUnion (fun j => supp ((s ++ [v]).getD j (fun _ => false))) ⊆
        U.biUnion (fun j => supp (s.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      by_cases eq : j = s.length
      · subst j
        have hv : i ∈ supp v := by simpa using hij
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
  · have eq : W.biUnion (fun j => supp ((s ++ [v]).getD j (fun _ => false))) =
        W.biUnion (fun j => supp (s.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      have ne : j ≠ s.length := fun e => incl (e ▸ hj)
      by_cases lt : j < s.length
      · rw [List.getD_append _ _ _ _ lt]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rw [eq]; have := h W; omega


private theorem appendGate {s : List Column} {q : Nat} (h : Count s q) (op : Bool) (i j : Nat) :
    Count (s ++ [mix op (wire s i) (wire s j)]) (q+(!op).toNat) := by
  cases op
  · apply grow h _ {i,j} (by exact le_trans (Finset.card_insert_le _ _) (by simp))
    simpa [wire] using cutOr (wire s i) (wire s j)
  · let k := if wire s i (52+159) then j else i
    apply grow h _ {k} (by simp)
    simp only [Finset.singleton_biUnion]
    have hh := cutAnd (wire s i) (wire s j)
    change _ ⊆ supp (wire s k)
    cases e : wire s i (52+159) <;> simpa only [k,e,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem run (gs : List Gate) {s : List Column} {q : Nat} (h : Count s q) :
    Count (gs.foldl step s) (q+gs.countP (fun g => !g.1)) := by
  induction gs generalizing s q with
  | nil => simpa using h
  | cons g gs ih =>
    obtain ⟨op,i,j⟩ := g
    have next := appendGate h op i j
    have eq : step s (op,i,j) = s ++ [mix op (wire s i) (wire s j)] := by cases op <;> rfl
    simp only [List.foldl_cons,eq]
    cases op <;> simpa [List.countP_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih next

private def raw := List.ofFn (fun j : Fin 28 => input j.val)
private theorem rawRead (i : Fin 28) : wire raw i.val = input i.val := by
  change raw.getD i.val _ = _
  rw [List.getD_eq_getElem _ _ (by simpa only [raw,List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn ..
private theorem lookup (c : Column) (i : Fin 29) : wire (raw ++ [c]) i.val = source c i := by
  by_cases h : i.val < 28
  · rw [wire,List.getD_append _ _ _ _ (by simpa [raw] using h)]
    simpa [source,h,wire] using rawRead ⟨i.val,h⟩
  · have e : i.val = 28 := by omega
    simp [wire,raw,source,e,List.getD_eq_getElem?_getD]
private theorem start : Count raw 0 := by
  have small : ∀ i : Fin 28, (supp (input i.val)).card ≤ 1 := by decide +kernel
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i < 28
  · change (supp (wire raw i)).card ≤ 1
    rw [show wire raw i = input i from rawRead ⟨i,hi⟩]
    exact small ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simpa [raw] using Nat.le_of_not_gt hi)]
    simp [supp]
private theorem addConst {s : List Column} {q : Nat} (h : Count s q) (b : Bool) :
    Count (s ++ [fun _ => b]) q := by
  have empty : supp (fun _ => b) = ∅ := by cases b <;> simp [supp]
  exact grow (c := 0) h _ ∅ (by simp) (by simp [empty])

end PEqualNP.Research.PlaneCase35Independent.OrCount
open PEqualNP.Research.PlaneCase35Independent.AndCount PEqualNP.Research.PlaneCase35Independent.Separation
  PEqualNP.Research.PlaneCase35Independent.Data PEqualNP.Research.PlaneCase35Independent.OrCount in
theorem PEqualNP.Research.PlaneCase35Independent.OrCount : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29) (gs : List Gate) (o : Nat),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    18 ≤ (!op₃).toNat + (!op₄).toNat + gs.countP (fun g => !g.1) := by
  intro op₃ op₄ l r a b gs o c d pool hp hn
  have h₃ := appendGate start op₃ l.val r.val
  rw [rawRead,rawRead,Nat.zero_add] at h₃
  have h₄ := appendGate h₃ op₄ a.val b.val
  rw [lookup,lookup] at h₄
  have init : Count pool ((!op₃).toNat+(!op₄).toNat) := by
    simpa [pool,raw,c,d,List.append_assoc] using addConst (addConst h₄ false) true
  have cost := run gs init {o}
  have full : supp (wire (gs.foldl step pool) o) = Finset.univ := by
    have neg : wire (gs.foldl step pool) o (52+159) = false := hn (159 : Fin 468)
    simp only [supp,neg,Bool.false_eq_true,ite_false]
    exact Finset.filter_true_of_mem (fun i _ => hp (flags[i.val]!))
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at cost
  change (supp (wire _ o)).card ≤ _ at cost
  rw [full] at cost
  simp only [Finset.card_univ,Fintype.card_fin] at cost
  omega

namespace PEqualNP.Research.PlaneCase35Independent.Types
open PEqualNP.Research.PlaneCase35Independent.Data PEqualNP.Research.PlaneCase35Independent.Separation PEqualNP.Research.PlaneCase35Independent.AndCount
private def pts : Array Nat := #[0,1,3,9,1,2,4,10,2,3,5,11,3,4,6,12,0,4,5,7,1,5,6,8,2,6,7,9,3,7,8,10,4,8,9,11,5,9,10,12,0,6,10,11,1,7,11,12,0,2,8,12]
private def point (p : Fin 52) := pts[p.val]!
private def anchor (line : Bool) (p : Fin 52) := if line then 13+p.val/4 else point p
private def posWord (i : Fin 52) := (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i.val)) &&& 0xfffffff
set_option maxRecDepth 16000 in
private theorem posMatch : ∀ i : Fin 52, posWord i = pos i.val := by decide +kernel
private theorem posBit (p : Fin 52) (j : Nat) : input j p.val = (posWord p).testBit j := by
  simp only [input,ite_eq_left p.isLt,posMatch]
private theorem valid : ∀ (m : Bool) (p : Fin 52), anchor m p < 28 ∧ input (anchor m p) p.val = true  := by
  simp only [posBit]
  decide +kernel
private def tag (k : Fin 28) := decide (13 ≤ k.val ∧ k.val < 26)
private theorem lineShape : ∀ (k : Fin 28) (p : Fin 52), tag k = true → input k.val p.val = true →
    k.val = 13+p.val/4 ∧ p.val/4 = k.val%13  := by
  simp only [posBit]
  intro k
  fin_cases k <;> as_aux_lemma => decide +kernel
private theorem pointShape : ∀ (k : Fin 28) (p : Fin 52), tag k = false → input k.val p.val = true →
    k.val = point p ∨ (k.val=26 ∧ (point p=0 ∨ point p=1)) ∨
    (k.val=27 ∧ (point p=3 ∨ point p=9))  := by
  simp only [posBit]
  intro k
  fin_cases k <;> as_aux_lemma => decide +kernel
private theorem wordOr (x : Nat) :
    (extend x).testBit 26 = (x.testBit 26 || (extend x).testBit 0 || (extend x).testBit 1) ∧
    (extend x).testBit 27 = (x.testBit 27 || (extend x).testBit 3 || (extend x).testBit 9) := by
  have hi (v : Nat) : (v%2).testBit 1 = false := by
    have cases : v%2=0 ∨ v%2=1 := by omega
    rcases cases with h|h <;> rw [h] <;> decide
  simp [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_assoc,hi]
private theorem negOr (n : Fin 468) : let r := 52+n.val
    input 26 r = (negative[n.val]!.testBit 26 || input 0 r || input 1 r) ∧
    input 27 r = (negative[n.val]!.testBit 27 || input 3 r || input 9 r) := by
  simpa [input,neg,show ¬52+n.val < 52 by omega] using wordOr negative[n.val]!

private def Pure (S : Fin 52 → Prop) (m : Bool) (w : Column) :=
  ∀ p : Fin 52, S p → w p.val = true → ∀ n : Fin 468, input (anchor m p) (52+n.val) = true → w (52+n.val) = true
private theorem rawPure (S : Fin 52 → Prop) (k : Fin 28) : Pure S (tag k) (input k.val) := by
  intro p _ on n hit
  cases e : tag k
  · simp only [anchor,e,Bool.false_eq_true,ite_false] at hit
    rcases pointShape k p e on with eq | ⟨eq,a|a⟩ | ⟨eq,a|a⟩
    · simpa [eq] using hit
    all_goals rw [a] at hit
    all_goals simp [eq,(negOr n).1,(negOr n).2,hit]
  · simpa [anchor,e,(lineShape k p e on).1] using hit
private theorem mixPure {S m x y} (op : Bool) (hx : Pure S m x) (hy : Pure S m y) : Pure S m (mix op x y) := by
  intro p hp on n hit
  cases op
  · change (x p.val || y p.val) = true at on
    rcases Bool.or_eq_true_iff.mp on with h | h
    · simp [mix,hx p hp h n hit]
    · simp [mix,hy p hp h n hit]
  · change (x p.val && y p.val) = true at on
    obtain ⟨u,v⟩ := Bool.and_eq_true_iff.mp on
    simp [mix,hx p hp u n hit,hy p hp v n hit]

private def allowed (line : Bool) (slot i j : Fin 4) (mode : Bool) :=
  line = mode ∨ line = true ∧ (slot=i ∨ slot=j)
private instance (t : Bool) (k i j : Fin 4) (m : Bool) : Decidable (allowed t k i j m) := inferInstanceAs (Decidable (_ ∨ _ ∧ (_ ∨ _)))
-- Only leaf types and references to gate three enter this selection.
set_option maxRecDepth 8192 in
private theorem plan : ∀ (x y z t da db : Bool), ∃ i j : Fin 4, ∃ m n : Bool,
    allowed x 0 i j m ∧ allowed y 1 i j m ∧
    (if da then m=n else allowed z 2 i j n) ∧
    (if db then m=n else allowed t 3 i j n) := by
  intro x y z t da db
  match x,y,z,t,da,db with
  | false,false,false,false,false,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,false,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,true,false,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,false,true,false,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,false,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,false,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,false,false,false => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,false,false,true => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,false,true,true,false,false => exact ⟨0,0,false,true,by decide⟩
  | false,false,true,true,false,true => exact ⟨0,2,false,false,by decide⟩
  | false,false,true,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | false,false,true,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | false,true,false,false,false,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,false,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,false,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,true,false,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,false,true,false,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,false,true,true,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,false,true,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,false,false,false => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,false,false,true => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,false,true,true => exact ⟨0,1,false,false,by decide⟩
  | false,true,true,true,false,false => exact ⟨0,1,false,true,by decide⟩
  | false,true,true,true,false,true => exact ⟨1,2,false,false,by decide⟩
  | false,true,true,true,true,false => exact ⟨1,3,false,false,by decide⟩
  | false,true,true,true,true,true => exact ⟨0,1,false,false,by decide⟩
  | true,false,false,false,false,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,false,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,true,false,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,false,true,false,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,false,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,false,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,false,false,false => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,false,false,true => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,false,true,false => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,false,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,false,true,true,false,false => exact ⟨0,0,false,true,by decide⟩
  | true,false,true,true,false,true => exact ⟨0,2,false,false,by decide⟩
  | true,false,true,true,true,false => exact ⟨0,3,false,false,by decide⟩
  | true,false,true,true,true,true => exact ⟨0,0,false,false,by decide⟩
  | true,true,false,false,false,false => exact ⟨0,0,true,false,by decide⟩
  | true,true,false,false,false,true => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,false,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,false,true,false,false => exact ⟨0,3,true,false,by decide⟩
  | true,true,false,true,false,true => exact ⟨0,1,false,false,by decide⟩
  | true,true,false,true,true,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,false,true,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,false,false,false => exact ⟨0,2,true,false,by decide⟩
  | true,true,true,false,false,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,false,true,false => exact ⟨0,1,false,false,by decide⟩
  | true,true,true,false,true,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,false,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,false,true => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,true,false => exact ⟨0,0,true,true,by decide⟩
  | true,true,true,true,true,true => exact ⟨0,0,true,true,by decide⟩
private def rawIndex (k : Fin 29) := Fin.ofNat 28 k.val
private def indices (l r : Fin 28) (a b : Fin 29) (k : Fin 4) : Fin 28 :=
  if k=0 then l else if k=1 then r else if k=2 then rawIndex a else rawIndex b
private theorem choose (i j : Fin 13) : ∃ A B : Fin 13, A≠B ∧ (i=A ∨ i=B) ∧ (j=A ∨ j=B) := by
  by_cases e : i=j
  · subst j
    by_cases z : i=0
    · exact ⟨i,1,by simp [z],Or.inl rfl,Or.inl rfl⟩
    · exact ⟨i,0,z,Or.inl rfl,Or.inl rfl⟩
  · exact ⟨i,j,e,Or.inl rfl,Or.inr rfl⟩
private theorem sourcePure {S n m c} (k : Fin 29) (hc : Pure S m c)
    (h : if k.val < 28 then Pure S n (input (rawIndex k).val) else m=n) : Pure S n (source c k) := by
  by_cases lt : k.val < 28
  · simp only [ite_eq_left lt] at h
    simpa [source,lt,rawIndex,Fin.ofNat,Nat.mod_eq_of_lt lt] using h
  · have eq : m=n := by simpa [lt] using h
    simpa [source,lt,eq] using hc

end PEqualNP.Research.PlaneCase35Independent.Types

open PEqualNP.Research.PlaneCase35Independent.Separation PEqualNP.Research.PlaneCase35Independent.AndCount
  PEqualNP.Research.PlaneCase35Independent.Data PEqualNP.Research.PlaneCase35Independent.Types in
theorem PEqualNP.Research.PlaneCase35Independent.Types : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    ∃ A B : Fin 13, A ≠ B ∧
      ∀ w ∈ [c,d], ∀ p : Fin 52, p.val/4 ≠ A.val → p.val/4 ≠ B.val → w p.val = true →
        ∃ v ∈ (List.ofFn (fun j : Fin 28 => input j.val)), v p.val = true ∧
          ∀ z : Fin 468, v (52+z.val) = true → w (52+z.val) = true := by
  intro op₃ op₄ l r a b c d
  let ks := indices l r a b
  obtain ⟨i,j,m,n,hx,hy,hz,ht⟩ := plan (tag l) (tag r) (tag (rawIndex a)) (tag (rawIndex b))
    (decide (¬a.val<28)) (decide (¬b.val<28))
  let label (k : Fin 4) := Fin.ofNat 13 (ks k).val
  obtain ⟨A,B,ne,hi,hj⟩ := choose (label i) (label j)
  let S := fun p : Fin 52 => p.val/4 ≠ A.val ∧ p.val/4 ≠ B.val
  have leaf (k : Fin 4) (mode : Bool) (h : allowed (tag (ks k)) k i j mode) :
      Pure S mode (input (ks k).val) := by
    rcases h with e | ⟨line,mem⟩
    · rw [←e]; exact rawPure S _
    · intro p off on
      have e : p.val/4 = (label k).val := (lineShape _ _ line on).2
      rcases mem with rfl | rfl
      · rcases hi with eq | eq <;> rw [eq] at e <;> exact False.elim (by rcases off with ⟨u,v⟩; contradiction)
      · rcases hj with eq | eq <;> rw [eq] at e <;> exact False.elim (by rcases off with ⟨u,v⟩; contradiction)
  have hc : Pure S m c := mixPure op₃ (leaf 0 m hx) (leaf 1 m hy)
  have left : Pure S n (source c a) := by
    apply sourcePure a hc
    by_cases h : a.val < 28
    · rw [ite_eq_left h]
      have leafOk : allowed (tag (rawIndex a)) 2 i j n := by simpa [h] using hz
      exact leaf 2 n leafOk
    · simpa [h] using hz
  have right : Pure S n (source c b) := by
    apply sourcePure b hc
    by_cases h : b.val < 28
    · rw [ite_eq_left h]
      have leafOk : allowed (tag (rawIndex b)) 3 i j n := by simpa [h] using ht
      exact leaf 3 n leafOk
    · simpa [h] using ht
  have hd : Pure S n d := mixPure op₄ left right
  have liftWire {mode w} (pure : Pure S mode w) (p : Fin 52) (ha : p.val/4 ≠ A.val) (hb : p.val/4 ≠ B.val)
      (on : w p.val = true) : ∃ v ∈ (List.ofFn (fun j : Fin 28 => input j.val)), v p.val = true ∧
      ∀ z : Fin 468, v (52+z.val) = true → w (52+z.val) = true := by
    let v : Fin 28 := ⟨_,(valid mode p).1⟩
    exact ⟨_,List.mem_ofFn.mpr ⟨v,rfl⟩,(valid mode p).2,pure p ⟨ha,hb⟩ on⟩
  refine ⟨A,B,ne,?_⟩
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact liftWire hc
  · exact liftWire hd

open PEqualNP.Research.PlaneCase35Independent.Separation PEqualNP.Research.PlaneCase35Independent.AndCount
  PEqualNP.Research.PlaneCase35Independent.Data in
theorem PEqualNP.Research.PlaneCase35Independent : ∀ (op₃ op₄ : Bool) (l r : Fin 28) (a b : Fin 29) (gs : List Gate) (o : Nat),
    let c := mix op₃ (input l.val) (input r.val)
    let d := mix op₄ (source c a) (source c b)
    let pool := List.ofFn (fun j : Fin 28 => input j.val) ++ [c,d,fun _ => false,fun _ => true]
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst ∧ 18 ≤ (!op₃).toNat + (!op₄).toNat + gs.countP (fun g => !g.1) ∧
    29 + op₃.toNat + op₄.toNat ≤ 4 + gs.length := by
  intro op₃ op₄ l r a b gs o c d pool hp hn
  obtain ⟨A,B,ne,allGood⟩ := PEqualNP.Research.PlaneCase35Independent.Types op₃ op₄ l r a b
  have hand : 9 ≤ gs.countP Prod.fst := by
    apply PEqualNP.Research.PlaneCase35Independent.Transport A B ne [c,d] gs o allGood _ _
    · simpa [pool,PEqualNP.Research.PlaneCase35Independent.Certificate.initial,List.append_assoc] using hp
    · simpa [pool,PEqualNP.Research.PlaneCase35Independent.Certificate.initial,List.append_assoc] using hn
  have hor := PEqualNP.Research.PlaneCase35Independent.OrCount op₃ op₄ l r a b gs o hp hn
  have counts (xs : List Gate) : xs.countP Prod.fst + xs.countP (fun g => !g.1) = xs.length := by
    induction xs with
    | nil => rfl
    | cons g t ih => cases h : g.1 <;> simp [h] <;> omega
  refine ⟨hand,hor,?_⟩
  have eq := counts gs
  cases op₃ <;> cases op₄ <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] at * <;> omega
