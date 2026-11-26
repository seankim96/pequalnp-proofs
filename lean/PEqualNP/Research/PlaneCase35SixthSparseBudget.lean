import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset


namespace PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndSeparation

abbrev Column := Nat → Bool
def disj (ws : List Column) (r : Nat) := ws.any (fun w => w r)
def both (a b : Column) (r : Nat) := a r && b r
def wire (s : List Column) (i : Nat) : Column := s.getD i (fun _ => false)
def addOr (s : List Column) (g : Nat × Nat) : List Column :=
  s ++ [fun r => wire s g.1 r || wire s g.2 r]
def good (p a b : Nat) (w : Column) := w p = true → w a = true ∨ w b = true

private def From (base : List Column) (w : Column) :=
  ∃ ws : List Column, (∀ v ∈ ws, v ∈ base) ∧ w = disj ws

private theorem readFrom {base s : List Column} (h : ∀ v ∈ s, From base v) (i : Nat) :
    From base (wire s i) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases he : s[i]? with
  | none => exact ⟨[],by simp,rfl⟩
  | some w => exact h w (List.mem_of_getElem? he)

private theorem allFrom (base : List Column) (gs : List (Nat × Nat)) :
    ∀ v ∈ gs.foldl addOr base, From base v := by
  have step (s : List Column) (g : Nat × Nat) (hs : ∀ v ∈ s, From base v) :
      ∀ v ∈ addOr s g, From base v := by
    intro v hv
    rcases List.mem_append.mp hv with old | newWire
    · exact hs v old
    · obtain rfl := List.mem_singleton.mp newWire
      obtain ⟨l,hl,el⟩ := readFrom hs g.1
      obtain ⟨r,hr,er⟩ := readFrom hs g.2
      refine ⟨l ++ r,?_,?_⟩
      · intro w hw
        exact (List.mem_append.mp hw).elim (hl w) (hr w)
      · funext i
        simp [el,er,disj]
  have run (gates : List (Nat × Nat)) (s : List Column) (hs : ∀ v ∈ s, From base v) :
      ∀ v ∈ gates.foldl addOr s, From base v := by
    induction gates generalizing s with
    | nil => exact hs
    | cons g tail ih => exact ih _ (step s g hs)
  apply run
  intro v hv
  refine ⟨[v],by simpa using hv,?_⟩
  funext r
  simp [disj]

private theorem fromGood {base : List Column} {w : Column} {p a b : Nat}
    (h : From base w) (hb : ∀ v ∈ base, good p a b v) : good p a b w := by
  obtain ⟨ws,sub,rfl⟩ := h
  intro hpos
  obtain ⟨v,hv,hp⟩ := List.any_eq_true.mp hpos
  rcases hb v (sub v hv) hp with ha | hc
  · exact Or.inl (List.any_eq_true.mpr ⟨v,hv,ha⟩)
  · exact Or.inr (List.any_eq_true.mpr ⟨v,hv,hc⟩)

def separated (s : List Column) :=
  ∃ n : Fin 257 → Fin 468, ∀ i j : Fin 257, i.val < j.val →
    ∃ p : Fin 52, ∀ w ∈ s, good p.val (52 + (n i).val) (52 + (n j).val) w

end PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndSeparation

open PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndSeparation in
theorem PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndSeparation : ∀ (base : List Column)
    (gs : List (Nat × Nat)) (left right : Nat),
    (∀ l r : List Column, (∀ w ∈ l, w ∈ base) → (∀ w ∈ r, w ∈ base) →
      separated (base ++ [both (disj l) (disj r)])) →
    let s := gs.foldl addOr base
    separated (s ++ [both (wire s left) (wire s right)]) := by
  intro base gs left right h
  let s := gs.foldl addOr base
  have hs : ∀ v ∈ s, From base v := allFrom base gs
  obtain ⟨l,hl,el⟩ := readFrom hs left
  obtain ⟨r,hr,er⟩ := readFrom hs right
  obtain ⟨n,hn⟩ := h l r hl hr
  refine ⟨n,?_⟩
  intro i j lt
  obtain ⟨p,hp⟩ := hn i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact fromGood (hs w old) (fun v hv => hp v (List.mem_append_left _ hv))
  · obtain rfl := List.mem_singleton.mp last
    change good _ _ _ (both (wire s left) (wire s right))
    rw [el,er]
    exact hp _ (by simp)


namespace PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndBudget
open PlaneFirstAndSeparation
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
end PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndBudget
namespace PEqualNP.Research.PlaneCase35SixthSparseBudget.Rows

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
end PEqualNP.Research.PlaneCase35SixthSparseBudget.Rows

namespace PEqualNP.Research.PlaneCase35SixthSparseBudget.Seed
open PlaneFirstAndSeparation PlaneFirstAndBudget
open Rows (input mix pos neg extend)
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def omittedFlags : Nat := 4406657483279
private def indices (i : Nat) : Nat :=
  (0x193c96431d8dc662f1588c3e170781c05fefb7cbddeaf378bbddae973b95c2df6eb65aed568b3d9ac961b057ebd5dae56eb358abd5aa953a8d429f4da65228d45a250a833f9f4e66f3499cca5f2c95caa53289348a411f8d46631168ac52271288c421d0d8642a110783412070280bf9f6f97c3ddecf479bc9deec753a5d0e772b8dc4e06fb75b4d96c355a0cf6632d92c863b198ac461b0982bc5dae972b55a2c960af572b556a853a9948a351285409f4f27134984b255288f47235188b4521d0c8541a09027f3f1f4f6793c1dcec74399c4e06f369b0d66833998ca633117cbc5a2c960aa5327938964a249188a44219007e3e1e0ec6c35198c4602e160ac54291408c44210d06430160a85026110803c1c0d0602c14090401c0a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x2001000200010020000046000001100100010008001000080500000208008000800400080004048000010401000040040084002000400020020080082002000200100020001001004000100100010008081000088080200008008000800400080004004010000400400040020404000200200800020020002001040200010011000001004000100108010008000880000080208008008000800400044000004010000400440040028002200800200840020024002001 >>> (28*i)) &&& 0xfffffff

private def negativeWords (i : Nat) : Nat :=
  (0xa424848e42084a64080d2a4048c824028d0e2a040a6290422e28042ae22044a621848262104a262084c2a2040e822024e061908226180832e130a02e128242a124a40e120a42a114a20e110a22e108252a104a602102870a0e0c08a0c0c1860b0c02e0a0c0a6090c222082c30a070e00a060e08a058680a054a80a050e80a044a882042c90e038602e030e02e028642a024a48e018682a014aa02012ca0200a4d020068e09c4001c9c2010c9c0011c9940214991022499002349884128984021c9824308982030c9814320981032498043285700045d64000d55080515500055d484109d480119d44001d942014c5408151d4041491402154531002553040615300065d2804295250405d24040dd2040691202464d150205d140215d114221d110225d10c241d108251d1042611102074d0c04195098501509412150905215088511d0841291082530906060cd058601d050605d048611903070490287401022544d01c301d018701d014321d00c341100a5508e4008cce0008ecc8011a8c4009c4c30106cc2010e4c181824c101864c081920c021944b210064b100264b01026ca8102a8a6100c8a45088ca2100e0a030a44989012896120489492108941214c930206c929202c921206c910226c909212090303448a910288a5108888512808831308865208886120c88452880843094c830306c8293028825308881c380c81838288143a0880d380080b19008071a04710007470804347000474650085c644089c64008dc62004e461008746080c345c08114588013458081345508054520846451080745080530502854c4c4809c4c0819c4a090a449810344949014488113c48490944548814450885c4448890442894443090684249480422944441c181441818344149810412984440c1c1040a1d004069c043890034385021438102343210464310027430d041430904343050610303064c2c5009c2c140942904234289403c28502942584814250485c24508902434840223444421848302124a4020b4c002070e041c901141c580141948214190823418901341858210183830c154a01c150a05c1492110143814c130a06c1292428125a400123844c114a21c10d241010786040c9411c0c580900c3c1080a590800a3d00409850340949210092d20008b51000879208070e048065a080063c04c05c281c058681c054a810052c84c04d281004b490c0387020032d04802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i)) &&& 0xfffffff

private def mins (i : Nat) : Nat :=
  (0x80002008000008400000240000012000000100000008000000400000020000001000000080000004000000200000010000000800000040000001000000080000004000000200000010000000800000040000002000000100000008000000400000020000001 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x1fe03f7e077e00003f807ef00000ff077f000000000000000003bb001baa4d58800688841c794f42c010a003d01e001b8801c00e24800032400000140400033f9eb0e01d0000000000000000df7947d0190e3b71a0882e86040c0c00800200000000000000003fb7f7f7e71e000000000007efdb7f0e9deff23f706c607409fffffffffffc0000000000000000000000000000000000000000000000000000000000000001ffffffffffffffc0000000000000000000000000000000000000000000000000fff800000000001fffffffffff000000000000000000000000003e00000000007003ff800000000ffc000000007ffffffffe000000000000000000ff800000000001803fc000000601fe0000003fe0000000fffffe000000000000003ff800000380b01c1fe0000000e0ffc0001c0ff000007fc000ffffc0000000381803f00000200601000fe0004008401e00000707f000381f007f001ff8000000000187f00488108066040f0090031c00f000e2430780000c7830780e03fe018901e0b3078103002000000470061149c66700081040380100020003c0c1c0f802628c1573381060011160e1a702c40090027122141993c04098c319101c9e63102821002152000104000c48ab6050052500b640a10a019a1828544245090ced64020a400a1481542121151201600010006a36840022d2aa8a89059417525545e000000000000000000000000000017fedffb1c000000000f7ece79cddfc6c339d803bdffbd5a0000000000000000000000000000bdebfcc80000077b75ede62503fa003febd60000001d00dbfd200000000000000000000000edf000015b557400003fc07efc0efc00007f00fde00001fe0efe0000000000000000077600375480000000000018be1bc0001f87f97e0000787fc00007c3ff00000000000fe00ff387c00007c3e0000000000000034f050000c7e3b0001e3f8001ef00000001f83fc4e39c0006300058f630f000c600000000000628580061c5e0098007600000e40cbc3618006871c0079999b004001c40530048000000000d32814d805034000450020544080ad406d40116288098601618880801c68840200000114c05040100d58800688841c794f42c010a003d01e001b8801c00e248000324000001404000000000000000fd5699add101541baf5ada0b00b70e805a206205a0059000511019fcf58700e80000000000000006fbca3e80c871db8d044174302060600400100000000000000001fdbfbfbf38f000000000003f7edbf874ef7f91fb836303a04 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def packed (i : Nat) : Nat :=
  (0x3ffc4c3ffebfff73fffffffffffe69724ffffffffffffffffffffafffdcfffffffc4fff9bfcbffff47fc7fc3ffffffffe9fff77ffd3ffffff2e6ff2fff93ffffff0fffff0ffffff8fffff4cefffcfffe5cbffe41bffffffffffc3ffebfffffffd3fcb1bffe6ffffff93fff1ffffffffffffffffffffffffffffe3fe2c9a65283fc7fc3f33ffffffffff7fffd2ffffff8ffff26bffe0ff1ff0ffffffffffffffffff48cfc7cffffffdafff83fc7fc3ffffffffe9ffffd9fffffffff8ff8b24fffffff1ff08bffffffffffffffff4fffc7ffffffcbf38a83fc7fc3ffffffffffffffdafd3fca1ff8ffffffcefe0ff1ff0ffffffffffffffffff4cefc7cfffffffffca83fc7fc3ffffc3ffe9fffffffd3fffff38c7fffffffe0fffffffffff0fffa7ffff6bf4ce287fe3ffffffffffffc7ffdbfffffffebfffffffd2fff13ffdffff77ffcdff1ff0fffffffffaffffffff48dfffcff7fffdd67fffffffc3ffffffffebffffffffffffffffdffff74e4bf731ff0fffffffffa7fffffffffffffccb7fffddfff47fc7fc3ffc4c3ffeb97ffffffffffff3fdffff77f4bf73fffffffffffffafffffffffce2c4fff7ffffffff45cc7fc3ffc4c3ffebffffdbfd2ffffffffffff74efcdfffffffffffffffafffff6ff4bffc4fffffffdd3bf37ffffc3ffffffffe9fffffffd1fffffffdffff77f2bfff1ff0fffff0ffffffffffff48efffcffffffddfff19cc7fffffffc3ffebffffd9fd238b1bfffffff77ffffff1ffffff530fffafffffffffccfffcfffdbfff67f47ffffffffffc3ffebfffffffd1fffff3ffffff69957fffffff6ccffffffaff8fffd4ffffffffffffcbf652ffffffc3ffffffffebfe3fff53f33fffffffff2fd94bffffff0ffffffffffff8dffff4bffffffffffc9afff37ffffc3ffffc3fffffe37ff55237fffffffff26bfffffffffffff530fffafffff6fffffffffffffffd3395fccc7fffffd4c3ffebfff7dbfff33f1fffffff24fffffff1ffffff530ffffffffffff4fffc7fcbffffff39537fc7fffffffc3fffffffffffd3fcbffffc7ffffce54d331ffffffff0ffffffffffff4ff2c7ffffffffffd537fc7fffffffc3ffff97fffffd333fff3fc7ffffff546fffffffffff0fffae6fff6bf4cd2c7ffffffffffd5fffc7fffffffffffffffffdbffffffff32ffff24cefffff1ff0fffffffffafffdf6d4fff2fffffffffd33bffffc7fc3ffffffffe9fe27fffff3bffff2ffff2ffffd1ff1ff0fffff0fffae5fdcfffffffffcff1fffd3ffffffffffffffffffffffe2fff513fff1fffffff2fff28dff1ff0fffff0fffafffddfd54ffffffff1ffcbf3bfffffffffffffc3ffebfe37da553fcb1fffffffffcefffff1ffffffff0fffa6681ffff4cefffccbfffcbffcaffffffffffffc3ffeb92377f5533bfffffc7ff2ffffffffffffffffe8fffffffdcfff47fffffff9a55edfe4ffffffffffeca3fffffffffffffffffefbbf97fb69911fffffffffb28ffffffffffd747f23ffffffffeda64ffffffffffffa3fffffffffffd1ffffefffffffb6957f73fffffffb28ffffff8bf6ff4bffc5ffffff7adfff37ffffffffffa3ffffffffdb55237ffefffffffb69fff73ffffffffe8ffffffffffff48cfffbff1dbfeda7f1bffffffffffa3ffff97f73ffd1ffffffbbffd7b7f57ffffffffffb28cbffffffffffffffffbffffffeda52fff17fffffeca3ffff97ffff5ff33f16fbbffffb69491ffffffffffe8fffffffde6ff4bfffffffffffedfff34c17fffffffa3fffffff79bfd2fff17fffffffb69fcdffffffffffe8fffffffff6ff48cfffbffffffeda7f1bfffffff73ffffffffffffffff3bf16ffe6fdefff920fffb3ffffffffffffffdcffffccfc5bff9bf5edfff83ffecfe573fff0ffffffffffff3bffefbbffdefff93ffc8b3f95cfffffffff83fffffce23fbeefff7bffe4ffffffffffffffffe8ffffff5ff33ffefbbfffffd9906fffb3ffffffffffa3fffffd7fcdfc6bff9bffff664ffffecffffffff1fe8fe073ffff37ffefba6957fffffffffffffffb3ffffa7ffdefd7fcefc5bee9bfffffff47ffffffffffff2ffffff799fff3bf1affe6fffb7fffffc8b3ffffffffffffffff67ffcefffbeefe5fedfe41bf16cffffffffffe9fe07995d13881afbbffffffffffffffff8bffffffffe4ffffffffffc5bff7fffff3bfffffecfe273fff0fff93fffffff3bffeffdfffffffffffc5fff8bffffffffe4fffffffcefc5bff7ffffffff83ffffffffffffffff9bffff55233f1effffffffd9fe0fffb3f88cfffc7ffe6ffffffffffffbfffff5edfd5ffffffffffffff1fff9bfffffff33ffeffff897fff560ffffffffffffffffe4fdc67ffcefffbff1e2fedffffffffffe2fffff1fff9bf7d95523bf1efffffffffffe0fffffffffffffffa3f8bfffffff23ffee7ff7bffd537ffffffffffffffe897fffffff3481affdfffffff57ffffb3fffffffffffff8bfffffff2bffeefff7bf3bffdc17fffffffffffe8fe2fff57ffca17fbbffdefcefffffffffffffffc3ffe5fffffffcefffbff7ff7bffca1bf23fffffffff0fff97fffffff3bf1affdfffffffffffc8fffffffffc3ffe58bfffffce2bfbff7fffffffffdc17fffffffff1fe9920fff57f38a1affdffffffffffffffffffffffc3ffe683fffffcdfffbfffdb5ff655fffffffdbfffff2fff9bfffffffffffefffffffb7f28dfc8b3f6ccfffffffe4fdefffffffffbee1fffffffffffffffdb33fff2fff9bf7ff5fffca1efbbffffb59fcdfffb3fffffffffffe6ffffd744dfffbffffffff64affffffffffffffffe893fffffff33ffeffc76fffd9fc6ffffff6fffffcbffe683ffd7fcd287bffffffff67fffffffffffffff1fff9a2ffffff33f1efffffd7fff551ffffffffffffffffffffffffffffc7feefff5edfff34c22cffffffffffe8fe27ffffffc8fffbbffd7ffffff33ffffffffffc3ffe6fdf6fffcdfffbfffff5fffd5fff23fffffecffffff9a27ff5fffc8fffbbfffffce4bf33ffffffffffcbffe6fffffffcefc7bfffffffffd247f23fffffffff2fe99bffff5ff3881effffffffff491fffffffffffffffa3ffde6fffffffffff1fffed38afcc23fffffffffffffffffdb5fffff1fffffffffce28dfc8b3ffffffffffa3f89e6fffff2bffeeffffffffffcc17fffffffffffe997f7bffff3bffefb87ffffff2bfffffffffffffcbffe6fdf65744efc7bfffffffffcafff23fffffd4a3fffffffffffd333f17ffe6ffffff920ffffffffffffffffffffffd44ccfc5fff9bfffffe483ffffa3fffffffb3fffffff5d1ffffe7ffffff6a993fffffe8ffffe8fedfff83ffff4ff23f9ebfff5fffe4fffffffe533ffffb3ffffffffffffffe7afffff4ff93fffffe8fffffffecffffffffffccfff9eb9a5fd3a7f47ffffa25ffffffffffffffffd3fff13ffe6ffffff90dfc8fe8fccfffffffffffffd74ff23ffebfffffffe437ffffa3ffffffffffffffda5d337ffe7fffffffe993ffc8fe8ffffe8fedfff83f6974cd23ffffffffffa64fffffffe273ffffffffffffffffffffffafffde7694a0ffffe88bfffffecfffffffff4bffff3eb7fffddfff83ffffa3f73ffffffffffffffd23ff17fffffff769fe0ffffe8ffffffcffffffdcfff48ffc4fffffffdaa7f83ffffa3ffd4a3fffffffffffffffffffaff8974e9560ffffffffffe8ffffffffffff4cffffffffe2fffa5583f17fffffffff3fff9ff73f53ffc817faff8bf4e94bfffffe8ffffe8ffffe7fdd6954cffc5fffffffffa7f83fffffdbffffffffffffffffd1fffffffdffde77f2bffc8fe8fff528ffffff8bfffffcfffffebfff7bffff45cfffffffd4a3ffffffffdbfd1ffffffffffff76957ffc8fffffffe8feffffffffff47f23ffebffffddfd5fdcffffffffffffffffe2ffffffffffcfadffdefe9491ffffe8ffffffcfffffffffffffffc4ffffff7bfa7f45c23fa3fffffffffffe2fff53f3c8fffafffdeffffd1ffffe8fffffffecfff8bf6ff4bffc5febffffddfff37ffffa3ffffffffffffffdb511ffffffffffff7692bffc8fe8ffffe8feffff83ffd548f2bffebfff79dffffffffffdbfffff3fffffffffffffff13fafffff6a9491fc8fe8fff128cffffffffffffffffffebfdbfdaa5247f17fffffc4a3fbfffffffffd23fffffafffff6a9fc6ffffffffffe8feffe781efff4bf286febffffdafffffffffffffffa33ffffff73ffffffffffafffd74ff57ffc5fffffffe8feffff89cffffff205febfff5d3fffffffffffffffa3fffffe2ffffd33fffffafffd7fe9546ffffffffffe8feffe781dfff4ff206febfffffffd5ffffffffffffff2b3f97f7bfffffc8fcfafffff4fffffffffe8ffffffcffffffde6fffcffc4fffffffffa7f47f23fa3ffc4a33bffffffdb5ffffffffffffff4e9ffffc5ffffff128ffffffffffd74fffff3ffffffffa4a37f23fffffffff2fff97fffffd3fff13ffffffffe928dfc8fe8ffffe8cadfffffffff4ff2bf3ebfffffffff37f17fffffffa3fffffe2fff5d33ffffffffffffe9286ffffffffffe8ffffe7fde6974cffc6fffffffffa4affffffffffffa3fbffffffda5d33caffffffffffe9fc6fc5fff97ffffffffffffffd4ffffff9e39bf79d3a483fffffff73fff0ffffffffffff3bf127ffffde77ffe0fc8ffffdcffffecffffffffffce2059e39bfffffff83fffffe533fffffe8ffffdafffffffff8e6fd7fce93ffff53fffffffc2dffffffffffccfff9e3fff5ffffffff154fffffffffb68fffffffff33f1678ffffffff920fff53ffffffffeca7ffdcffffce23f9e39bffd3ffffffffffe5fffffffe8fff75a53ffc8fff8ffffffce93fffffffffffffc2dffffddffffcefc49e3fffffffff83f23ffff73ffffbbffffffffff37ffe7ffffff75993ffff53ffdcffffecffffffffffcdfff9cbfff7bf67ffffffffff73fffffffffffff53f34bfe7ffffdefd993fffffff97ffffffffff8fffffffffc5fff9bf79d3bf37ffd4fe573ffffffffe3ffffff3bf167ffffdeffffd1ffffff97ffffffffff8fffd4ffffc5fff9bf7bf3a437fffffff73fff0b3ffe0fd9fff3bffe72fffff77fffffffffffdcffffeefff8ff67f44e2ff9ffffffddfe4fffffffffffffffbbffffffffff33ffe7fe6fd7699fc6fff53ffffffffeeffffdcffffcdfc69ff9bffda67fffffd4fffffffffbabffffff5ff33f127fe6ffffd9fd1ffffff94cffffffffffdefffffffc49ff9bffdafff37f23ffe533ffffffffe3ffffffffffe7fe6fff6bf90dfc513ffffffffeca3ffdefd7fcdfff9cb9bffff67ffffffffffffffffbbfffffff5ff33ffe7fffffffd9fc6fff13f94cffffffffffff6bffff2ffffffff5ff3a437f17ffe5ffffffffffe375affffff17ffe6fd7fcefcdffffffffffffc2efff8ff6bffccfff9fffff5ffffffff154ffffd4ff1babfe375afff37f1a7ffffd7ffffffffffff94cffffffaff8deffffff2c5fff9bffd33bf47ffffffffc4ff2bbfffffd9fff3bffe7ffffff4ffffffc5fffffffffcaeaff8de67ffcefc59ffffffd3fff47fffffe5fffffffffffffda5ffffffff2ffffffce90dfc813f97fffffffa3ffff6bfffffc4fff9bffff3bffff23ffe5fffffffffffffda5fffcbffffffffffce93ffc5fff97fffffffaff8de6974ff2c5fff9bffff3bfffffffffffffff2b7fffffff5ff3bffe72fffffffffc6fc813fffffffcada7f81e6bffcefc69cbfffffffffffffffffffc4ff2bbfffffda5d338bfe7fffffffffffffc5ffffdcffffffa3ffffffffcfffffe37fffdd64a83fffffff73fffffe8fffffffff3fffff8fffff759fe0fff13ffdcffffffa3ffffffffcf284fe3ffffdd67f83fffffff73fffffe99ffffffff3c817f8dfffffff4a0ffffff8bfffffeca24ffffffffffc53e37fffffffffffffffe273ffffffffffffffff3fffff8fffde77f2a0fc813f89cfffffffe7fff67ffcffc4fff7ffffffff83f23ffff73ffffbffffffd9fff3cafff8fffff77ffe0fc5ffffdcffffefa67fff67f48f285fffffffddfff83ffffffffffffffe89ffffffff3fffff8c7fff699560fff53ffffffffefa3ffffffffcffc7fe3ffffda67f83ffd4fe2fffff0b3f9bf7ffffffcafcf8fffff6bffffffffffffffffcffa3ffdffd4fcffc7fe3ffffff64a83fffffffffffffbe8fff73f57f3fffff8ffffffd9fe0fff13f8bffffc2dfe6ffffffffffff3fffffffffd5fff214fe2fffff1b7f9bffffffffc8fcf8ffffffff57ffffffffffffffffa27fdd6bf4cfffffff1e25fffd583ffffffffd4fffbff9fffdafd33c81fffffffffff560ffffff8bffffcefa67fdf67ffcf207fe3ffffd3fff83fffffe2fffff0b7f9bffda53fffffcffffffffff2bffc8fff8bffffc7ffe6fdf695fff2bf3e3ffffff3bfffffffffffffff3fff9ff7dafd33ff1ffffffffffffe0fc8fffffffffcefa67fdd6954cf2bfffffffffffff83fffffdb73fffffe8fffffffff3fffff2dfffffd957ffff53ffdcffffffaff8ffffffcfffffff7fffdd6551bfffffdbffffffbbf93fffffffffffcffdffdefd9ffffff13f6fffffc3ffe48fffffffffc43ff7ffffffff37fffffff73fffffe89e0fff53f3fffffffffdefd92bffffffffdcffffffaff8fffd5fcffffffffff7bf67f1bfffffff73fff3feb9e3fff57f3cb1bfffffdefd9fffffffffffffffc3fffffff6fffff2fffffffffdd395fdc17ffffffffffbbf963fffffffff14ffdffdeffffcdfff53ffffffffefa27fff6fffcffc6fff7ffffffd5fdc214fff73ffffbeb9ffffffd13cb1bffdffff77f57fffffffffffffc7fae58fffd4fff2ffffffff7bf392ffffffffffffff3fe9fe2ffffff3ff13fffffdeffffd1708fffffffffcfffff8ff6fffcf2ffffffff7bffd245c17ffff73fff3feb9e3ffffff3cb17ffdffdeffffd1ffffffffffffc2effffff6d5fff2fffffffffdd3bffdc17ffffffffffbfffe2ffffff3fffff2fffde77ffc670813ffdcfffceffff8ff67f48f2fffffffffddfff1bfffffffffffffbe8fe07fffff3fffff2fffd7699ffffffffffffffffffae78dcffffcfffffff1db5da67f1bffffffffffff3beb9e37fffd13cb1fffffffffd9ffffffffffff13ffffae7ffffd7fcfffffff1fffff65247ffffffffffff3feb9e3fff5ff3ff1fffffffffd9491ffffff6fffffcacfe6ffffffffffff3ffffffdafcafff23ffdbffffffbbf93f7bffffffffcffc7fff6bffffffffff6fffffcaefe68dffff4bf2c73ffffffdaffffffffffffffffffbff9e07ff5d13fffffffffff6992bffffffffff13ffefae78defd748fffffffffffff67f1bffffffffffff1bbffff7dbfffffffcfffffd74fffff33ffffffffffcffaff8dc6fffcffffffffff5d3fff47f17fffffd4ff3bebfe37fffff3ff1ffffffd7ffffd1fffffffffffffffffffff6ffffffff3cb1ff5ff395fcc23fffffffff0b7ffe2fffffffff1ffffffd7ffffcdfc853fffffffc3ffe5fdd6fffff2fffffffffff395fcc17ffff33fff1bbf9a37fffd3fcb1ffffffd7ffffcdfffffffffffffffa3f89dfff4cfffffcbfff5fffff1bffffffffffff3bfffe07dafff3ff1ff2fffd7fffffffc8fffffffffcacffffdf6d7ffffc73ffffffd33bffff23ffff33fff2bab9bf7ff5fffcbfcfffffff4ce4bffffffffffffffefa7f89effffcfffffcb1fffd3fff47ffffffffffff3be9fff7d9fff3ff1ffffffff4fffd1fc8fffffffffcffae78de657fcf2fffff1ffffffff47fffffffffffffb6897ffdb5fffffffffffffffce2bffc813ffccfffcaeae4fde697fff2fffffffffff3bffff17ffffffffffbe99ff7bf5d33ffffffc7ffffff286ffffff >>> (174*i)) &&& 0x3fffffffffffffffffffffffffffffffffffffffffff

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
set_option maxRecDepth 12000 in
private theorem bits28 : ∀ j : Fin 257, (boards (28)).testBit j.val = true → (mins (28)) &&& (negativeWords (j.val)) = (mins (28)) := by decide +kernel
private theorem boardOK (w : Fin 29) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
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
  | ⟨28,_⟩ => exact bits28 j
  | ⟨a+29,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 29) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 29) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 29) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 29) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 29) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 29) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 29) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 29) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 29) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 29) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 29) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 29) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 29) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 29) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 29) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 29) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 29) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 29) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 29) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 29) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 29) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 29) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 29) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 29) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 29) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 29) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 29) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 29) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 29) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 29) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 29) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 29) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 29) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 29) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 29) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
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
  obtain ⟨w,hw,on⟩ := member (List.range 29) full
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
theorem pairGuard (i j : Fin 257) (lt : i < j) :
    ∃ p : Fin 52, omittedFlags.testBit p.val = false ∧
      pos p.val &&& (neg (ix i) ||| neg (ix j)) = pos p.val := retained i j lt
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
def c := mix true (input 15) (input 27)
def d := mix true (input 17) (input 26)

end PEqualNP.Research.PlaneCase35SixthSparseBudget.Seed

open PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35SixthSparseBudget.PlaneFirstAndBudget PEqualNP.Research.PlaneCase35SixthSparseBudget.Seed
open PEqualNP.Research.PlaneCase35SixthSparseBudget.Rows (input mix) in
theorem PEqualNP.Research.PlaneCase35SixthSparseBudget : ∀ (swap : Bool) (extra : List Column) (gs : List Gate) (o : Nat),
    let x := mix true (input 13) (input 26)
    let y := mix true (input 13) (input 27)
    let pre := if swap then [c,d,y,x] else [c,d,x,y]
    let pool := ((initial ++ pre) ++ extra) ++ [fun _ => false, fun _ => true]
    (∀ w ∈ extra, ∀ p : Fin 52, omittedFlags.testBit p.val = false → w p.val = true →
      ∃ u ∈ initial, u p.val = true ∧ ∀ r : Nat, u r = true → w r = true) →
    (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step pool) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro swap extra gs o x y pre pool transfer hp hn
  have inactive : ∀ p : Fin 52, omittedFlags.testBit p.val = false →
      c p.val = false ∧ d p.val = false ∧ x p.val = false ∧ y p.val = false := by
    dsimp only [x,y]
    decide +kernel
  apply separated_bound _ gs o _ hp hn
  let f (i : Fin 257) : Fin 468 := ⟨ix i,neg_match i⟩
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,off,cov⟩ := pairGuard i j lt
  have raw := initial_good p (f i) (f j) cov
  obtain ⟨hc,hd,hx,hy⟩ := inactive p off
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with before | con
  · rcases List.mem_append.mp before with fixed | more
    · rcases List.mem_append.mp fixed with original | added
      · exact raw w original
      · cases swap <;> simp only [pre,ite_true,ite_false,Bool.false_eq_true,List.mem_cons,List.not_mem_nil,or_false] at added <;>
          rcases added with rfl | rfl | rfl | rfl <;> simp [good,hc,hd,hx,hy]
    · intro hit
      obtain ⟨u,hu,on,sub⟩ := transfer w more p off hit
      exact (raw u hu on).elim (fun h => Or.inl (sub _ h)) (fun h => Or.inr (sub _ h))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at con
    rcases con with rfl | rfl <;> simp [good]
