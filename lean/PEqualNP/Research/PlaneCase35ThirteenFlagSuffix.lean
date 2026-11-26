import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndSeparation

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

end PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndSeparation


namespace PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndBudget
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
    (K : Finset (Fin 468)) (hk : 257 ≤ K.card)
    (sep : ∀ i j : K, i.val < j.val → ∃ p : Fin 52,
      ∀ w ∈ s, good p.val (52+i.val.val) (52+j.val.val) w)
    (hp : ∀ p : Fin 52, wire (gs.foldl step s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl step s) o (52 + n.val) = false) :
    9 ≤ gs.countP Prod.fst := by
  let f (i : K) : Fin (2 ^ (gs.countP Prod.fst)) :=
    ⟨trace s (52 + i.val.val) gs,trace_lt _ _ _⟩
  have distinct (i j : K) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,hp0⟩ := sep i j lt
    have remain := preserve gs s _ _ _ hp0 (congrArg Fin.val eq)
    have bad := (readGood remain o) (hp p)
    simp [hn] at bad
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with lt | gt
    · exact distinct i j lt eq
    · exact distinct j i gt eq.symm
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin,Fintype.card_coe] at card
  by_contra h
  have le : gs.countP Prod.fst ≤ 8 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP Prod.fst ≤ 256 at bound
  omega
end PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndBudget


namespace PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthExceptions.PairShape

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

end PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthExceptions.PairShape
namespace PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthExceptions.PairShape
set_option maxHeartbeats 0
set_option maxRecDepth 14000
private def col (k : Nat) := (0x4210413001a00c000e0000000000000000000000000024301102001c5000d0020400282800800050030001000000140015000010000202880024900000000008400084a800000000000000008c000b2990000000000890014b61000000000000000000000000000018c20000006524ff76feddb7ffd83dc55021fd547d6fa3bb7f6785e882ea5fe40bf6dd6d5001f621bf3176fe901c2000d8442000002d140800006fdd6a4040375240000001bdf8b6f5851fa8bac0d000e8000000defc5b7d8dfef58e01d3f3abb428a1f5400d203ffff6eefec8d27de9ff2d949bd07d460d51407504fffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffe0000000000000000000000003ffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000f800001fffff80000000000000000003fffff00000000000000000007ffffffffffffffffffc000000000000000000000000000000000000000000000001f00007ffffe00000000000003e0000fffffc00000000000007fffc000000000000003fffffffffffff800000000000000000000000000007c00010f000780001fff0000000000000000f80003fffe00000000078003ffff00000000003ffe00000000007fffffffffe00000000000000000803c00000f0007c000000fff800000001e000878003c001ff000000000003e000fff80000003c01fff00000007ffc0000001fffffff0000000000440380088880043801c00e007f80000201c000078003c0000ffc0000070021c00e007f800000001e00ffc00007803ff00001ff80000fffff80000200270040070002700000000707ff001103004444002381c0c03e00040c0003c01e0007f00003811c0c03e0000003c0ffc01e07fe00fe0007fe0002004e0000004210c13001e04c700f00802e02003800260000031fe024301122011c7060f8020400383801f00070230c038000781f8e1fe0781f800000000440e0000008e09180b4f0cf00809c0000021119303c2dc1e102e080180120000c7c123092427398f840800c38060184610401c1e679860020298202492100302980840008ca880000002207000008ca30b3998209800008894c1cb63882c40204800c724612a2735d04018c2193110677511100440202490048c006053002421640105210124908042a108025500000090600023522db410a00092646b69058810481a93254b7840cc9546f00890120000000822a055402a282905c448090101248052010a409228085440954408a89016c000091001352d821400926b6429022952aabc8adb00000000000000000000000000000000000000000000000000000000000037fe7fedffff383c00000000000003f7ff3c7f9fe7b9efbfe3e19867900000000000006ffce000f7bfff7357400000000000000000000000000000000000000000000001bfdfb7ff3880000000000fbfe73de6ceef988a06c3fba00000000001ff90007fdbde980000000000037fa00ef7fdaa80000000000000000000000000000000000037efb7e400000007bf336ab90b8347ec0077f8000000001fd007d6fa01a3f60000000001fe003f6dd0000000001bf0076fe90000000000000000000000000006fdd6000003752400000000000000000000000000000002e1cff003bfc0000003fc1fff873fc00000007f80fffc0000003fc1fff80000000000000000001fff801ff00000017707fb8073e0ff000000ff0fc00000000000000000000000058cfc01df000001f07fc3be000003e0ff8000003fc7e00000000000007e0703fc0fe000007bc0fe31f0e78000030c00000bb83fdc0660f00003e180000000000000000002c4e01b0000707877c000039e00000fb0000000079dddd8060fd86800000c67e1b838000740fc1f000003dc1e331cc000600002ec1f602838001c40000000000000589c05000221b800050000e80002e82fb1af0bd105eb32000604b080d00b76d0107ec340000c5c34200083c1c0000ee18c8d00080016c34082001000000000016480a001a001002007f42d65db0b0d83dc550200054302103a1762785e882ea40040900406d5001f62000316208001c2000d8442000002d1408000000000a40401000000000000000000000000000000000001fe3aded8586c3fb510034c2278f65e2f9176802140436d01fd001b908038400d84a0005a30800000688800000001bdf8b6f5851fa8bac0d000e800000000000000000000000003f3abb428a1f5400d203c74e2e2d808406da03e001400c0014001510001000000000000000000000000000000000000000defc5b7d8dfef58e01d00000000000000000001fbff46c7ec0d278e9cf2d849bd07c060c01407404 >>> (468*k)) &&& 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
private def key (k : Nat) := (0x6332c4232810b2206b206330c5af0b39f070eb015aeeb52aea31ae606ae0632cc52aca4eec9296c55aeab4eea9422a8212a452a8a4228839e871ee834ee6939e6731a6610a624224831a46296450ea4139e272962521224eea206320c31a06212041ee035adeb295e5e6de3109e2529ca211c4109c20e9c14eda91eda30e9a1069a0 >>> (5*k)) &&& 0x1f
private def removed : Nat := 0x8cdbea1003008431e56b2019113d1b022c2d399ab8c4ea1d5dd4ddb0156860cd224572e197450204d415ab5e092df2cf53c633f41a6d7b7aaf50
private def full := (2:Nat)^468-1
private def side (i k : Nat) := if (col k).testBit i then full else col k
private def cov (i p : Nat) := side i (key (4*p)) &&& side i (key (4*p+1)) &&&
  side i (key (4*p+2)) &&& side i (key (4*p+3))
private def contribution (i p : Nat) :=
  if (0x402004182ef : Nat).testBit p then 0 else cov i p
private def cover (i : Nat) := (List.range 52).foldr (fun p b => contribution i p ||| b) 0
private theorem bitMember (i j : Nat) (ws : List Nat)
    (h : (ws.foldr (fun p b => contribution i p ||| b) 0).testBit j = true) :
    ∃ p ∈ ws, (contribution i p).testBit j = true := by
  induction ws with
  | nil => simp at h
  | cons p ps ih =>
    rw [List.foldr_cons,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨p,by simp,h⟩
    · obtain ⟨p,hp,yes⟩ := ih h
      exact ⟨p,List.mem_cons_of_mem _ hp,yes⟩

private theorem keys : ∀ (p : Fin 52) (k : Fin 30), base k p.val = true →
    k.val = key (4*p.val) ∨ k.val = key (4*p.val+1) ∨
      k.val = key (4*p.val+2) ∨ k.val = key (4*p.val+3) := by decide +kernel
private def nw (i : Nat) : Nat := (0x2e4008c0b8800382e100860b8042282e0008e0b2804282c881120b2040680c809180b2004686c420940b1042600c4081c0b1002702c30106030824302c2010e0b0606086c121840b0406186c0a1900b0242482c081920300a4506c021940b0042680c0091c0ee0008a3b200068ac400981b020248ec0009a3aa000a86a100a22a8102a0ea000aa1a6000c8e9102227a420848e9002323a2000e9a8482902a110a20a8402987a060a08a8142a03a040a89e8082922a010aa2e62004a19820308a6040c83980032865808129948210865080520940a140650085229302062e4a080a39202068a4448880910a240a44089829092122e42084a0902834064080d20901a300a4048c80900a342e2a040a18a41088e28042a988a110ae22044a1886120822124a018841288220a4c01882130822060e0288103a022024e0186420882182830186020cae130a02f84a0908a124a40b8482908a114a2038442889e1082520841a180a104a600840a1c0a0e0c080830b040a0c0c18982c300ae0a0c0a0824b0806090c220820b0c0a070e0028192820a060e0868161a00a054a800814b200a050e8008129241a04869028112a202042c90f80e180ae030e02f80a1908a024a4878061a0820168a028052a802012ca00802934020068e0272004609c4001c270804301c02114270004709940214264408901902034264008d09884128062084c0988013826180830984021c260c0c10982430826080c30981432006048490981032426010ca0180213415c00114d64000d25880130d60404935800134554001515420144150205415400154d4c001915220444d48410935200464d44001d25090520142214425080530540c14105028540540815135010524140215414c40094530406104c08190530006534b01024529042134a100a4d28042924981030525040534901034122244424881130121242414841094d20406904809190d15020574520844d14021534450884d11022574430905d10825134410984110207414321044d0c0419142614045094121042494805090521042294405088511342104a41082530241c1810906060c74161804d050605741218459038700040c94109030704640b0d00102a540640a1d00902434804089511d01c30174061c04d01432104049491d00c341040295408e4008cb38800384e100863380023acca010a13220448cc8011a031082508c4009c930c041acc2010e130606080c12184130406180c0a190130206480c0219412e0408a4b2100612c400980b0302412c0409acaa100a22a140a0ca8102a229840308a450880290c2108a4108cb28840380a120a4128402980a070a0228142a00a030a4126240480983030126040c8896120462524840094301422504852c930206f24a480ac92120632440899c9092120240c0d248a910222294422c8a110a0222c44048891120221c48088851280220c4c0886520822184831884d2800212c241884929022114a200843094f20e0c0ac830306620b4c03c82930222094c21881c38072060e0808161a022050e8008121a40203c601880d3800202c64008071a091c80118471000711c2010c470004711940214c64408931900236c62004e1186020c46100871183030446080c33181032445c08111164200c45880131160204c45508050150a0504540815914c201805228449148211845108071142014c050285431312024c4c0819912c240884a4908b128242844981031125240444909031122044cc48490911152204045288411142214c4448890110a2500432904910c241804269402109252004229441107060444181830105a60044149810104a610040e1c011030704040a1d00101a700439002310e2400c438502110e0408e432904200c8c112432104610c4009c430d04110c2410c030706010c14184030306420b8502042c940130b14024c2c140990aa500ac2a140a10a6100c429042310a2500cc2850290098d010826140c10961204025248410941214424d0810092d2004249481309142240243484008ad10242294420088d110421848300849290020f0c010834304020b4c00081c38041c90111071600401c38101070604441948211064208c41890130061e08041858210060e0c08170a0420596800016380420586810c154a0130542815c14d20170524844c145a010050e052c130a06604b4903c1292420049e1008125a400048e110c114a217043490401078602039602000e3c002038702000cb41010325044c0c58090030f04240b8502002cb40240b0d02002ad40240a95020029e40080a59080028f40040985030025a48040949210024b480008b5100021e4800072c04201c38108065a080018f011c05c28170161a04c054a810014b211c04d2810012d243c038702000cb410002f140600b4d00002b5400009e501c01c3810005a680000f1c0 >>> (30*i)) &&& 0x3fffffff
private def transposeAt (i : Nat) : Prop := ∀ k : Fin 30, (col k.val).testBit i = (nw i).testBit k.val
private theorem transpose0 : ∀ t : Fin 12, transposeAt (t.val+0) := by unfold transposeAt; decide +kernel
private theorem transpose1 : ∀ t : Fin 12, transposeAt (t.val+12) := by unfold transposeAt; decide +kernel
private theorem transpose2 : ∀ t : Fin 12, transposeAt (t.val+24) := by unfold transposeAt; decide +kernel
private theorem transpose3 : ∀ t : Fin 12, transposeAt (t.val+36) := by unfold transposeAt; decide +kernel
private theorem transpose4 : ∀ t : Fin 12, transposeAt (t.val+48) := by unfold transposeAt; decide +kernel
private theorem transpose5 : ∀ t : Fin 12, transposeAt (t.val+60) := by unfold transposeAt; decide +kernel
private theorem transpose6 : ∀ t : Fin 12, transposeAt (t.val+72) := by unfold transposeAt; decide +kernel
private theorem transpose7 : ∀ t : Fin 12, transposeAt (t.val+84) := by unfold transposeAt; decide +kernel
private theorem transpose8 : ∀ t : Fin 12, transposeAt (t.val+96) := by unfold transposeAt; decide +kernel
private theorem transpose9 : ∀ t : Fin 12, transposeAt (t.val+108) := by unfold transposeAt; decide +kernel
private theorem transpose10 : ∀ t : Fin 12, transposeAt (t.val+120) := by unfold transposeAt; decide +kernel
private theorem transpose11 : ∀ t : Fin 12, transposeAt (t.val+132) := by unfold transposeAt; decide +kernel
private theorem transpose12 : ∀ t : Fin 12, transposeAt (t.val+144) := by unfold transposeAt; decide +kernel
private theorem transpose13 : ∀ t : Fin 12, transposeAt (t.val+156) := by unfold transposeAt; decide +kernel
private theorem transpose14 : ∀ t : Fin 12, transposeAt (t.val+168) := by unfold transposeAt; decide +kernel
private theorem transpose15 : ∀ t : Fin 12, transposeAt (t.val+180) := by unfold transposeAt; decide +kernel
private theorem transpose16 : ∀ t : Fin 12, transposeAt (t.val+192) := by unfold transposeAt; decide +kernel
private theorem transpose17 : ∀ t : Fin 12, transposeAt (t.val+204) := by unfold transposeAt; decide +kernel
private theorem transpose18 : ∀ t : Fin 12, transposeAt (t.val+216) := by unfold transposeAt; decide +kernel
private theorem transpose19 : ∀ t : Fin 12, transposeAt (t.val+228) := by unfold transposeAt; decide +kernel
private theorem transpose20 : ∀ t : Fin 12, transposeAt (t.val+240) := by unfold transposeAt; decide +kernel
private theorem transpose21 : ∀ t : Fin 12, transposeAt (t.val+252) := by unfold transposeAt; decide +kernel
private theorem transpose22 : ∀ t : Fin 12, transposeAt (t.val+264) := by unfold transposeAt; decide +kernel
private theorem transpose23 : ∀ t : Fin 12, transposeAt (t.val+276) := by unfold transposeAt; decide +kernel
private theorem transpose24 : ∀ t : Fin 12, transposeAt (t.val+288) := by unfold transposeAt; decide +kernel
private theorem transpose25 : ∀ t : Fin 12, transposeAt (t.val+300) := by unfold transposeAt; decide +kernel
private theorem transpose26 : ∀ t : Fin 12, transposeAt (t.val+312) := by unfold transposeAt; decide +kernel
private theorem transpose27 : ∀ t : Fin 12, transposeAt (t.val+324) := by unfold transposeAt; decide +kernel
private theorem transpose28 : ∀ t : Fin 12, transposeAt (t.val+336) := by unfold transposeAt; decide +kernel
private theorem transpose29 : ∀ t : Fin 12, transposeAt (t.val+348) := by unfold transposeAt; decide +kernel
private theorem transpose30 : ∀ t : Fin 12, transposeAt (t.val+360) := by unfold transposeAt; decide +kernel
private theorem transpose31 : ∀ t : Fin 12, transposeAt (t.val+372) := by unfold transposeAt; decide +kernel
private theorem transpose32 : ∀ t : Fin 12, transposeAt (t.val+384) := by unfold transposeAt; decide +kernel
private theorem transpose33 : ∀ t : Fin 12, transposeAt (t.val+396) := by unfold transposeAt; decide +kernel
private theorem transpose34 : ∀ t : Fin 12, transposeAt (t.val+408) := by unfold transposeAt; decide +kernel
private theorem transpose35 : ∀ t : Fin 12, transposeAt (t.val+420) := by unfold transposeAt; decide +kernel
private theorem transpose36 : ∀ t : Fin 12, transposeAt (t.val+432) := by unfold transposeAt; decide +kernel
private theorem transpose37 : ∀ t : Fin 12, transposeAt (t.val+444) := by unfold transposeAt; decide +kernel
private theorem transpose38 : ∀ t : Fin 12, transposeAt (t.val+456) := by unfold transposeAt; decide +kernel
private theorem transpose (i : Fin 468) : transposeAt i.val := by
  have per (q : Fin 39) (t : Fin 12) : transposeAt (t.val + 12*q.val) := by
    match q with
    | ⟨0,_⟩ => exact transpose0 t
    | ⟨1,_⟩ => exact transpose1 t
    | ⟨2,_⟩ => exact transpose2 t
    | ⟨3,_⟩ => exact transpose3 t
    | ⟨4,_⟩ => exact transpose4 t
    | ⟨5,_⟩ => exact transpose5 t
    | ⟨6,_⟩ => exact transpose6 t
    | ⟨7,_⟩ => exact transpose7 t
    | ⟨8,_⟩ => exact transpose8 t
    | ⟨9,_⟩ => exact transpose9 t
    | ⟨10,_⟩ => exact transpose10 t
    | ⟨11,_⟩ => exact transpose11 t
    | ⟨12,_⟩ => exact transpose12 t
    | ⟨13,_⟩ => exact transpose13 t
    | ⟨14,_⟩ => exact transpose14 t
    | ⟨15,_⟩ => exact transpose15 t
    | ⟨16,_⟩ => exact transpose16 t
    | ⟨17,_⟩ => exact transpose17 t
    | ⟨18,_⟩ => exact transpose18 t
    | ⟨19,_⟩ => exact transpose19 t
    | ⟨20,_⟩ => exact transpose20 t
    | ⟨21,_⟩ => exact transpose21 t
    | ⟨22,_⟩ => exact transpose22 t
    | ⟨23,_⟩ => exact transpose23 t
    | ⟨24,_⟩ => exact transpose24 t
    | ⟨25,_⟩ => exact transpose25 t
    | ⟨26,_⟩ => exact transpose26 t
    | ⟨27,_⟩ => exact transpose27 t
    | ⟨28,_⟩ => exact transpose28 t
    | ⟨29,_⟩ => exact transpose29 t
    | ⟨30,_⟩ => exact transpose30 t
    | ⟨31,_⟩ => exact transpose31 t
    | ⟨32,_⟩ => exact transpose32 t
    | ⟨33,_⟩ => exact transpose33 t
    | ⟨34,_⟩ => exact transpose34 t
    | ⟨35,_⟩ => exact transpose35 t
    | ⟨36,_⟩ => exact transpose36 t
    | ⟨37,_⟩ => exact transpose37 t
    | ⟨38,_⟩ => exact transpose38 t
    | ⟨v+39,h⟩ => omega
  have h := per ⟨i.val/12,by omega⟩ ⟨i.val%12,by omega⟩
  simpa only [Nat.mod_add_div] using h
private def sourceAt (i : Nat) : Prop := (nw i) % 2^28 = neg i ∧ (nw i).testBit 28 = ((neg i).testBit 15 && (neg i).testBit 27) ∧ (nw i).testBit 29 = ((neg i).testBit 17 && (neg i).testBit 26)
private theorem source0 : ∀ t : Fin 12, sourceAt (t.val+0) := by unfold sourceAt; decide +kernel
private theorem source1 : ∀ t : Fin 12, sourceAt (t.val+12) := by unfold sourceAt; decide +kernel
private theorem source2 : ∀ t : Fin 12, sourceAt (t.val+24) := by unfold sourceAt; decide +kernel
private theorem source3 : ∀ t : Fin 12, sourceAt (t.val+36) := by unfold sourceAt; decide +kernel
private theorem source4 : ∀ t : Fin 12, sourceAt (t.val+48) := by unfold sourceAt; decide +kernel
private theorem source5 : ∀ t : Fin 12, sourceAt (t.val+60) := by unfold sourceAt; decide +kernel
private theorem source6 : ∀ t : Fin 12, sourceAt (t.val+72) := by unfold sourceAt; decide +kernel
private theorem source7 : ∀ t : Fin 12, sourceAt (t.val+84) := by unfold sourceAt; decide +kernel
private theorem source8 : ∀ t : Fin 12, sourceAt (t.val+96) := by unfold sourceAt; decide +kernel
private theorem source9 : ∀ t : Fin 12, sourceAt (t.val+108) := by unfold sourceAt; decide +kernel
private theorem source10 : ∀ t : Fin 12, sourceAt (t.val+120) := by unfold sourceAt; decide +kernel
private theorem source11 : ∀ t : Fin 12, sourceAt (t.val+132) := by unfold sourceAt; decide +kernel
private theorem source12 : ∀ t : Fin 12, sourceAt (t.val+144) := by unfold sourceAt; decide +kernel
private theorem source13 : ∀ t : Fin 12, sourceAt (t.val+156) := by unfold sourceAt; decide +kernel
private theorem source14 : ∀ t : Fin 12, sourceAt (t.val+168) := by unfold sourceAt; decide +kernel
private theorem source15 : ∀ t : Fin 12, sourceAt (t.val+180) := by unfold sourceAt; decide +kernel
private theorem source16 : ∀ t : Fin 12, sourceAt (t.val+192) := by unfold sourceAt; decide +kernel
private theorem source17 : ∀ t : Fin 12, sourceAt (t.val+204) := by unfold sourceAt; decide +kernel
private theorem source18 : ∀ t : Fin 12, sourceAt (t.val+216) := by unfold sourceAt; decide +kernel
private theorem source19 : ∀ t : Fin 12, sourceAt (t.val+228) := by unfold sourceAt; decide +kernel
private theorem source20 : ∀ t : Fin 12, sourceAt (t.val+240) := by unfold sourceAt; decide +kernel
private theorem source21 : ∀ t : Fin 12, sourceAt (t.val+252) := by unfold sourceAt; decide +kernel
private theorem source22 : ∀ t : Fin 12, sourceAt (t.val+264) := by unfold sourceAt; decide +kernel
private theorem source23 : ∀ t : Fin 12, sourceAt (t.val+276) := by unfold sourceAt; decide +kernel
private theorem source24 : ∀ t : Fin 12, sourceAt (t.val+288) := by unfold sourceAt; decide +kernel
private theorem source25 : ∀ t : Fin 12, sourceAt (t.val+300) := by unfold sourceAt; decide +kernel
private theorem source26 : ∀ t : Fin 12, sourceAt (t.val+312) := by unfold sourceAt; decide +kernel
private theorem source27 : ∀ t : Fin 12, sourceAt (t.val+324) := by unfold sourceAt; decide +kernel
private theorem source28 : ∀ t : Fin 12, sourceAt (t.val+336) := by unfold sourceAt; decide +kernel
private theorem source29 : ∀ t : Fin 12, sourceAt (t.val+348) := by unfold sourceAt; decide +kernel
private theorem source30 : ∀ t : Fin 12, sourceAt (t.val+360) := by unfold sourceAt; decide +kernel
private theorem source31 : ∀ t : Fin 12, sourceAt (t.val+372) := by unfold sourceAt; decide +kernel
private theorem source32 : ∀ t : Fin 12, sourceAt (t.val+384) := by unfold sourceAt; decide +kernel
private theorem source33 : ∀ t : Fin 12, sourceAt (t.val+396) := by unfold sourceAt; decide +kernel
private theorem source34 : ∀ t : Fin 12, sourceAt (t.val+408) := by unfold sourceAt; decide +kernel
private theorem source35 : ∀ t : Fin 12, sourceAt (t.val+420) := by unfold sourceAt; decide +kernel
private theorem source36 : ∀ t : Fin 12, sourceAt (t.val+432) := by unfold sourceAt; decide +kernel
private theorem source37 : ∀ t : Fin 12, sourceAt (t.val+444) := by unfold sourceAt; decide +kernel
private theorem source38 : ∀ t : Fin 12, sourceAt (t.val+456) := by unfold sourceAt; decide +kernel
private theorem source (i : Fin 468) : sourceAt i.val := by
  have per (q : Fin 39) (t : Fin 12) : sourceAt (t.val + 12*q.val) := by
    match q with
    | ⟨0,_⟩ => exact source0 t
    | ⟨1,_⟩ => exact source1 t
    | ⟨2,_⟩ => exact source2 t
    | ⟨3,_⟩ => exact source3 t
    | ⟨4,_⟩ => exact source4 t
    | ⟨5,_⟩ => exact source5 t
    | ⟨6,_⟩ => exact source6 t
    | ⟨7,_⟩ => exact source7 t
    | ⟨8,_⟩ => exact source8 t
    | ⟨9,_⟩ => exact source9 t
    | ⟨10,_⟩ => exact source10 t
    | ⟨11,_⟩ => exact source11 t
    | ⟨12,_⟩ => exact source12 t
    | ⟨13,_⟩ => exact source13 t
    | ⟨14,_⟩ => exact source14 t
    | ⟨15,_⟩ => exact source15 t
    | ⟨16,_⟩ => exact source16 t
    | ⟨17,_⟩ => exact source17 t
    | ⟨18,_⟩ => exact source18 t
    | ⟨19,_⟩ => exact source19 t
    | ⟨20,_⟩ => exact source20 t
    | ⟨21,_⟩ => exact source21 t
    | ⟨22,_⟩ => exact source22 t
    | ⟨23,_⟩ => exact source23 t
    | ⟨24,_⟩ => exact source24 t
    | ⟨25,_⟩ => exact source25 t
    | ⟨26,_⟩ => exact source26 t
    | ⟨27,_⟩ => exact source27 t
    | ⟨28,_⟩ => exact source28 t
    | ⟨29,_⟩ => exact source29 t
    | ⟨30,_⟩ => exact source30 t
    | ⟨31,_⟩ => exact source31 t
    | ⟨32,_⟩ => exact source32 t
    | ⟨33,_⟩ => exact source33 t
    | ⟨34,_⟩ => exact source34 t
    | ⟨35,_⟩ => exact source35 t
    | ⟨36,_⟩ => exact source36 t
    | ⟨37,_⟩ => exact source37 t
    | ⟨38,_⟩ => exact source38 t
    | ⟨v+39,h⟩ => omega
  have h := per ⟨i.val/12,by omega⟩ ⟨i.val%12,by omega⟩
  simpa only [Nat.mod_add_div] using h
private theorem colOK (k : Fin 30) (j : Fin 468) : (col k.val).testBit j.val = base k (52+j.val) := by
  rw [transpose j k]
  obtain ⟨raw,hc,hd⟩ := source j
  have no : ¬52+j.val < 52 := by omega
  by_cases low : k.val < 28
  · have e := congrArg (fun x : Nat => x.testBit k.val) raw
    change ((nw j.val) % (2^28)).testBit k.val = _ at e
    rw [Nat.testBit_mod_two_pow] at e
    simpa [low,base,input,no] using e
  · by_cases middle : k.val = 28
    · simpa [base,low,middle,mix,input,no] using hc
    · have last : k.val = 29 := by omega
      simpa [base,low,middle,last,mix,input,no] using hd
private def rowOKAt (i : Nat) : Prop := removed.testBit i = false → (cover i ||| removed ||| (1 <<< i)) = full
private theorem rowOK0 : ∀ t : Fin 12, rowOKAt (t.val+0) := by unfold rowOKAt; decide +kernel
private theorem rowOK1 : ∀ t : Fin 12, rowOKAt (t.val+12) := by unfold rowOKAt; decide +kernel
private theorem rowOK2 : ∀ t : Fin 12, rowOKAt (t.val+24) := by unfold rowOKAt; decide +kernel
private theorem rowOK3 : ∀ t : Fin 12, rowOKAt (t.val+36) := by unfold rowOKAt; decide +kernel
private theorem rowOK4 : ∀ t : Fin 12, rowOKAt (t.val+48) := by unfold rowOKAt; decide +kernel
private theorem rowOK5 : ∀ t : Fin 12, rowOKAt (t.val+60) := by unfold rowOKAt; decide +kernel
private theorem rowOK6 : ∀ t : Fin 12, rowOKAt (t.val+72) := by unfold rowOKAt; decide +kernel
private theorem rowOK7 : ∀ t : Fin 12, rowOKAt (t.val+84) := by unfold rowOKAt; decide +kernel
private theorem rowOK8 : ∀ t : Fin 12, rowOKAt (t.val+96) := by unfold rowOKAt; decide +kernel
private theorem rowOK9 : ∀ t : Fin 12, rowOKAt (t.val+108) := by unfold rowOKAt; decide +kernel
private theorem rowOK10 : ∀ t : Fin 12, rowOKAt (t.val+120) := by unfold rowOKAt; decide +kernel
private theorem rowOK11 : ∀ t : Fin 12, rowOKAt (t.val+132) := by unfold rowOKAt; decide +kernel
private theorem rowOK12 : ∀ t : Fin 12, rowOKAt (t.val+144) := by unfold rowOKAt; decide +kernel
private theorem rowOK13 : ∀ t : Fin 12, rowOKAt (t.val+156) := by unfold rowOKAt; decide +kernel
private theorem rowOK14 : ∀ t : Fin 12, rowOKAt (t.val+168) := by unfold rowOKAt; decide +kernel
private theorem rowOK15 : ∀ t : Fin 12, rowOKAt (t.val+180) := by unfold rowOKAt; decide +kernel
private theorem rowOK16 : ∀ t : Fin 12, rowOKAt (t.val+192) := by unfold rowOKAt; decide +kernel
private theorem rowOK17 : ∀ t : Fin 12, rowOKAt (t.val+204) := by unfold rowOKAt; decide +kernel
private theorem rowOK18 : ∀ t : Fin 12, rowOKAt (t.val+216) := by unfold rowOKAt; decide +kernel
private theorem rowOK19 : ∀ t : Fin 12, rowOKAt (t.val+228) := by unfold rowOKAt; decide +kernel
private theorem rowOK20 : ∀ t : Fin 12, rowOKAt (t.val+240) := by unfold rowOKAt; decide +kernel
private theorem rowOK21 : ∀ t : Fin 12, rowOKAt (t.val+252) := by unfold rowOKAt; decide +kernel
private theorem rowOK22 : ∀ t : Fin 12, rowOKAt (t.val+264) := by unfold rowOKAt; decide +kernel
private theorem rowOK23 : ∀ t : Fin 12, rowOKAt (t.val+276) := by unfold rowOKAt; decide +kernel
private theorem rowOK24 : ∀ t : Fin 12, rowOKAt (t.val+288) := by unfold rowOKAt; decide +kernel
private theorem rowOK25 : ∀ t : Fin 12, rowOKAt (t.val+300) := by unfold rowOKAt; decide +kernel
private theorem rowOK26 : ∀ t : Fin 12, rowOKAt (t.val+312) := by unfold rowOKAt; decide +kernel
private theorem rowOK27 : ∀ t : Fin 12, rowOKAt (t.val+324) := by unfold rowOKAt; decide +kernel
private theorem rowOK28 : ∀ t : Fin 12, rowOKAt (t.val+336) := by unfold rowOKAt; decide +kernel
private theorem rowOK29 : ∀ t : Fin 12, rowOKAt (t.val+348) := by unfold rowOKAt; decide +kernel
private theorem rowOK30 : ∀ t : Fin 12, rowOKAt (t.val+360) := by unfold rowOKAt; decide +kernel
private theorem rowOK31 : ∀ t : Fin 12, rowOKAt (t.val+372) := by unfold rowOKAt; decide +kernel
private theorem rowOK32 : ∀ t : Fin 12, rowOKAt (t.val+384) := by unfold rowOKAt; decide +kernel
private theorem rowOK33 : ∀ t : Fin 12, rowOKAt (t.val+396) := by unfold rowOKAt; decide +kernel
private theorem rowOK34 : ∀ t : Fin 12, rowOKAt (t.val+408) := by unfold rowOKAt; decide +kernel
private theorem rowOK35 : ∀ t : Fin 12, rowOKAt (t.val+420) := by unfold rowOKAt; decide +kernel
private theorem rowOK36 : ∀ t : Fin 12, rowOKAt (t.val+432) := by unfold rowOKAt; decide +kernel
private theorem rowOK37 : ∀ t : Fin 12, rowOKAt (t.val+444) := by unfold rowOKAt; decide +kernel
private theorem rowOK38 : ∀ t : Fin 12, rowOKAt (t.val+456) := by unfold rowOKAt; decide +kernel
private theorem rowOK (i : Fin 468) : rowOKAt i.val := by
  have per (q : Fin 39) (t : Fin 12) : rowOKAt (t.val + 12*q.val) := by
    match q with
    | ⟨0,_⟩ => exact rowOK0 t
    | ⟨1,_⟩ => exact rowOK1 t
    | ⟨2,_⟩ => exact rowOK2 t
    | ⟨3,_⟩ => exact rowOK3 t
    | ⟨4,_⟩ => exact rowOK4 t
    | ⟨5,_⟩ => exact rowOK5 t
    | ⟨6,_⟩ => exact rowOK6 t
    | ⟨7,_⟩ => exact rowOK7 t
    | ⟨8,_⟩ => exact rowOK8 t
    | ⟨9,_⟩ => exact rowOK9 t
    | ⟨10,_⟩ => exact rowOK10 t
    | ⟨11,_⟩ => exact rowOK11 t
    | ⟨12,_⟩ => exact rowOK12 t
    | ⟨13,_⟩ => exact rowOK13 t
    | ⟨14,_⟩ => exact rowOK14 t
    | ⟨15,_⟩ => exact rowOK15 t
    | ⟨16,_⟩ => exact rowOK16 t
    | ⟨17,_⟩ => exact rowOK17 t
    | ⟨18,_⟩ => exact rowOK18 t
    | ⟨19,_⟩ => exact rowOK19 t
    | ⟨20,_⟩ => exact rowOK20 t
    | ⟨21,_⟩ => exact rowOK21 t
    | ⟨22,_⟩ => exact rowOK22 t
    | ⟨23,_⟩ => exact rowOK23 t
    | ⟨24,_⟩ => exact rowOK24 t
    | ⟨25,_⟩ => exact rowOK25 t
    | ⟨26,_⟩ => exact rowOK26 t
    | ⟨27,_⟩ => exact rowOK27 t
    | ⟨28,_⟩ => exact rowOK28 t
    | ⟨29,_⟩ => exact rowOK29 t
    | ⟨30,_⟩ => exact rowOK30 t
    | ⟨31,_⟩ => exact rowOK31 t
    | ⟨32,_⟩ => exact rowOK32 t
    | ⟨33,_⟩ => exact rowOK33 t
    | ⟨34,_⟩ => exact rowOK34 t
    | ⟨35,_⟩ => exact rowOK35 t
    | ⟨36,_⟩ => exact rowOK36 t
    | ⟨37,_⟩ => exact rowOK37 t
    | ⟨38,_⟩ => exact rowOK38 t
    | ⟨v+39,h⟩ => omega
  have h := per ⟨i.val/12,by omega⟩ ⟨i.val%12,by omega⟩
  simpa only [Nat.mod_add_div] using h
private def indexed (w : Nat) : Finset (Fin 468) := Finset.univ.filter fun j => w.testBit j.val = true
private theorem ecard : (indexed removed).card = 211 := by decide +kernel
private theorem sound (i j : Fin 468) (lt : i < j)
    (ei : i ∉ indexed removed) (ej : j ∉ indexed removed) : ∃ p : Fin 52, (0x402004182ef : Nat).testBit p.val = false ∧
    ∀ k : Fin 30, base k p.val = true → base k (52+i.val) = true ∨ base k (52+j.val) = true := by
  have off (n : Fin 468) (h : n ∉ indexed removed) : removed.testBit n.val = false := by
    cases eq : removed.testBit n.val <;> simp_all [indexed]
  have eq := congrArg (fun w : Nat => w.testBit j.val) (rowOK i (off i ei))
  have one : (1 <<< i.val : Nat).testBit j.val = false := by
    rw [Nat.one_shiftLeft,Nat.testBit_two_pow]; simp [show i.val ≠ j.val by omega]
  have bit : full.testBit j.val = true := by
    rw [full,Nat.testBit_two_pow_sub_one]; simp [j.isLt]
  simp only [Nat.testBit_or,off j ej,one,Bool.or_false,bit] at eq
  obtain ⟨q,hq,on⟩ := bitMember _ _ (List.range 52) eq
  let p : Fin 52 := ⟨q,List.mem_range.mp hq⟩
  have clear : (0x402004182ef : Nat).testBit q = false := by
    cases e : (0x402004182ef : Nat).testBit q <;> simp_all [contribution]
  refine ⟨p,clear,?_⟩
  intro k hk
  have h : (cov i.val q).testBit j.val = true := by simpa [contribution,clear] using on
  simp only [cov,Nat.testBit_and,Bool.and_eq_true] at h
  have sideGood (t : Nat) (ht : (side i.val t).testBit j.val = true) :
      (col t).testBit i.val = true ∨ (col t).testBit j.val = true := by
    cases hit : (col t).testBit i.val
    · right; simpa [side,hit] using ht
    · exact Or.inl rfl
  have ok : (col k.val).testBit i.val = true ∨ (col k.val).testBit j.val = true := by
    rcases keys p k hk with e | e | e | e
    · exact e ▸ sideGood _ h.1.1.1
    · exact e ▸ sideGood _ h.1.1.2
    · exact e ▸ sideGood _ h.1.2
    · exact e ▸ sideGood _ h.2
  simpa only [colOK k i,colOK k j] using ok
end PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthCharge PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneCase35SixthExceptions.PairShape PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35ThirteenFlagSuffix.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneCase35ThirteenFlagSuffix : ∀ (pool : List (Nat → Bool)),
    (∀ w ∈ pool, ∀ p : Fin 52, (0x402004182ef : Nat).testBit p.val = false → w p.val = true →
      ∃ k : Fin 30, base k p.val = true ∧
        ∀ j : Fin 468, base k (52+j.val) = true → w (52+j.val) = true) →
    ∀ (gs : List Gate) (o : Nat),
      (∀ p : Fin 52, wire (gs.foldl step pool) o p.val = true) →
      (∀ j : Fin 468, wire (gs.foldl step pool) o (52+j.val) = false) →
      9 ≤ gs.countP Prod.fst := by
  intro pool dom gs o hp hn
  let K := Finset.univ \ indexed removed
  have size : 257 ≤ K.card := by
    dsimp only [K]; rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [ecard]
  apply separated_bound pool gs o K size _ hp hn
  intro i j lt
  obtain ⟨p,clear,h⟩ := sound i.val j.val lt (Finset.mem_sdiff.mp i.property).2 (Finset.mem_sdiff.mp j.property).2
  refine ⟨p,?_⟩
  intro w hw hit
  obtain ⟨k,on,lift⟩ := dom w hw p clear hit
  exact (h k on).imp (lift i.val) (lift j.val)
