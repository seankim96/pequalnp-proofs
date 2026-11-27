import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndSeparation

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

end PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndSeparation


namespace PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndBudget
open PlaneFirstAndSeparation
abbrev Gate := Bool × Nat × Nat × Option Nat
variable (guards : Nat → Column)
def step (s : List Column) (g : Gate) : List Column :=
  let x := wire s g.2.1
  let y := wire s g.2.2.1
  s ++ [fun v => (if g.1 then x v && y v else x v || y v) &&
    (g.2.2.2.elim true (fun k => guards k v))]

private def trace (s : List Column) (r : Nat) : List Gate → Nat
  | [] => 0
  | g :: gs =>
    let tail := trace (step guards s g) r gs
    if g.1 then 2 * tail + (wire s g.2.1 r).toNat else tail

private theorem trace_lt (s : List Column) (r : Nat) (gs : List Gate) :
    trace guards s r gs < 2 ^ (gs.countP Prod.fst) := by
  induction gs generalizing s with
  | nil => simp [trace]
  | cons g gs ih =>
    have h := ih (step guards s g)
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
    (strong : ∀ k, guards k p = true → guards k a = true ∧ guards k b = true)
    (h : ∀ w ∈ s, good p a b w) (eq : trace guards s a gs = trace guards s b gs) :
    ∀ w ∈ gs.foldl (step guards) s, good p a b w := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace guards (step guards s g) a gs = trace guards (step guards s g) b gs := by
      cases op : g.1 <;> simp [trace,op] at eq <;>
        cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all <;> omega
    apply ih _ _ tail
    intro w hw
    have l := readGood h g.2.1
    have r := readGood h g.2.2.1
    rcases List.mem_append.mp hw with old | last
    · exact h _ old
    obtain rfl := List.mem_singleton.mp last
    intro hit
    obtain ⟨lit,mask⟩ := Bool.and_eq_true_iff.mp hit
    have safe : (g.2.2.2.elim true (fun k => guards k a)) = true ∧
                (g.2.2.2.elim true (fun k => guards k b)) = true := by
      cases mode : g.2.2.2 with
      | none => simp
      | some k => exact strong k (by simpa [mode] using mask)
    simp only [safe.1,safe.2,Bool.and_true]
    cases op : g.1
    · simp [op] at lit ⊢
      rcases lit with left | right
      · rcases l left with v | v <;> tauto
      · rcases r right with v | v <;> tauto
    · have same : wire s g.2.1 a = wire s g.2.1 b := by
        simp [trace,op,tail] at eq
        cases x : wire s g.2.1 a <;> cases y : wire s g.2.1 b <;> simp_all
      simp [op] at lit ⊢
      obtain ⟨lp,rp⟩ := lit
      have la := l lp
      have ra := r rp
      rw [same] at la ⊢
      tauto

theorem separated_bound (s : List Column) (gs : List Gate) (o : Nat)
    (K : Finset (Fin 468)) (hk : 257 ≤ K.card)
    (sep : ∀ i j : K, i.val < j.val → ∃ p : Fin 52,
      (∀ k, guards k p.val = true → guards k (52+i.val.val) = true ∧ guards k (52+j.val.val) = true) ∧
      ∀ w ∈ s, good p.val (52+i.val.val) (52+j.val.val) w)
    (hp : ∀ p : Fin 52, wire (gs.foldl (step guards) s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl (step guards) s) o (52 + n.val) = false) :
    9 ≤ gs.countP Prod.fst := by
  let f (i : K) : Fin (2 ^ (gs.countP Prod.fst)) :=
    ⟨trace guards s (52 + i.val.val) gs,trace_lt guards _ _ _⟩
  have distinct (i j : K) (lt : i.val < j.val) (eq : f i = f j) : False := by
    obtain ⟨p,strong,hp0⟩ := sep i j lt
    have remain := preserve guards gs s _ _ _ strong hp0 (congrArg Fin.val eq)
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
end PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndBudget


namespace PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthExceptions.PairShape

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

end PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthExceptions.PairShape
namespace PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthExceptions.PairShape
set_option maxHeartbeats 0
set_option maxRecDepth 14000
private def col (k : Nat) := (0x4210413001a00c000e0000000000000000000000000024301102001c5000d0020400282800800050030001000000140015000010000202880024900000000008400084a800000000000000008c000b2990000000000890014b61000000000000000000000000000018c20000006524ff76feddb7ffd83dc55021fd547d6fa3bb7f6785e882ea5fe40bf6dd6d5001f621bf3176fe901c2000d8442000002d140800006fdd6a4040375240000001bdf8b6f5851fa8bac0d000e8000000defc5b7d8dfef58e01d3f3abb428a1f5400d203ffff6eefec8d27de9ff2d949bd07d460d51407504fffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffe0000000000000000000000003ffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000f800001fffff80000000000000000003fffff00000000000000000007ffffffffffffffffffc000000000000000000000000000000000000000000000001f00007ffffe00000000000003e0000fffffc00000000000007fffc000000000000003fffffffffffff800000000000000000000000000007c00010f000780001fff0000000000000000f80003fffe00000000078003ffff00000000003ffe00000000007fffffffffe00000000000000000803c00000f0007c000000fff800000001e000878003c001ff000000000003e000fff80000003c01fff00000007ffc0000001fffffff0000000000440380088880043801c00e007f80000201c000078003c0000ffc0000070021c00e007f800000001e00ffc00007803ff00001ff80000fffff80000200270040070002700000000707ff001103004444002381c0c03e00040c0003c01e0007f00003811c0c03e0000003c0ffc01e07fe00fe0007fe0002004e0000004210c13001e04c700f00802e02003800260000031fe024301122011c7060f8020400383801f00070230c038000781f8e1fe0781f800000000440e0000008e09180b4f0cf00809c0000021119303c2dc1e102e080180120000c7c123092427398f840800c38060184610401c1e679860020298202492100302980840008ca880000002207000008ca30b3998209800008894c1cb63882c40204800c724612a2735d04018c2193110677511100440202490048c006053002421640105210124908042a108025500000090600023522db410a00092646b69058810481a93254b7840cc9546f00890120000000822a055402a282905c448090101248052010a409228085440954408a89016c000091001352d821400926b6429022952aabc8adb00000000000000000000000000000000000000000000000000000000000037fe7fedffff383c00000000000003f7ff3c7f9fe7b9efbfe3e19867900000000000006ffce000f7bfff7357400000000000000000000000000000000000000000000001bfdfb7ff3880000000000fbfe73de6ceef988a06c3fba00000000001ff90007fdbde980000000000037fa00ef7fdaa80000000000000000000000000000000000037efb7e400000007bf336ab90b8347ec0077f8000000001fd007d6fa01a3f60000000001fe003f6dd0000000001bf0076fe90000000000000000000000000006fdd6000003752400000000000000000000000000000002e1cff003bfc0000003fc1fff873fc00000007f80fffc0000003fc1fff80000000000000000001fff801ff00000017707fb8073e0ff000000ff0fc00000000000000000000000058cfc01df000001f07fc3be000003e0ff8000003fc7e00000000000007e0703fc0fe000007bc0fe31f0e78000030c00000bb83fdc0660f00003e180000000000000000002c4e01b0000707877c000039e00000fb0000000079dddd8060fd86800000c67e1b838000740fc1f000003dc1e331cc000600002ec1f602838001c40000000000000589c05000221b800050000e80002e82fb1af0bd105eb32000604b080d00b76d0107ec340000c5c34200083c1c0000ee18c8d00080016c34082001000000000016480a001a001002007f42d65db0b0d83dc550200054302103a1762785e882ea40040900406d5001f62000316208001c2000d8442000002d1408000000000a40401000000000000000000000000000000000001fe3aded8586c3fb510034c2278f65e2f9176802140436d01fd001b908038400d84a0005a30800000688800000001bdf8b6f5851fa8bac0d000e800000000000000000000000003f3abb428a1f5400d203c74e2e2d808406da03e001400c0014001510001000000000000000000000000000000000000000defc5b7d8dfef58e01d00000000000000000001fbff46c7ec0d278e9cf2d849bd07c060c01407404 >>> (468*k)) &&& 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
private def key (k : Nat) := (0x6332c4232810b2206b206330c5af0b39f070eb015aeeb52aea31ae606ae0632cc52aca4eec9296c55aeab4eea9422a8212a452a8a4228839e871ee834ee6939e6731a6610a624224831a46296450ea4139e272962521224eea206320c31a06212041ee035adeb295e5e6de3109e2529ca211c4109c20e9c14eda91eda30e9a1069a0 >>> (5*k)) &&& 0x1f
private def removed : Nat := 0xf6a9e9136f002497296f47122263c862cacd8a37b62ba5aa0af29fb007cda51966c84a4ca1b0129e8830f15b4721720f7b90e375490f0fc840040
private def full := (2:Nat)^468-1
private def side (i k : Nat) := if (col k).testBit i then full else col k
private def cov (i p : Nat) := side i (key (4*p)) &&& side i (key (4*p+1)) &&&
  side i (key (4*p+2)) &&& side i (key (4*p+3))
private def safe (p : Nat) := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f903fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03fc0fe000007bc0fe31f0e78000030dfe3adff87ffc3ff5f0034fe3f8f65e2f917680214043ede1ff001bf0f87fc00d87be005a3fb00000688f9fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (468*p)) &&& full
private def contribution (i p : Nat) :=
  if 4 ≤ p ∧ (safe p).testBit i = true then cov i p &&& safe p else 0
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
    (ei : i ∉ indexed removed) (ej : j ∉ indexed removed) : ∃ p : Fin 52, 4 ≤ p.val ∧ (safe p.val).testBit i.val = true ∧
    (safe p.val).testBit j.val = true ∧
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
  have ok : 4 ≤ q ∧ (safe q).testBit i.val = true := by
    by_contra bad
    simp [contribution,bad] at on
  have both := on
  simp [contribution,ok,Nat.testBit_and] at both
  refine ⟨p,ok.1,ok.2,both.2,?_⟩
  intro k hk
  have h := both.1
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
def fixed (k : Fin 32) : Column :=
  if h : k.val < 30 then base ⟨k.val,h⟩
  else if k.val = 30 then mix true (input 13) (input 26) else mix true (input 13) (input 27)
private def col32 (k : Fin 32) :=
  if h : k.val < 30 then col k.val else col 13 &&& col (if k.val = 30 then 26 else 27)
private theorem phys (k : Fin 32) (j : Fin 468) :
    (col32 k).testBit j.val = fixed k (52+j.val) := by
  by_cases h : k.val < 30
  · simpa only [col32,fixed,h,dif_pos] using colOK (⟨k.val,h⟩ : Fin 30) j
  · have h13 := colOK (13 : Fin 30) j
    have h26 := colOK (26 : Fin 30) j
    have h27 := colOK (27 : Fin 30) j
    change (col 13).testBit j.val = input 13 (52+j.val) at h13
    change (col 26).testBit j.val = input 26 (52+j.val) at h26
    change (col 27).testBit j.val = input 27 (52+j.val) at h27
    by_cases eq : k.val = 30 <;> simp [col32,fixed,h,eq,Nat.testBit_and,h13,h26,h27,mix]
def guardsList : List (Fin 32 × Fin 32) := [(2,6)]
def guards (k : Nat) (v : Nat) := (guardsList[k]?).elim false (fun ab => fixed ab.1 v || fixed ab.2 v)
private theorem columns : ∀ p : Fin 52, ∀ ab ∈ guardsList,
    (fixed ab.1 p.val || fixed ab.2 p.val) = true →
    safe p.val &&& (col32 ab.1 ||| col32 ab.2) = safe p.val := by decide +kernel
private theorem strong {p : Fin 52} {j : Fin 468} (hit : (safe p.val).testBit j.val = true)
    (k : Nat) (on : guards k p.val = true) : guards k (52+j.val) = true := by
  cases e : guardsList[k]? with
  | none => simp [guards,e] at on
  | some ab =>
    have mask := columns p ab (List.mem_of_getElem? e) (by simpa [guards,e] using on)
    have v := congrArg (fun x : Nat => x.testBit j.val) mask
    simpa [guards,e,Nat.testBit_and,Nat.testBit_or,hit,phys] using v
private theorem silent : ∀ (k : Fin 32) (p : Fin 52), 30 ≤ k.val → 4 ≤ p.val → fixed k p.val = false := by decide +kernel
end PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthCharge PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthExceptions.PairShape PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneCase35SemanticReuse.Guard.bound : ∀ (extra : List (Nat → Bool)),
    (∀ w ∈ extra, ∀ p : Fin 52, 4 ≤ p.val → p.val ≠ 44 → w p.val = true →
      ∃ k : Fin 32, fixed k p.val = true ∧ ∀ j : Fin 468,
        fixed k (52+j.val) = true → w (52+j.val) = true) →
    ∀ (gs : List Gate) (o : Nat),
    let pool := List.ofFn fixed ++ extra
    (∀ p : Fin 52, wire (gs.foldl (step guards) pool) o p.val = true) →
    (∀ j : Fin 468, wire (gs.foldl (step guards) pool) o (52+j.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro extra dominated gs o pool hp hn
  let K := Finset.univ \ indexed removed
  have size : 257 ≤ K.card := by
    dsimp only [K]; rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [ecard]
  apply separated_bound guards pool gs o K size _ hp hn
  intro i j lt
  obtain ⟨p,high,mi,mj,raw⟩ := sound i.val j.val lt (Finset.mem_sdiff.mp i.property).2 (Finset.mem_sdiff.mp j.property).2
  refine ⟨p,fun k on => ⟨strong mi k on,strong mj k on⟩,?_⟩
  have pass (k : Fin 32) : good p.val (52+i.val.val) (52+j.val.val) (fixed k) := by
    by_cases low : k.val < 30
    · simpa [good,fixed,low] using raw ⟨k.val,low⟩
    · simp [good,silent k p (by omega) high]
  intro w hw
  rcases List.mem_append.mp hw with prior | fresh
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp prior
    exact pass k
  · intro on
    have avoid : p.val ≠ 44 := by
      intro eq
      rw [eq,show safe 44 = 0 by decide +kernel] at mi
      simpa using mi
    obtain ⟨k,hk,prop⟩ := dominated w fresh p high avoid on
    exact (pass k hk).imp (prop i.val) (prop j.val)

namespace PEqualNP.Research.PlaneCase35SemanticReuse.OrCost

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
end PEqualNP.Research.PlaneCase35SemanticReuse.OrCost

namespace PEqualNP.Research.PlaneCase35SemanticReuse.Ordinary
open Guard.PlaneCase35SixthCharge (fixed guards guardsList)
private abbrev G := Bool × Nat × Nat
private abbrev Col := Nat → Bool
private abbrev w := OrCost.wire
private abbrev start (ab : Fin 32 × Fin 32) : List Col :=
  OrCost.step (List.ofFn fixed) (false,ab.1.val,ab.2.val)
def cheap (g : Bool × Nat × Nat) : Bool := g.1 && (g.2.1 == 32 || g.2.2 == 32)

private def translate (k : Nat) (g : G) : Guard.PlaneFirstAndBudget.Gate :=
  if cheap g then (false, if g.2.1 == 32 then g.2.2 else g.2.1,
                           if g.2.1 == 32 then g.2.2 else g.2.1, some k)
  else (g.1,g.2.1,g.2.2,none)

private theorem unchanged {k : Nat} {s : List Col} (h : w s 32 = guards k) (g : G) :
    OrCost.step s g = Guard.PlaneFirstAndBudget.step guards s (translate k g) := by
  obtain ⟨op,a,b⟩ := g
  cases op
  · simp [translate,cheap,OrCost.step,OrCost.addOr,Guard.PlaneFirstAndBudget.step,
          OrCost.wire,Guard.PlaneFirstAndSeparation.wire]
  · by_cases left : a = 32
    · subst a
      simp [translate,cheap,OrCost.step,OrCost.both,Guard.PlaneFirstAndBudget.step,
            ← h,OrCost.wire,Guard.PlaneFirstAndSeparation.wire,Bool.and_comm] <;> (funext r; simp [OrCost.both,Bool.and_comm])
    · by_cases right : b = 32
      · subst b
        simp [translate,cheap,OrCost.step,OrCost.both,Guard.PlaneFirstAndBudget.step,
              ← h,OrCost.wire,Guard.PlaneFirstAndSeparation.wire,left] <;> rfl
      · simp [translate,cheap,OrCost.step,OrCost.both,Guard.PlaneFirstAndBudget.step,
              OrCost.wire,Guard.PlaneFirstAndSeparation.wire,left,right] <;> rfl

private theorem simulate (k : Nat) (gs : List G) (s : List Col)
    (len : 32 < s.length) (h : w s 32 = guards k) :
    gs.foldl OrCost.step s =
    (gs.map (translate k)).foldl (Guard.PlaneFirstAndBudget.step guards) s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    let v : Col := OrCost.mix g.1 (w s g.2.1) (w s g.2.2)
    have step : OrCost.step s g = s ++ [v] := by
      cases eq : g.1 <;> simp [OrCost.step,OrCost.addOr,OrCost.both,OrCost.mix,v,eq,w] <;> rfl
    have hold : w (s ++ [v]) 32 = w s 32 := by
      exact List.getD_append _ _ _ _ len
    simp only [List.map_cons,List.foldl_cons]
    rw [← unchanged h g]
    exact ih _ (by rw [step]; simp; omega) (by rw [step,hold,h])

private theorem splitCost (k : Nat) (gs : List G) :
    gs.countP cheap + gs.countP (fun g => !g.1) +
    (gs.map (translate k)).countP Prod.fst = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,a,b⟩ := g
    cases op <;> by_cases ha : a = 32 <;> by_cases hb : b = 32 <;>
      simp [List.countP_cons,translate,cheap,ha,hb] at * <;> omega

private theorem fixedClosed : OrCost.Closed (List.ofFn fixed) := by
  intro j
  by_cases lt : j < 32
  · rw [OrCost.wire,List.getD_eq_getElem _ _ (show j < (List.ofFn fixed).length by simpa using lt),List.getElem_ofFn]
    by_cases low : j < 30
    · unfold fixed
      rw [dif_pos low]
      exact OrCost.rawActs ⟨j,low⟩
    · unfold fixed
      rw [dif_neg low]
      by_cases eq : j = 30
      · rw [if_pos eq]
        exact OrCost.andActs (OrCost.rawActs 13) (OrCost.rawActs 26)
      · rw [if_neg eq]
        exact OrCost.andActs (OrCost.rawActs 13) (OrCost.rawActs 27)
  · rw [OrCost.wire,List.getD_eq_default _ _ (show (List.ofFn fixed).length ≤ j by simpa using Nat.le_of_not_gt lt)]
    exact OrCost.falseActs

private def root (r : Nat) := fixed 2 r || fixed 6 r
private def extraAnd (r : Nat) := fixed 1 r && fixed 24 r
private theorem quiet : ∀ p : Fin 52, p.val ≠ 44 → extraAnd p.val = false := by decide +kernel
theorem counts (gs : List G) (o : Nat)
    (hp : ∀ p : Fin 52, w (gs.foldl OrCost.step (OrCost.step (start (2,6)) (true,1,24))) o p.val = true)
    (hn : ∀ j : Fin 468, w (gs.foldl OrCost.step (OrCost.step (start (2,6)) (true,1,24))) o (52+j.val) = false) :
    18 ≤ gs.countP (fun g => !g.1) ∧ 9 ≤ gs.countP (fun g => !(!g.1 || cheap g)) := by
  let s := OrCost.step (start (2,6)) (true,1,24)
  have initial : s = List.ofFn fixed ++ [root,extraAnd] := by rfl
  have len : 32 < s.length := by rw [initial]; simp
  have read : w s 32 = guards 0 := by rfl
  have sim := simulate 0 gs s len read
  have dom (v : Col) (h : v ∈ [root,extraAnd]) (p : Fin 52)
      (_high : 4 ≤ p.val) (avoid : p.val ≠ 44) (on : v p.val = true) :
      ∃ k : Fin 32, fixed k p.val = true ∧ ∀ j : Fin 468,
        fixed k (52+j.val) = true → v (52+j.val) = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · rcases Bool.or_eq_true_iff.mp on with a | b
      · exact ⟨2,a, fun j hit => Bool.or_eq_true_iff.mpr (Or.inl hit)⟩
      · exact ⟨6,b, fun j hit => Bool.or_eq_true_iff.mpr (Or.inr hit)⟩
    · simp [quiet p avoid] at on
  have ands := Guard.bound [root,extraAnd] dom (gs.map (translate 0)) o
    (by simpa only [← initial,← sim,Guard.PlaneFirstAndSeparation.wire,OrCost.wire] using hp)
    (by simpa only [← initial,← sim,Guard.PlaneFirstAndSeparation.wire,OrCost.wire] using hn)
  have ors := OrCost.beforeFirstOr ((false,2,6)::(true,1,24)::gs) fixedClosed o hp hn
  have need : 18 ≤ gs.countP (fun g => !g.1) := by
    apply Nat.le_of_succ_le_succ
    simpa only [List.countP_cons,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using ors
  refine ⟨need,?_⟩
  have eq : (gs.map (translate 0)).countP Prod.fst = gs.countP (fun g => !(!g.1 || cheap g)) := by
    rw [List.countP_map]
    congr 1
    funext g
    cases eq : g.1 <;> cases h : cheap g <;> simp_all [Function.comp_def,translate,cheap]
  rwa [←eq]
end PEqualNP.Research.PlaneCase35SemanticReuse.Ordinary
namespace PEqualNP.Research.PlaneCase35SemanticReuse.Audit
open OrCost (wire step)
abbrev G := Bool × Nat × Nat
abbrev Col := Nat → Bool
def value (s : List Col) (g : G) (r : Nat) :=
  if g.1 then wire s g.2.1 r && wire s g.2.2 r else wire s g.2.1 r || wire s g.2.2 r
def possible (pred : G → Bool) (s : List Col) (g : G) :=
  ∃ alt : G, pred alt = true ∧ ∀ r : Fin 520, value s alt r.val = value s g r.val
def free (g : G) := !g.1 || Ordinary.cheap g
noncomputable def chooseGate (pred : G → Bool) (s : List Col) (g : G) : G := by
  classical
  exact if h : possible pred s g then Classical.choose h else g
private theorem equiv (pred : G → Bool) (s : List Col) (g : G) (r : Fin 520) :
    value s (chooseGate pred s g) r.val = value s g r.val := by
  classical
  unfold chooseGate
  split
  · rename_i h; exact (Classical.choose_spec h).2 r
  · rfl
private theorem chosen (pred : G → Bool) (s : List Col) (g : G) :
    pred (chooseGate pred s g) = true ↔ possible pred s g := by
  classical
  unfold chooseGate
  split
  · rename_i h; simp [(Classical.choose_spec h).1,h]
  · rename_i h
    constructor
    · intro yes; exact ⟨g,yes,fun _ => rfl⟩
    · exact fun yes => False.elim (h yes)

noncomputable def rewriteG (pred : G → Bool) (s : List Col) : List G → List G
  | [] => []
  | g :: gs => chooseGate pred s g :: rewriteG pred (step s g) gs
private def row (s : List Col) (r : Nat) := s.map (fun v => v r)
private theorem read (s : List Col) (r j : Nat) : wire s j r = (row s r).getD j false := by
  simp only [wire,row,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases s[j]? <;> rfl
private theorem advance (s : List Col) (r : Nat) (g : G) :
    row (step s g) r = row s r ++ [value s g r] := by
  cases h : g.1 <;> simp [row,step,OrCost.addOr,OrCost.both,value,h]
private theorem simulate (pred : G → Bool) (gs : List G) (r : Fin 520) (s t : List Col)
    (h : row s r.val = row t r.val) :
    row (gs.foldl step s) r.val = row ((rewriteG pred s gs).foldl step t) r.val := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    rw [advance,advance,h,← equiv pred s g r]
    simp only [value,read,h]
theorem transfer (pred : G → Bool) (gs : List G) (s : List Col) (o : Nat) (r : Fin 520) :
    wire ((rewriteG pred s gs).foldl step s) o r.val = wire (gs.foldl step s) o r.val := by
  simp only [read,simulate pred gs r s s rfl]

noncomputable def credit (s : List Col) (g : G) : Nat := by
  classical
  exact if possible Prod.fst s g ∧ possible free s g then 1 else 0
noncomputable def auditStep (state : List Col × Nat) (g : G) := (step state.1 g,state.2 + credit state.1 g)
theorem count (gs : List G) (s : List Col) (n : Nat) :
    (gs.foldl auditStep (s,n)).2 +
      (rewriteG Prod.fst s gs).countP (fun g => !g.1) +
      (rewriteG free s gs).countP (fun g => !free g) = n + gs.length := by
  induction gs generalizing s n with
  | nil => simp [rewriteG]
  | cons g gs ih =>
    have next := ih (step s g) (n+credit s g)
    have atLeast : possible Prod.fst s g ∨ possible free s g := by
      cases h : g.1 with
      | true => exact Or.inl ⟨g,h,fun _ => rfl⟩
      | false => exact Or.inr ⟨g,by simp [free,h],fun _ => rfl⟩
    have cost : credit s g + (if !(chooseGate Prod.fst s g).1 then 1 else 0) +
        (if !(free (chooseGate free s g)) then 1 else 0) = 1 := by
      have x := chosen Prod.fst s g
      have y := chosen free s g
      cases u : (chooseGate Prod.fst s g).1 <;> cases v : free (chooseGate free s g) <;>
        simp [u,v] at x y <;> simp_all [credit]
    simp only [List.foldl_cons,List.length_cons,List.countP_cons,rewriteG,auditStep]
    omega
end PEqualNP.Research.PlaneCase35SemanticReuse.Audit
open PEqualNP.Research.PlaneCase35SemanticReuse PEqualNP.Research.PlaneCase35SemanticReuse.Guard.PlaneCase35SixthCharge PEqualNP.Research.PlaneCase35SemanticReuse.Audit in
theorem PEqualNP.Research.PlaneCase35SemanticReuse : ∀ (gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := OrCost.step (OrCost.step (List.ofFn fixed) (false,2,6)) (true,1,24)
  (∀ p : Fin 52, OrCost.wire (gs.foldl OrCost.step pool) o p.val = true) →
  (∀ j : Fin 468, OrCost.wire (gs.foldl OrCost.step pool) o (52+j.val) = false) →
  35 + (gs.foldl auditStep (pool,0)).2 ≤ 8 + gs.length := by
  intro gs o pool hp hn
  have lower (pred : Audit.G → Bool) := Ordinary.counts (rewriteG pred pool gs) o
    (fun p => (transfer pred gs pool o ⟨p.val,by omega⟩).trans (hp p))
    (fun j => (transfer pred gs pool o ⟨52+j.val,by omega⟩).trans (hn j))
  have ors := (lower Prod.fst).1
  have ands := (lower free).2
  change 9 ≤ (rewriteG free pool gs).countP (fun g => !free g) at ands
  have eq := Audit.count gs pool 0
  have bounded := (Nat.add_le_add (Nat.add_le_add_left ors (gs.foldl auditStep (pool,0)).2) ands).trans_eq eq
  omega
