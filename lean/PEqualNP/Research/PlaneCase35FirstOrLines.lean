import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
set_option Elab.async false

namespace PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndSeparation

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

end PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndSeparation


namespace PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndBudget
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
    (K : Finset (Fin 468)) (hk : 129 ≤ K.card)
    (sep : ∀ i j : K, i.val < j.val → ∃ p : Fin 52,
      (∀ k, guards k p.val = true → guards k (52+i.val.val) = true ∧ guards k (52+j.val.val) = true) ∧
      ∀ w ∈ s, good p.val (52+i.val.val) (52+j.val.val) w)
    (hp : ∀ p : Fin 52, wire (gs.foldl (step guards) s) o p.val = true)
    (hn : ∀ n : Fin 468, wire (gs.foldl (step guards) s) o (52 + n.val) = false) :
    8 ≤ gs.countP Prod.fst := by
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
  have le : gs.countP Prod.fst ≤ 7 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) le
  change 2 ^ gs.countP Prod.fst ≤ 128 at bound
  omega
end PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndBudget


namespace PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthExceptions.PairShape

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

end PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthExceptions.PairShape
namespace PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthExceptions.PairShape
set_option maxHeartbeats 0
set_option maxRecDepth 14000
private def col (k : Nat) := (0x4210413001a00c000e0000000000000000000000000024301102001c5000d0020400282800800050030001000000140015000010000202880024900000000008400084a800000000000000008c000b2990000000000890014b61000000000000000000000000000018c20000006524ff76feddb7ffd83dc55021fd547d6fa3bb7f6785e882ea5fe40bf6dd6d5001f621bf3176fe901c2000d8442000002d140800006fdd6a4040375240000001bdf8b6f5851fa8bac0d000e8000000defc5b7d8dfef58e01d3f3abb428a1f5400d203ffff6eefec8d27de9ff2d949bd07d460d51407504fffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffe0000000000000000000000003ffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000f800001fffff80000000000000000003fffff00000000000000000007ffffffffffffffffffc000000000000000000000000000000000000000000000001f00007ffffe00000000000003e0000fffffc00000000000007fffc000000000000003fffffffffffff800000000000000000000000000007c00010f000780001fff0000000000000000f80003fffe00000000078003ffff00000000003ffe00000000007fffffffffe00000000000000000803c00000f0007c000000fff800000001e000878003c001ff000000000003e000fff80000003c01fff00000007ffc0000001fffffff0000000000440380088880043801c00e007f80000201c000078003c0000ffc0000070021c00e007f800000001e00ffc00007803ff00001ff80000fffff80000200270040070002700000000707ff001103004444002381c0c03e00040c0003c01e0007f00003811c0c03e0000003c0ffc01e07fe00fe0007fe0002004e0000004210c13001e04c700f00802e02003800260000031fe024301122011c7060f8020400383801f00070230c038000781f8e1fe0781f800000000440e0000008e09180b4f0cf00809c0000021119303c2dc1e102e080180120000c7c123092427398f840800c38060184610401c1e679860020298202492100302980840008ca880000002207000008ca30b3998209800008894c1cb63882c40204800c724612a2735d04018c2193110677511100440202490048c006053002421640105210124908042a108025500000090600023522db410a00092646b69058810481a93254b7840cc9546f00890120000000822a055402a282905c448090101248052010a409228085440954408a89016c000091001352d821400926b6429022952aabc8adb00000000000000000000000000000000000000000000000000000000000037fe7fedffff383c00000000000003f7ff3c7f9fe7b9efbfe3e19867900000000000006ffce000f7bfff7357400000000000000000000000000000000000000000000001bfdfb7ff3880000000000fbfe73de6ceef988a06c3fba00000000001ff90007fdbde980000000000037fa00ef7fdaa80000000000000000000000000000000000037efb7e400000007bf336ab90b8347ec0077f8000000001fd007d6fa01a3f60000000001fe003f6dd0000000001bf0076fe90000000000000000000000000006fdd6000003752400000000000000000000000000000002e1cff003bfc0000003fc1fff873fc00000007f80fffc0000003fc1fff80000000000000000001fff801ff00000017707fb8073e0ff000000ff0fc00000000000000000000000058cfc01df000001f07fc3be000003e0ff8000003fc7e00000000000007e0703fc0fe000007bc0fe31f0e78000030c00000bb83fdc0660f00003e180000000000000000002c4e01b0000707877c000039e00000fb0000000079dddd8060fd86800000c67e1b838000740fc1f000003dc1e331cc000600002ec1f602838001c40000000000000589c05000221b800050000e80002e82fb1af0bd105eb32000604b080d00b76d0107ec340000c5c34200083c1c0000ee18c8d00080016c34082001000000000016480a001a001002007f42d65db0b0d83dc550200054302103a1762785e882ea40040900406d5001f62000316208001c2000d8442000002d1408000000000a40401000000000000000000000000000000000001fe3aded8586c3fb510034c2278f65e2f9176802140436d01fd001b908038400d84a0005a30800000688800000001bdf8b6f5851fa8bac0d000e800000000000000000000000003f3abb428a1f5400d203c74e2e2d808406da03e001400c0014001510001000000000000000000000000000000000000000defc5b7d8dfef58e01d00000000000000000001fbff46c7ec0d278e9cf2d849bd07c060c01407404 >>> (468*k)) &&& 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
private def key (k : Nat) := (0x6332c4232810b2206b206330c5af0b39f070eb015aeeb52aea31ae606ae0632cc52aca4eec9296c55aeab4eea9422a8212a452a8a4228839e871ee834ee6939e6731a6610a624224831a46296450ea4139e272962521224eea206320c31a06212041ee035adeb295e5e6de3109e2529ca211c4109c20e9c14eda91eda30e9a1069a0 >>> (5*k)) &&& 0x1f
private def removed : Nat := 0xf7ffffbf2fe47ff7afed5f1eea3f826fffcd8ebfbf6f8fff0ffa9ff57fffff9ddffeea599df1c9e9f731715bc679fe2b77fed77ffb4f5bfcf55e6
private def full := (2:Nat)^468-1
private def side (i k : Nat) := if (col k).testBit i then full else col k
private def cov (i p : Nat) := side i (key (4*p)) &&& side i (key (4*p+1)) &&&
  side i (key (4*p+2)) &&& side i (key (4*p+3))
private def safe (p : Nat) := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 >>> (468*p)) &&& full
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
private theorem ecard : (indexed removed).card = 337 := by decide +kernel
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
end PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthCharge
open PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthCharge PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneCase35SixthExceptions.PairShape PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndSeparation PEqualNP.Research.PlaneCase35FirstOrLines.Guard.PlaneFirstAndBudget in
theorem PEqualNP.Research.PlaneCase35FirstOrLines.Guard.bound : ∀ (extra : List (Nat → Bool)),
    (∀ w ∈ extra, ∀ p : Fin 52, 4 ≤ p.val → (0x31b112b41c3af : Nat).testBit p.val = false → w p.val = true →
      ∃ k : Fin 32, fixed k p.val = true ∧ ∀ j : Fin 468,
        fixed k (52+j.val) = true → w (52+j.val) = true) →
    ∀ (gs : List Gate) (o : Nat),
    let pool := List.ofFn fixed ++ extra
    (∀ p : Fin 52, wire (gs.foldl (step guards) pool) o p.val = true) →
    (∀ j : Fin 468, wire (gs.foldl (step guards) pool) o (52+j.val) = false) →
    8 ≤ gs.countP Prod.fst := by
  intro extra dominated gs o pool hp hn
  let K := Finset.univ \ indexed removed
  have size : 129 ≤ K.card := by
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
    have zero : ∀ i : Fin 52, (0x31b112b41c3af : Nat).testBit i.val = true → safe i.val = 0 := by decide +kernel
    have avoid : (0x31b112b41c3af : Nat).testBit p.val = false := by
      cases e : (0x31b112b41c3af : Nat).testBit p.val with
      | false => rfl
      | true => simp [zero p e] at mi
    obtain ⟨k,hk,prop⟩ := dominated w fresh p high avoid on
    exact (pass k hk).imp (prop i.val) (prop j.val)

namespace PEqualNP.Research.PlaneCase35FirstOrLines.OrCost

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

def poolWire (i : Fin 33) : Column :=
  if h : i.val < 30 then base ⟨i.val,h⟩
  else if i.val = 30 then mix true (input 13) (input 26)
  else if i.val = 31 then mix true (input 13) (input 27)
  else mix false (input 2) (input 6)

private def negatives : Array (Fin 468) := #[
  41, 232, 287, 197, 153, 53,
  306, 349]
private def positives : Array (Array (Fin 52)) := #[
  #[0, 4, 6, 8, 10, 11, 15, 16, 22, 25, 28, 29, 30, 31, 34, 39, 41, 47, 51], #[1, 4, 8, 12, 16, 17, 18, 19, 20, 24, 28, 33, 37, 38, 39, 41, 43, 44, 49], #[2, 5, 8, 12, 16, 20, 21, 22, 23, 24, 28, 32, 34, 35, 38, 40, 45, 47, 48], #[1, 4, 8, 12, 13, 14, 15, 18, 20, 24, 29, 30, 31, 34, 36, 40, 43, 44, 49], #[0, 4, 5, 6, 7, 9, 12, 16, 22, 25, 28, 33, 34, 35, 36, 39, 40, 45, 48], #[0, 5, 8, 12, 13, 14, 15, 16, 20, 21, 23, 27, 29, 31, 34, 37, 40, 46, 48],
  #[0, 5, 8, 12, 16, 20, 21, 22, 23, 24, 28, 32, 37, 38, 39, 40, 45, 46, 48], #[1, 4, 8, 9, 10, 11, 14, 16, 17, 19, 20, 25, 31, 34, 37, 41, 44, 50, 51]]
private def negRow (t : Fin 8) := 52 + (negatives[t.val]!).val
private def flag (t : Fin 8) (i : Fin 19) : Fin 52 := positives[t.val]![i.val]!
variable (t : Fin 8)
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

-- The meet closure on 52 positive and eight selected negative coordinates.
private def signatures : Array Nat := #[
  0x0, 0x1, 0x2, 0x3, 0x4, 0x8,
  0xc, 0xf, 0x10, 0x20, 0x40, 0x80,
  0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000,
  0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000,
  0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000,
  0x3000000, 0x4000000, 0x8000000, 0xf000000, 0x10000000, 0x20000000,
  0x40000000, 0x80000000, 0x100000000, 0x200000000, 0x400000000, 0x800000000,
  0x1000000000, 0x2000000000, 0x4000000000, 0x8000000000, 0x10000000000, 0x20000000000,
  0x40000000000, 0x80000000000, 0x100000000000, 0x200000000000, 0x400000000000, 0x800000000000,
  0x1000000000000, 0x2000000000000, 0x4000000000000, 0x8000000000000, 0x10000000000000, 0x18808000008000,
  0x20000000000000, 0x24000240800000, 0x40000000000000, 0x80000000000000, 0x80001000240400, 0xa0000000000000,
  0xa0010000000000, 0xa0020000000000, 0xa00f0000000000, 0x100000000000000, 0x100200024080000, 0x110000000000000,
  0x110000000000010, 0x110000000000020, 0x1100000000000f0, 0x140000000000000, 0x140000400000000, 0x140000f00000000,
  0x200000000000000, 0x200480800000800, 0x210000000000000, 0x280000000000000, 0x280000000001000, 0x280000000004000,
  0x28000000000f000, 0x290000000000000, 0x290000010000000, 0x2900000f0000000, 0x400000000000000, 0x400000100022040,
  0x420000000000000, 0x440000000000000, 0x440100000000000, 0x440f00000000000, 0x460000000000000, 0x500000000000000,
  0x520000000000000, 0x520002000000000, 0x52000f000000000, 0x540000000000000, 0x560000000000000, 0x560000010001204,
  0x640000000000000, 0x640000000100000, 0x640000000400000, 0x640000000f00000, 0x6e0000000000000, 0x6e2000001000120,
  0x750000000000000, 0x751010000010001, 0x800000000000000, 0x801000000000000, 0x802000000000000, 0x80f000000000000,
  0x810000000000000, 0x810000000000100, 0x810000000000200, 0x810000000000f00, 0x820000000000000, 0x820000000010000,
  0x8200000000f0000, 0x840000000000000, 0x840044080000080, 0x880000000000000, 0x8a0000000000000, 0x8a0100000100012,
  0x910000000000000, 0x910020002404000, 0xa90000000000000, 0xa90002408000008, 0xff0000000000000, 0xff000241800120c,
  0xff1110000110013, 0xff2020003404120, 0xfffffffffffffff]
private def word (i : Fin 135) : Nat := signatures[i.val]!
private def generators : Array (Fin 135) := #[
  109, 125, 107, 101, 89, 64,
  127, 70, 61, 129, 122, 79,
  59, 7, 74, 117, 84, 120,
  105, 33, 87, 77, 98, 68,
  93, 113, 132, 131, 116, 119,
  3, 6, 133]
private def intersections : Array Nat := #[
  0x6d6c6d6c6c505047470000003e3e1414003a3a3a3a360036006d6c6666666666666363635f5f5f5f5b5b5b5b5858585050504e4e4e4e504e4e4b4b4b4747474745452e002e0000003e00003a3a00000036000000000000002e00000000000000000000000000000000000000000000000000140000000000000000000000000100000001000100, 0x7d7c7d7c7c7b7b6e6e7d7c7b6e6e7676766e6e6e6e6e6e6e6e00004141180018003c3c003c3c3c003c3232003c00003f3f3f3f3f3f3f000000000000080008000000414141413f3f003c3c000000000000000000320000000000000000000000000000000000000000000000000018000000000000000000000000000000080200000002020000, 0x6b6b6a6a6a5151000041413f3e3e3c3c3c0c000c003737000066666b6a666666665e5e5b5a5a5a585e5b5b5b5a5858515151515151514e4e4e3e3e3e090900000000414141413f3f3e3c3c00000000370000000000000000000000000000000000000000001c00001c001c0000000000000000000000000000000c000009000000000000000000, 0x6564646564000045453c3c003e3e3c3c3c0d0d00000000000063635e5e5b5b5b5b6564636060605f5e5b5b5b5a5858222200100010000000004b4b4b4545454545453c3c3c3c00003e3c3c000000000000000000000000000000000000000000000000002200000000000000000000000000000000001000000d00000000000404000400000000, 0x5958585858000000000000000000150000000000000000000058585858585858585858585858585858585858585958000000110000000000002600000a0000000000000000000000000000000000000000000000000000000000000000000000260000000000000000000000000000000015000000110000000000000a00000000000000000000, 0x403f3f3f3f3f3f00003f3f3f00001600000e0000000000000000003f3f190000000000002a000000000000000000003f3f3f3f3f3f3f0000000000000000000000003f3f3f3f403f00000000000000000000000000000000000000002a0000000000000000000000000000000019000016000000000000000e0000000000000000000000000000,
  0x7f7f7e7e7e72727f7e6e6e6e6e6e6e6e6e727272726e6e6e6e474700001a1a000045454545454545000000000000003a3a3a121200003a00004545454747474745452f2f000000000000003a3a000000000000000000002f000000000000000000000000001d00001d1d00001a0000000000000012000000000000000000000000000000000000, 0x46454545450000454500000000001700000000000000000000454500000000000045454545454545003300000000002300000000000000000045454545454545464500000000000000000000000000000000003300000000000000000000000000000023001f001f00000000000000170000000000000000000000000000000000000000000000, 0x3d3c3c3c3c000000003c3c0000003c3c3c000000003800000000003c3c1b0000003c3c003c3c3c003c0000003c0000240000000000000000002700000000000000003c3c3c3c0000003d3c00000038000000000000000000000000000000002700002400000000000000001b000000000000000000000000000000000000000000000000000000, 0x8180808180818072727b7b7b6e6e6e6e6e727272726e6e6e6e505051514e4e4e4e0000002b2b00000000000000000055555551515151504e4e2828003a3a3a3a00003f3f3f3f3f3f0000003a3a00000000000000000000000000002b00002800000000000020200000000000000000000000000000000000000000000000000505050000000000, 0x7a797979796e6e6e6e6e6e6e7a796e6e6e6e6e6e6e6e6e6e6e3e3e3e3e3e3e3e3e3e3e3e2c0000003e3e3e3e000000250000000000000000003e3e3e0b00000000003000000000003e00000000000000000000000000300000002c00000000000025000000000000000000000000000000000000000000000000000b0000000000000000000000, 0x4f4e4e4e4e4e4e000000000000000000000f000000000000004e4e4e4e4e4e4e4e00000000000000003400000000004e4e4e4e4e4e4e4e4f4e29000000000000000031000000000000000000000000000000340000310000000000000029000000000000000000000000000000000000000000000000000f000000000000000000000000000000,
  0x3b3a3a3a3a3a3a3a3a00000000000000003a3a3a3a390000003a3a0000000000000000002d000000003500000000003a3a3a130000003a00000000003a3a3a3a00000000000000000000003b3a3900000035000000000000002d000000000000000000000000000000000000000000000000001300000000000000000000000000000000000000, 0x70003060005000000020000000000000000000000000000000100000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000706050403020100, 0x4a494847473a3a47470800000b000000003a3a3a3a0000000047470900000000004545454545454500000000000a003a3a3a000000003a00004545454a49484745450000000000000000003a3a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0a09080000000000000000, 0x7573727472727272726e6e6e6e6e6e6e6e757473726e6e6e6e3a3a0c00000000000d000000000000000000000000003a3a3a000000003a0f000000003a3a3a3a0000000000000e000000003a3a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0e0d0c000000000000000000000000, 0x5453515251515112003f3f3f000000000000000000000000004e4e51514e4e4e4e1000000000000000000000001100515151545352514e4e4e0000000000000000003f3f3f3f3f3f000000130000000000000000000000000000000000000000000000000000000000000000000000000000001312111000000000000000000000000000000000, 0x78767776766e6e6e6e76766e6e6e7877766e6e6e6e6e6e6e6e14003c3c000000003c3c003c3c3c003c0000003c1500000000000000000000000000000000000017003c3c3c3c1600003c3c000000000000000000000000000000000000000000000000000000000000000000000000171615140000000000000000000000000000000000000000,
  0x69686766664e4e1a001800003e3e000000000000000000000066666666696867665b5b5b585858585b5b5b5b5858584e4e4e4e4e4e4e4e4e4e3e3e3e0000000000000000000019003e1b0000000000000000000000000000000000000000000000000000000000000000001b1a1918000000000000000000000000000000000000000000000000, 0x211e00200020001d000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000000000000000000000000000000000000000021201f1e1d1c00000000000000000000000000000000000000000000000000000000, 0x575555565555553a3a3f3f3f25000000003a3a3a3a00000000505051514e4e4e4e220000000000000000000000000057565551515151504e4e0000003a3a3a3a23003f3f3f3f3f3f0024003a3a00000000000000000000000000000000000000002524232200000000000000000000000000000000000000000000000000000000000000000000, 0x4d4b4b4c4b280045450000003e3e00000000000000000000004b4b3e3e3e3e3e3e4b4b4b454545453e3e3e3e002600000000000000000029004d4c4b4545454545450000000000003e2700000000000000000000000000000000000000292827260000000000000000000000000000000000000000000000000000000000000000000000000000, 0x62606061602b0045453c3c002c003c3c3c00000000000000005f5f5a5a5858585860605f6261605f5a5858585a5858000000000000000000004545454545454545453c3c3c3c2a00003c3c2d000000000000000000000000002d2c2b2a000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x44434241413f3f2f0041413f30003c3c3c00000000000000002e004141000000003c3c003c3c3c003c0000003c00003f3f3f3f3f3f3f003100000000000000000000444342413f3f003c3c0000000000000000000031302f2e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x5d5b5c5b5b000000003200003e3e00000000000000000000005b5b5b5b5b5b5b5b5b5b5b585858585b5d5c5b585858000000000000000034003e3e3e0000000033000000000000003e0000350000000000353433320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x71706f6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e71706f6e3600370000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003800390039383736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x848284828280807e7e7d7c7b7979777776727272726f6e6f6e6d6c6a6a676667666464636060605f5e5c5c5b5a585855555551515151504e4e4b4b4b484748474545424142413f3f3e3c3c3a3a00000036000000320000002e00000000000000000000000000000000000000000018000000140000000000000000000000080300000003020100, 0x838282838281807e7e7c7c7b7979767676747472726e6e6e6e6c6c6a6a666666666564636161605f5e5b5b5b5a585856565552515251504e4e4c4c4b474747474545414141413f3f3e3c3c3a3a00000000000000000000000000002b00002800000000002220200000000000000000000000000000001000000d00000000000606050400000000, 0x7472727472727272726e6e6e6e6e6e6e6e747472726e6e6e6e3a3a0000000000000d000000000000000000000000003a3a3a000000003a00000000003a3a3a3a00000000000000000000003a3a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000000000000000000000000, 0x77767776766e6e6e6e76766e6e6e7777766e6e6e6e6e6e6e6e14003c3c000000003c3c003c3c3c003c0000003c0000000000000000000000000000000000000000003c3c3c3c0000003c3c000000000000000000000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000,
  0x30003000000000000020000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000003020100, 0x60000060005000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000606050400000000, 0x858582828280807f7e7c7c7b79797676767372737270706e6e6c6c6b6a686866666464636060605f5e5b5b5b5a585855555553535151504e4e4b4b4b494947474545434341413f3f3e3c3c3a3a000037000000000000002f000000000000000000000000001e00001e1d1c001a000000000000001200000000000c000009000000000000000000]
private def witnesses : Array (Fin 8) := #[
  0, 1, 0, 2, 0, 0,
  0, 0, 2, 0, 1, 0,
  4, 0, 1, 1, 0, 0,
  0, 1, 3, 0, 0, 0,
  0, 0, 1, 0, 0, 1,
  5, 0, 0, 0, 3, 1,
  1, 1, 0, 0, 1, 0,
  0, 0, 0, 2, 0, 2,
  0, 0, 0, 0, 0, 1,
  0, 0, 0, 1, 0, 0,
  0, 1, 0, 0, 3, 0,
  0, 1, 1, 0, 4, 0,
  0, 0, 0, 0, 1, 2,
  0, 5, 0, 0, 0, 0,
  3, 0, 0, 0, 0, 6,
  0, 0, 0, 2, 0, 0,
  0, 0, 1, 0, 0, 1,
  0, 0, 1, 2, 0, 1,
  0, 0, 0, 0, 0, 7,
  0, 0, 0, 0, 0, 1,
  1, 0, 2, 0, 0, 1,
  0, 0, 0, 0, 0, 0,
  0, 0, 0]
private def meetIndex (i : Fin 33) (j : Fin 135) : Fin 135 :=
  Fin.ofNat 135 ((intersections[i.val]! >>> (8*j.val)) &&& 255)
private theorem row0 : ∀ j : Fin 135, word (meetIndex 0 j) = word (generators[0]!) &&& word j := by decide +kernel
private theorem row1 : ∀ j : Fin 135, word (meetIndex 1 j) = word (generators[1]!) &&& word j := by decide +kernel
private theorem row2 : ∀ j : Fin 135, word (meetIndex 2 j) = word (generators[2]!) &&& word j := by decide +kernel
private theorem row3 : ∀ j : Fin 135, word (meetIndex 3 j) = word (generators[3]!) &&& word j := by decide +kernel
private theorem row4 : ∀ j : Fin 135, word (meetIndex 4 j) = word (generators[4]!) &&& word j := by decide +kernel
private theorem row5 : ∀ j : Fin 135, word (meetIndex 5 j) = word (generators[5]!) &&& word j := by decide +kernel
private theorem row6 : ∀ j : Fin 135, word (meetIndex 6 j) = word (generators[6]!) &&& word j := by decide +kernel
private theorem row7 : ∀ j : Fin 135, word (meetIndex 7 j) = word (generators[7]!) &&& word j := by decide +kernel
private theorem row8 : ∀ j : Fin 135, word (meetIndex 8 j) = word (generators[8]!) &&& word j := by decide +kernel
private theorem row9 : ∀ j : Fin 135, word (meetIndex 9 j) = word (generators[9]!) &&& word j := by decide +kernel
private theorem row10 : ∀ j : Fin 135, word (meetIndex 10 j) = word (generators[10]!) &&& word j := by decide +kernel
private theorem row11 : ∀ j : Fin 135, word (meetIndex 11 j) = word (generators[11]!) &&& word j := by decide +kernel
private theorem row12 : ∀ j : Fin 135, word (meetIndex 12 j) = word (generators[12]!) &&& word j := by decide +kernel
private theorem row13 : ∀ j : Fin 135, word (meetIndex 13 j) = word (generators[13]!) &&& word j := by decide +kernel
private theorem row14 : ∀ j : Fin 135, word (meetIndex 14 j) = word (generators[14]!) &&& word j := by decide +kernel
private theorem row15 : ∀ j : Fin 135, word (meetIndex 15 j) = word (generators[15]!) &&& word j := by decide +kernel
private theorem row16 : ∀ j : Fin 135, word (meetIndex 16 j) = word (generators[16]!) &&& word j := by decide +kernel
private theorem row17 : ∀ j : Fin 135, word (meetIndex 17 j) = word (generators[17]!) &&& word j := by decide +kernel
private theorem row18 : ∀ j : Fin 135, word (meetIndex 18 j) = word (generators[18]!) &&& word j := by decide +kernel
private theorem row19 : ∀ j : Fin 135, word (meetIndex 19 j) = word (generators[19]!) &&& word j := by decide +kernel
private theorem row20 : ∀ j : Fin 135, word (meetIndex 20 j) = word (generators[20]!) &&& word j := by decide +kernel
private theorem row21 : ∀ j : Fin 135, word (meetIndex 21 j) = word (generators[21]!) &&& word j := by decide +kernel
private theorem row22 : ∀ j : Fin 135, word (meetIndex 22 j) = word (generators[22]!) &&& word j := by decide +kernel
private theorem row23 : ∀ j : Fin 135, word (meetIndex 23 j) = word (generators[23]!) &&& word j := by decide +kernel
private theorem row24 : ∀ j : Fin 135, word (meetIndex 24 j) = word (generators[24]!) &&& word j := by decide +kernel
private theorem row25 : ∀ j : Fin 135, word (meetIndex 25 j) = word (generators[25]!) &&& word j := by decide +kernel
private theorem row26 : ∀ j : Fin 135, word (meetIndex 26 j) = word (generators[26]!) &&& word j := by decide +kernel
private theorem row27 : ∀ j : Fin 135, word (meetIndex 27 j) = word (generators[27]!) &&& word j := by decide +kernel
private theorem row28 : ∀ j : Fin 135, word (meetIndex 28 j) = word (generators[28]!) &&& word j := by decide +kernel
private theorem row29 : ∀ j : Fin 135, word (meetIndex 29 j) = word (generators[29]!) &&& word j := by decide +kernel
private theorem row30 : ∀ j : Fin 135, word (meetIndex 30 j) = word (generators[30]!) &&& word j := by decide +kernel
private theorem row31 : ∀ j : Fin 135, word (meetIndex 31 j) = word (generators[31]!) &&& word j := by decide +kernel
private theorem row32 : ∀ j : Fin 135, word (meetIndex 32 j) = word (generators[32]!) &&& word j := by decide +kernel
private theorem meetWord (i : Fin 33) (j : Fin 135) :
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
  · exact row30 j
  · exact row31 j
  · exact row32 j
private def Rep (x : Column) (i : Fin 135) :=
  (∀ p : Fin 52, x p.val = (word i).testBit p.val) ∧
  (∀ t : Fin 8, x (negRow t) = (word i).testBit (52+t.val))
private theorem rawRep : ∀ j : Fin 33, Rep (poolWire j) (generators[j.val]!) := by
  unfold Rep
  decide +kernel
private theorem falseRep : Rep (fun _ => false) 0 := by unfold Rep; decide +kernel
private theorem trueRep : Rep (fun _ => true) 134 := by unfold Rep; decide +kernel
-- A conjunction acts on every previously certified signature. Composition
-- handles arbitrary AND gates using associativity and only 30 generator rows.
private def Acts (x : Column) := ∀ y : Column, ∀ i : Fin 135, Rep y i →
  ∃ j : Fin 135, Rep (mix true x y) j
private theorem rawActs (j : Fin 33) : Acts (poolWire j) := by
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
private theorem signature {x : Column} (h : Acts x) : ∃ i : Fin 135, Rep x i := by
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
private def mask (k : Fin 8) (i : Fin 135) : Finset (Fin 19) :=
  if (word i).testBit (52+k.val) then ∅ else
    Finset.univ.filter (fun f => (word i).testBit (flag k f).val)
private theorem smallMask : ∀ i : Fin 135, ∀ k : Fin 8, (mask k i).card ≤ 1 := by decide +kernel
private theorem repSmall {i : Fin 135} {x : Column} (h : Rep x i) (k : Fin 8) :
    (supp k x).card ≤ 1 := by
  have eq : supp k x = mask k i := by simp only [supp,mask,h.1,h.2]
  rw [eq]; apply smallMask
private def Easy (x : Column) (k : Fin 8) :=
  x (negRow k) = true ∨ ∀ f : Fin 19, x (flag k f).val = false
def line (x : Column) (a : Nat) := ∀ p : Fin 52, x p.val = input a p.val
def linePair (x y : Column) :=
  (line x 13 ∧ line y 19) ∨ (line x 19 ∧ line y 13)
private theorem canChoose : ∀ i : Fin 135, i ≠ 7 → i ≠ 33 →
    let k := witnesses[i.val]!
    (word i).testBit (52+k.val) = true ∨ ∀ f : Fin 19, (word i).testBit (flag k f).val = false := by decide +kernel
private theorem easy {x : Column} {i : Fin 135} (h : Rep x i) (a : i ≠ 7) (b : i ≠ 33) :
    Easy x (witnesses[i.val]!) := by
  simpa only [Easy,h.1,h.2] using canChoose i a b
private theorem bits13 : ∀ p : Fin 52, (word 7).testBit p.val = input 13 p.val := by decide +kernel
private theorem line13 {x : Column} (h : Rep x 7) : line x 13 :=
  fun p => (h.1 p).trans (bits13 p)
private theorem bits19 : ∀ p : Fin 52, (word 33).testBit p.val = input 19 p.val := by decide +kernel
private theorem line19 {x : Column} (h : Rep x 33) : line x 19 :=
  fun p => (h.1 p).trans (bits19 p)
private theorem same {x y : Column} {i : Fin 135} (hx : Rep x i) (hy : Rep y i) :
    Rep (mix false x y) i := by
  constructor
  · intro p; simp [mix,hx.1 p,hy.1 p]
  · intro k; simp [mix,hx.2 k,hy.2 k]
private theorem freeOr {x y : Column} {i j : Fin 135} (hx : Rep x i) (hy : Rep y j)
    (excluded : ¬ linePair x y) : ∃ k : Fin 8, (supp k (mix false x y)).card ≤ 1 := by
  by_cases eq : i = j
  · subst j; exact ⟨0,repSmall (same hx hy) 0⟩
  by_cases ix : i = 7 ∨ i = 33
  · by_cases jy : j = 7 ∨ j = 33
    · rcases ix with rfl | rfl <;> rcases jy with rfl | rfl
      · exact False.elim (eq rfl)
      · exact False.elim (excluded (Or.inl ⟨line13 hx,line19 hy⟩))
      · exact False.elim (excluded (Or.inr ⟨line19 hx,line13 hy⟩))
      · exact False.elim (eq rfl)
    · have comm : mix false x y = mix false y x := by funext r; exact Bool.or_comm ..
      rw [comm]
      exact ⟨_,orSmall _ _ _ (easy hy (fun h => jy (Or.inl h)) (fun h => jy (Or.inr h))) (repSmall hx _)⟩
  · exact ⟨_,orSmall _ _ _ (easy hx (fun h => ix (Or.inl h)) (fun h => ix (Or.inr h))) (repSmall hy _)⟩
private def Closed (s : List Column) := ∀ j : Nat, Acts (wire s j)
private theorem appendActs {s : List Column} (h : Closed s) (v : Column) (hv : Acts v) :
    Closed (s ++ [v]) := by
  intro j
  by_cases lt : j < s.length
  · simpa only [wire,List.getD_append _ _ _ _ lt] using h j
  · by_cases eq : j = s.length
    · subst j; simpa [wire] using hv
    · rw [wire,List.getD_eq_default _ _ (show (s++[v]).length ≤ j by simp; omega)]; exact falseActs
private theorem beginClosed : Closed (List.ofFn poolWire) := by
  intro j
  by_cases lt : j < 33
  · rw [wire,List.getD_eq_getElem _ _ (show j < (List.ofFn poolWire).length by simpa using lt), List.getElem_ofFn]; exact rawActs ⟨j,lt⟩
  · rw [wire,List.getD_eq_default _ _ (show (List.ofFn poolWire).length ≤ j by simpa using Nat.le_of_not_gt lt)]; exact falseActs
private theorem start {s : List Column} (hs : Closed s) (k : Fin 8) : Count k s 0 := by
  intro W
  apply le_trans Finset.card_biUnion_le
  rw [Nat.zero_add,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨_,h⟩ := signature (hs j)
  exact repSmall h k
private theorem finish (k : Fin 8) (gs : List Gate) {s : List Column} (h : Count k s 0) (o : Nat)
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

private theorem andBlock (gs : List Gate) (hs : ∀ g ∈ gs, g.1 = true) {s : List Column}
    (hb : Closed s) : Closed (gs.foldl step s) := by
  induction gs generalizing s with
  | nil => exact hb
  | cons g gs ih =>
    obtain ⟨op,a,b⟩ := g
    have eq := hs (op,a,b) (by simp)
    change op = true at eq
    subst op
    exact ih (fun g hg => hs g (by simp [hg])) (appendActs hb _ (andActs (hb a) (hb b)))
end PEqualNP.Research.PlaneCase35FirstOrLines.OrCost

namespace PEqualNP.Research.PlaneCase35FirstOrLines.Ordinary
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

private def root (r : Nat) := fixed 2 r || fixed 6 r

private theorem extendsPool (pre : List G) (s : List Col) :
    ∃ vs : List Col, pre.foldl OrCost.step s = s ++ vs := by
  induction pre generalizing s with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨vs,h⟩ := ih (OrCost.step s g)
    let v := OrCost.mix g.1 (w s g.2.1) (w s g.2.2)
    have eq : OrCost.step s g = s ++ [v] := by
      cases e : g.1 <;> simp [OrCost.step,OrCost.addOr,OrCost.both,OrCost.mix,v,e,w] <;> rfl
    exact ⟨v::vs,h.trans (by rw [eq,List.append_assoc]; rfl)⟩
private theorem paidBound : ∀ (pre gs : List (Bool × Nat × Nat)) (o : Nat),
  let pool := pre.foldl OrCost.step (OrCost.step (List.ofFn fixed) (false,2,6))
  (∀ v ∈ pool.drop 33, ∀ p : Fin 52, (0x31b112b41c3af : Nat).testBit p.val = false → v p.val = false) →
  (∀ p : Fin 52, OrCost.wire (gs.foldl OrCost.step pool) o p.val = true) →
  (∀ j : Fin 468, OrCost.wire (gs.foldl OrCost.step pool) o (52+j.val) = false) →
  8 ≤ (gs.map (translate 0)).countP Prod.fst := by
  intro pre gs o pool quiet hp hn
  obtain ⟨vs,hvs⟩ := extendsPool pre (start (2,6))
  have e : pool = List.ofFn fixed ++ [root] ++ vs := hvs
  have drop : pool.drop 33 = vs := by
    rw [e,show 33 = (List.ofFn fixed ++ [root]).length by simp,List.drop_left]
  have dom (v : Col) (h : v ∈ root :: vs) (p : Fin 52)
      (_high : 4 ≤ p.val) (avoid : (0x31b112b41c3af : Nat).testBit p.val = false) (on : v p.val = true) :
      ∃ k : Fin 32, fixed k p.val = true ∧ ∀ j : Fin 468, fixed k (52+j.val) = true → v (52+j.val) = true := by
    rcases List.mem_cons.mp h with rfl | rest
    · rcases Bool.or_eq_true_iff.mp on with a | b
      · exact ⟨2,a,fun _ hit => Bool.or_eq_true_iff.mpr (Or.inl hit)⟩
      · exact ⟨6,b,fun _ hit => Bool.or_eq_true_iff.mpr (Or.inr hit)⟩
    · rw [←drop] at rest
      simp [quiet _ rest p avoid] at on
  have len : 32 < pool.length := by rw [e]; simp
  have read : w pool 32 = guards 0 := by
    rw [e]; exact (List.getD_append _ _ _ _ (by simp)).trans (by rfl)
  have sim := simulate 0 gs pool len read
  have eq : pool = List.ofFn fixed ++ (root::vs) := by simpa using e
  have ands := Guard.bound (root::vs) dom (gs.map (translate 0)) o
    (by simpa only [← eq,← sim,Guard.PlaneFirstAndSeparation.wire,OrCost.wire] using hp)
    (by simpa only [← eq,← sim,Guard.PlaneFirstAndSeparation.wire,OrCost.wire] using hn)
  exact ands
private abbrev block12 : List G := [(true,1,24),(true,15,32),(true,25,32),(true,0,17),(true,0,23)]
private abbrev block13 : List G := block12 ++ [(true,0,25)]
private def c8 (r : Nat) := fixed 1 r && fixed 24 r
private def c9 (r : Nat) := fixed 15 r && root r
private def c10 (r : Nat) := fixed 25 r && root r
private def c11 (r : Nat) := fixed 0 r && fixed 17 r
private def c12 (r : Nat) := fixed 0 r && fixed 23 r
private def c13 (r : Nat) := fixed 0 r && fixed 25 r
private theorem silentBlock : ∀ p : Fin 52, (0x31b112b41c3af : Nat).testBit p.val = false →
    c8 p.val = false ∧ c9 p.val = false ∧ c10 p.val = false ∧ c11 p.val = false ∧
    c12 p.val = false ∧ c13 p.val = false := by decide +kernel

private theorem startClosed : OrCost.Closed (start (2,6)) := by
  have e : start (2,6) = List.ofFn OrCost.poolWire := by rfl
  rw [e]
  exact OrCost.beginClosed

private abbrev initial := block13.foldl OrCost.step (start (2,6))
private theorem initClosed : OrCost.Closed initial :=
  OrCost.andBlock block13 (by decide) startClosed
theorem firstOrBound (pre : List G) (a b : Nat) (tail : List G) (o : Nat)
    (allAnd : ∀ g ∈ pre, g.1 = true)
    (other : ¬ OrCost.linePair (w (pre.foldl OrCost.step initial) a) (w (pre.foldl OrCost.step initial) b))
    (hp : ∀ p : Fin 52, w ((pre ++ (false,a,b)::tail).foldl OrCost.step initial) o p.val = true)
    (hn : ∀ j : Fin 468, w ((pre ++ (false,a,b)::tail).foldl OrCost.step initial) o (52+j.val) = false) :
    27 + (pre ++ (false,a,b)::tail).countP cheap ≤ (pre ++ (false,a,b)::tail).length := by
  let gs := pre ++ (false,a,b)::tail
  have closed := OrCost.andBlock pre allAnd initClosed
  obtain ⟨i,hi⟩ := OrCost.signature (closed a)
  obtain ⟨j,hj⟩ := OrCost.signature (closed b)
  obtain ⟨k,hk⟩ := OrCost.freeOr hi hj other
  let s := pre.foldl OrCost.step initial
  have eval : gs.foldl OrCost.step initial =
      tail.foldl OrCost.step (s ++ [OrCost.mix false (w s a) (w s b)]) := by
    dsimp only [gs]
    rw [List.foldl_append]
    rfl
  have hp' : ∀ p : Fin 52, w (gs.foldl OrCost.step initial) o p.val = true := hp
  have hn' : ∀ j : Fin 468, w (gs.foldl OrCost.step initial) o (52+j.val) = false := hn
  rw [eval] at hp' hn'
  have ors := OrCost.finish k tail (OrCost.addSmall k (OrCost.start closed k) _ hk) o hp' hn'
  have q : ∀ v ∈ initial.drop 33, ∀ p : Fin 52,
      (0x31b112b41c3af : Nat).testBit p.val = false → v p.val = false := by
    intro v hv p he
    change v ∈ [c8,c9,c10,c11,c12,c13] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    obtain ⟨u,v,w,x,y,z⟩ := silentBlock p he
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have ands := paidBound block13 gs o q hp hn
  have costs := splitCost 0 gs
  let nr : G → Bool := fun g => !g.1
  have ortotal : gs.countP nr = pre.countP nr + (tail.countP nr + 1) := by
    simp [gs,List.countP_append,List.countP_cons,nr]
  change 18 ≤ tail.countP nr at ors
  change gs.countP cheap + gs.countP nr + (gs.map (translate 0)).countP Prod.fst = gs.length at costs
  change 27 + gs.countP cheap ≤ gs.length
  omega
end PEqualNP.Research.PlaneCase35FirstOrLines.Ordinary
open PEqualNP.Research.PlaneCase35FirstOrLines in
theorem PEqualNP.Research.PlaneCase35FirstOrLines : ∀ (pre : List (Bool × Nat × Nat)) (a b : Nat) (tail : List (Bool × Nat × Nat)) (o : Nat),
  let s := pre.foldl OrCost.step Ordinary.initial
  let gs := pre ++ (false,a,b)::tail
  (∀ g ∈ pre, g.1 = true) →
  (¬ OrCost.linePair (OrCost.wire s a) (OrCost.wire s b)) →
  (∀ p : Fin 52, OrCost.wire (gs.foldl OrCost.step Ordinary.initial) o p.val = true) →
  (∀ j : Fin 468, OrCost.wire (gs.foldl OrCost.step Ordinary.initial) o (52+j.val) = false) →
  27 + gs.countP Ordinary.cheap ≤ gs.length := Ordinary.firstOrBound
