import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
set_option Elab.async false
namespace PEqualNP.Research.PlaneCase35GuardOmissionMaximum
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

def guard (r : Nat) := base 2 r || base 23 r
def compatible (K : Finset (Fin 468)) := ∀ i j : K, i.val < j.val →
    ∃ p : Fin 52, 4 ≤ p.val ∧ p.val ≠ 10 ∧
      (guard p.val = true → guard (52+i.val.val) = true ∧ guard (52+j.val.val) = true) ∧
      ∀ k : Fin 30, base k p.val = true → base k (52+i.val.val) = true ∨ base k (52+j.val.val) = true
set_option maxHeartbeats 0
set_option maxRecDepth 14000
private def col (k : Nat) := (0x4210413001a00c000e0000000000000000000000000024301102001c5000d0020400282800800050030001000000140015000010000202880024900000000008400084a800000000000000008c000b2990000000000890014b61000000000000000000000000000018c20000006524ff76feddb7ffd83dc55021fd547d6fa3bb7f6785e882ea5fe40bf6dd6d5001f621bf3176fe901c2000d8442000002d140800006fdd6a4040375240000001bdf8b6f5851fa8bac0d000e8000000defc5b7d8dfef58e01d3f3abb428a1f5400d203ffff6eefec8d27de9ff2d949bd07d460d51407504fffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffe0000000000000000000000003ffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000f800001fffff80000000000000000003fffff00000000000000000007ffffffffffffffffffc000000000000000000000000000000000000000000000001f00007ffffe00000000000003e0000fffffc00000000000007fffc000000000000003fffffffffffff800000000000000000000000000007c00010f000780001fff0000000000000000f80003fffe00000000078003ffff00000000003ffe00000000007fffffffffe00000000000000000803c00000f0007c000000fff800000001e000878003c001ff000000000003e000fff80000003c01fff00000007ffc0000001fffffff0000000000440380088880043801c00e007f80000201c000078003c0000ffc0000070021c00e007f800000001e00ffc00007803ff00001ff80000fffff80000200270040070002700000000707ff001103004444002381c0c03e00040c0003c01e0007f00003811c0c03e0000003c0ffc01e07fe00fe0007fe0002004e0000004210c13001e04c700f00802e02003800260000031fe024301122011c7060f8020400383801f00070230c038000781f8e1fe0781f800000000440e0000008e09180b4f0cf00809c0000021119303c2dc1e102e080180120000c7c123092427398f840800c38060184610401c1e679860020298202492100302980840008ca880000002207000008ca30b3998209800008894c1cb63882c40204800c724612a2735d04018c2193110677511100440202490048c006053002421640105210124908042a108025500000090600023522db410a00092646b69058810481a93254b7840cc9546f00890120000000822a055402a282905c448090101248052010a409228085440954408a89016c000091001352d821400926b6429022952aabc8adb00000000000000000000000000000000000000000000000000000000000037fe7fedffff383c00000000000003f7ff3c7f9fe7b9efbfe3e19867900000000000006ffce000f7bfff7357400000000000000000000000000000000000000000000001bfdfb7ff3880000000000fbfe73de6ceef988a06c3fba00000000001ff90007fdbde980000000000037fa00ef7fdaa80000000000000000000000000000000000037efb7e400000007bf336ab90b8347ec0077f8000000001fd007d6fa01a3f60000000001fe003f6dd0000000001bf0076fe90000000000000000000000000006fdd6000003752400000000000000000000000000000002e1cff003bfc0000003fc1fff873fc00000007f80fffc0000003fc1fff80000000000000000001fff801ff00000017707fb8073e0ff000000ff0fc00000000000000000000000058cfc01df000001f07fc3be000003e0ff8000003fc7e00000000000007e0703fc0fe000007bc0fe31f0e78000030c00000bb83fdc0660f00003e180000000000000000002c4e01b0000707877c000039e00000fb0000000079dddd8060fd86800000c67e1b838000740fc1f000003dc1e331cc000600002ec1f602838001c40000000000000589c05000221b800050000e80002e82fb1af0bd105eb32000604b080d00b76d0107ec340000c5c34200083c1c0000ee18c8d00080016c34082001000000000016480a001a001002007f42d65db0b0d83dc550200054302103a1762785e882ea40040900406d5001f62000316208001c2000d8442000002d1408000000000a40401000000000000000000000000000000000001fe3aded8586c3fb510034c2278f65e2f9176802140436d01fd001b908038400d84a0005a30800000688800000001bdf8b6f5851fa8bac0d000e800000000000000000000000003f3abb428a1f5400d203c74e2e2d808406da03e001400c0014001510001000000000000000000000000000000000000000defc5b7d8dfef58e01d00000000000000000001fbff46c7ec0d278e9cf2d849bd07c060c01407404 >>> (468*k)) &&& 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
private def key (k : Nat) := (0x6332c4232810b2206b206330c5af0b39f070eb015aeeb52aea31ae606ae0632cc52aca4eec9296c55aeab4eea9422a8212a452a8a4228839e871ee834ee6939e6731a6610a624224831a46296450ea4139e272962521224eea206320c31a06212041ee035adeb295e5e6de3109e2529ca211c4109c20e9c14eda91eda30e9a1069a0 >>> (5*k)) &&& 0x1f
private def removed : Nat := 0x52ed512bbbffeac3282fc50a22434040c5809336b79b250ac8f69bde038506c97d407f983d3492d890383166d6e1ff8b7b5866fc8f0f0e8850326
private def full := (2:Nat)^468-1
private def side (i k : Nat) := if (col k).testBit i then full else col k
private def cov (i p : Nat) := side i (key (4*p)) &&& side i (key (4*p+1)) &&&
  side i (key (4*p+2)) &&& side i (key (4*p+3))
private def safe (p : Nat) := (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880f800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880f800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880f800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800001fffff80000000000000000003fffffed8586c3fb510034c227fffffffffffffffffff6d01fd001b908038400d84a0005a3080000068880fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >>> (468*p)) &&& full
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
private theorem ecard : (indexed removed).card = 224 := by decide +kernel
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
private theorem subsetGuard : ∀ p : Fin 52, guard p.val = true →
    safe p.val &&& (col 2 ||| col 23) = safe p.val := by decide +kernel
private theorem safeGuard (p : Fin 52) (i : Fin 468) (hit : (safe p.val).testBit i.val = true)
    (g : guard p.val = true) : guard (52+i.val) = true := by
  have eq := congrArg (fun x : Nat => x.testBit i.val) (subsetGuard p g)
  simpa [Nat.testBit_and,Nat.testBit_or,hit,guard,←colOK (2 : Fin 30) i,←colOK (23 : Fin 30) i] using eq
private theorem existsFamily : ∃ K : Finset (Fin 468), compatible K ∧ K.card = 244 := by
  let K := Finset.univ \ indexed removed
  refine ⟨K,?_,?_⟩
  · intro i j lt
    obtain ⟨p,high,hit,hjt,pass⟩ := sound i.val j.val lt (Finset.mem_sdiff.mp i.property).2 (Finset.mem_sdiff.mp j.property).2
    have ne : p.val ≠ 10 := by
      intro eq
      rw [eq, show safe 10 = 0 by decide +kernel] at hit
      simpa using hit
    exact ⟨p,high,ne,fun h => ⟨safeGuard p i.val hit h,safeGuard p j.val hjt h⟩,pass⟩
  · dsimp only [K]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [ecard]
private def pw (i : Nat) := (0x80040002000100080000106000001040040001000800040002005000002020020000800400020001004800001010040000400400210008000400020008020008200200008004000200010004010000100100004002008100008202008000080080002001000080004001004000040040001000804040002000802000020020000800424020001000440000010040000400408010008000220000008020600200200008004000110000004010000100104004002200088008002008100080084002001 >>> (30*i)) &&& 1073741823
private def addressAt (i : Nat) := (0xb4765ac4571ad56c9d25ac724e46d15a6b43682cd595b28d0ec741bb055f2bb566acb5c2b255aa774ba8f5119ff3d6774e99b92f25bcab90f1aa31c5d87f0ea19c2d84ea3eacd5eab15492a54c484906a3540a754d1001ffa5148a8ed1ca2f45a8850aa093fa7ccf89e93ce794e89cf3b6764e69c136e6d0e59a933a644c25a32da58cb09552924fc9e93124a46c8c90c1d24047a8e91b8250498d31a23145c8ad1422544487d0e61c432859099f23f07d6f85f03846f0db5b634f698d2e1041a63ccad9830e632c620a2fb81d02202403804ff1fc3f77ecf65efbea7bcf61eb3d57a8f4de73cd7a4f31e33c2782f01d539e774ed1d4bae750e8dd139d738e59c838a6fedf9b9b726ced85b33606b6d6984b54610c1da534969cd219f34267acf19b315628c4d80b2664aca99230d624c31833005f4a697a2884fa8a10c2175debb9172233b4758ea9c33846f5751aa360b757198c2ea5ecc99622be578c414b2944f09d93f246488909031f83e07bad61bc365682ca22a2904f0971022003d0790fe1b03384307a0f1620370600ac1001902603d5f00e01a01c01802570005592ac54ea9950295528a3941a824ee9f13b26049a9c1352644be9792c2534a4931232404748d0f7211444870fc1f242c8410620b414810ff1ed3d87a0f39e63c0750e81cf39c724e41bc36c67d74adc5d0698d29a433c66d7119a332660b91713245c0c3986302600bd1742de5b8b51692d0574ac1572b8558a91512a0514a213a2724f89c13221c3b07592c24c4808d91a228428798f21e2424841021ec3c0750e418e3606a0d31a4330630c016a188308bb1742d0570a804c094518a213a2704b0901162284207e0f01cc390660c01682a04e0901081b02a04807c0f01802403003000 >>> (11*i)) &&& 2047
private def members : Array Nat := #[0x3a9d454aa14c00, 0x3a9d4ea7515401, 0x3a9d4572b15602, 0x3a9d4ea7515e03, 0x3a9d4ea7516004, 0x3a9d4ea2c40c05, 0x3a9d4ea07c3c07, 0x3a9d4ea7516408, 0x3a9d4ea753a8b3, 0x3a9d4ea7516809, 0x3a9d4ea7516eb6, 0x3a9d4ea751700a, 0x3a9d4ea596c80b, 0x3a9d4ea753a80c, 0x3a9d4ea753a80d, 0x3a9d4ea753a80e, 0x3a9d4ea0984a0f, 0x3a9d4ea7517210, 0x3a9d4ea753a8ba, 0x3a9d4ea5a82411, 0x3a9d4ea2f57813, 0x3a9d45faf97614, 0x3a9d4ea753a815, 0x3a9d4ea7502e16, 0x3a9d4ea753a818, 0x3a9d4ea7518019, 0x3a9d4ea304361a, 0x3a9d4ea3083a1c, 0x3a9d4ea753a820, 0x3a9d4ea753a821, 0x3a9d4ea7504e22, 0x3a9d4ea7504823, 0x3a9d4ea753a828, 0x3a9d4ea7505e29, 0x3a9d4ea753a82a, 0x3a9d4ea0b4582b, 0x3a9d4ea7518c2e, 0x3a9d4ea753a8c7, 0x3a9d4ea752f830, 0x3a9d4ea1088231, 0x3a9d41c8e06e32, 0x3a9d4ea3299233, 0x3a9d4ea753a8cb, 0x3a9d4ea7519834, 0x3a9d4ea0e86c35, 0x3a9d4ea753a843, 0x3a9d4ea751863b, 0x3a9d4ea7507a3c, 0x3a9d467b399a3e, 0x3a9d4ea753a83f, 0x3a9d4ea753a840, 0x3a9d4ea753a844, 0x3a8d2689208e45, 0x3a9d4ea751a046, 0x3a9d4ea7509449, 0x3a9d4ea751a8d3, 0x3a9d4ea134984b, 0x3a9d4ea144a04e, 0x3a9d46bb58a44f, 0x3a9d4ea753a8d8, 0x3a9d4ea154a853, 0x3a86130178ae56, 0x3a9d4ea751b658, 0x3a9d4ea751b459, 0x3a9d4ea750b65a, 0x3a9d4ea354ba5c, 0x3a9d4ea753a8dc, 0x3a9d4ea751b25f, 0x3a9d433190c662, 0x3a9d4ea750dc67, 0x3a9d4ea1a8d268, 0x3a9d4ea753a8e0, 0x3a9d4ea753a8df, 0x3a9d4ea753a86f, 0x3a9d4ea751c470, 0x3a9d4ea751c8e3, 0x3a9d4ea750e471, 0x3a9d4ea1d4e873, 0x3a9d4ea399ca76, 0x3a9d4ea753a8e7, 0x3a9d4ea753a877, 0x3a9d4ea1e8f278, 0x3a9d4ea224f87b, 0x3a9d4ea753a884, 0x3a9d4ea753a885, 0x3a9d4ea657287d, 0x3a9d4ea753a87e, 0x3a9d4ea205007f, 0x3a9d4ea7511082, 0x3a9d4ea3b5d883, 0x3a9d4ea753a886, 0x3a9d4ea751d087, 0x3a9d4ea753a8ee, 0x3a9d4ea753a8e9, 0x3a9d4ea753a88a, 0x3a9d4ea753a88b, 0x3a9d4ea66f348c, 0x3a9d4ea753a88d, 0x3a9d4ea7512e8e, 0x3a9d4ea675208f, 0x3a9d4ea753a891, 0x3a9d4ea2612692, 0x3a9d4ea753a894, 0x3a9d4ea753a895, 0x3a9d4ea753a896, 0x3a9d4ea7513699, 0x3a9d4ea751de9a, 0x3a9d4ea7513a9c, 0x3a9d4ea753a8f0, 0x3a9d4ea753449e, 0x3a9d4ea751409f, 0x3a9d4ea753a8f2, 0x3a9d4ea753a8a1, 0x3a9d4ea75146a2, 0x3a9d4ea753a8a4, 0x3a9d4ea753a8a5, 0x3a9d4ea753a8a7, 0x3a9d4ea753a8ad, 0x3a9d4ea753a8b5, 0x3a9d4ea753a8c4, 0x3a9d4ea752eec5, 0x3a9d4ea753a8c8, 0x3a9d4ea751bc6c, 0x3a9d4ea751ba65, 0x3a9d4ea384da6b, 0x3a9d4ea751d6ea, 0x3a9d4ea753a8f1, 0x3a9d4ea75280f3, 0x3a9d4ea751faf4, 0x3a9d486c2e14f5, 0x3a9d4ea511f0f6, 0x3a9d4803fdfcf7, 0x3a9d4ea7528742, 0x3a9d4ea753a947, 0x3a9d4ea3f1f6f9, 0x3a9d4ea7528cfa, 0x3a9d4ea753a945, 0x3a9d4ea753a901, 0x3a9d4ea4160702, 0x3a9d4ea7538504, 0x3a94ba54261106, 0x3a9d4ea7529907, 0x3a9d4ea753a90c, 0x3a9d4ea7521f0e, 0x3a9d4ea7522510, 0x3a9d4ea7522711, 0x3a9d4ea7529d4d, 0x3a9d4ea7522b14, 0x3a9d4ea753a94f, 0x3a9d4ea7522f16, 0x3a9d4ea753a950, 0x3a9d4ea753a918, 0x3a9d4ea72f9519, 0x3a9d4ea753a91a, 0x3a9d4ea492391b, 0x3a9d4ea7363d1d, 0x3a9d4ea496431f, 0x3a9d4ea753a920, 0x3a9d4ea753a922, 0x3a9d4ea753a923, 0x3a9d4ea4a24f26, 0x3a9d4ea753a929, 0x3a9d4ea4b6592a, 0x3a931984be5d2b, 0x3a9d4ea7526d32, 0x3a9d4a95466b33, 0x3a9d4ea753a955, 0x3a9d4ea752a734, 0x3a9d4ea753a954, 0x3a9d4ea4e67137, 0x3a9d4ea753a93a, 0x3a9d4ea4f6793b, 0x3a9d4ea753a93e, 0x3a9d4ea753a93f, 0x3a9d4ea753a941, 0x3a9d4ea7538148, 0x3a9d4ea753a949, 0x3a9d4ea7534756, 0x3a9d4ea7534957, 0x3a9d4ea7534b58, 0x3a9d4ea69ab559, 0x3a9d4ea7534f5b, 0x3a9d4ea753a95c, 0x3a9d4ea753a95d, 0x3a9d4ea753a95e, 0x3a9d4ea753a95f, 0x3a9d4ea7535160, 0x3a9d4ea7535361, 0x3a9d4ea6aac762, 0x3a9d4ea753a966, 0x3a9d4ea753a967, 0x3a9d4ea753a968, 0x3a9d4ea753a969, 0x3a9d4ea753576b, 0x3a9d4ea752db6c, 0x3a9d4ea753a96e, 0x3a9d4ea753a96f, 0x3a9d4ea752e370, 0x3a9d4ea753a972, 0x3a9d4ea7535973, 0x3a9d4ea752eb74, 0x3a9d4ea7535b76, 0x3a9d4ea753a9ae, 0x3a9d4ea753a978, 0x3a9d4ea753a979, 0x3a9d4ea753a97a, 0x3a9d4ea753a97b, 0x3a9d4ea6befd7d, 0x3a9d4ea753a97f, 0x3a9d4d86130780, 0x3a9d4ea6c70581, 0x3a9d4d961f0d85, 0x3a9d4ea7531388, 0x3a9d4ea753678a, 0x3a9d4ea753a98b, 0x3a9d4ea753a98c, 0x3a9d4ea753698d, 0x3a9d4ea7531f8e, 0x3a9d4ea6d72390, 0x3a9d4ea753a992, 0x3a9d4ea753a993, 0x3a9d4ea753a9b6, 0x3a9d4ea753a996, 0x3a9d4ea7536f97, 0x3a9d4ea753a998, 0x3a9d4ea753a999, 0x3a9d4ea753a99c, 0x3a9d4ea753a99e, 0x3a9d4ea6e3439f, 0x3a9d4ea753a9a0, 0x3a9d4ea6f377b9, 0x3a9d4ea753a9cf, 0x3a9d4ea753a1ba, 0x3a9d4ea753a9bd, 0x3a9d4ea753a9be, 0x3a9d4ea753a9bf, 0x3a9d4ea753a9d1, 0x3a9d4ea753a9c1, 0x3a9d4ea74b89c3, 0x3a9d4ea753a9c5, 0x3a9d4e9f278fc6, 0x3a9d4ea753a9c8, 0x3a9d4ea753a9cc, 0x3a9d4ea753a9ce]
private def color (i : Fin 468) : Fin 244 := Fin.ofNat 244 ((addressAt (i.val)) / 6)
private def slot (i : Fin 468) : Fin 6 := Fin.ofNat 6 ((addressAt (i.val)) % 6)
private def member (c : Fin 244) (k : Fin 6) := (members[c.val]! >>> (9*k.val)) &&& 511
private theorem recover : ∀ i : Fin 468, member (color i) (slot i) = i.val := by decide +kernel
private theorem small : ∀ p : Fin 52, (pw (p.val)) < 2^30 := by decide +kernel
private theorem posOK : ∀ (p : Fin 52) (k : Fin 30), base k p.val = (pw (p.val)).testBit k.val := by decide +kernel
private def nOK (v : Nat) : Prop := ∀ k : Fin 30, base k (52+v) = (nw (v)).testBit k.val
private theorem ns0 : ∀ t : Fin 12, nOK (12*0+t.val) := by unfold nOK; decide +kernel
private theorem ns1 : ∀ t : Fin 12, nOK (12*1+t.val) := by unfold nOK; decide +kernel
private theorem ns2 : ∀ t : Fin 12, nOK (12*2+t.val) := by unfold nOK; decide +kernel
private theorem ns3 : ∀ t : Fin 12, nOK (12*3+t.val) := by unfold nOK; decide +kernel
private theorem ns4 : ∀ t : Fin 12, nOK (12*4+t.val) := by unfold nOK; decide +kernel
private theorem ns5 : ∀ t : Fin 12, nOK (12*5+t.val) := by unfold nOK; decide +kernel
private theorem ns6 : ∀ t : Fin 12, nOK (12*6+t.val) := by unfold nOK; decide +kernel
private theorem ns7 : ∀ t : Fin 12, nOK (12*7+t.val) := by unfold nOK; decide +kernel
private theorem ns8 : ∀ t : Fin 12, nOK (12*8+t.val) := by unfold nOK; decide +kernel
private theorem ns9 : ∀ t : Fin 12, nOK (12*9+t.val) := by unfold nOK; decide +kernel
private theorem ns10 : ∀ t : Fin 12, nOK (12*10+t.val) := by unfold nOK; decide +kernel
private theorem ns11 : ∀ t : Fin 12, nOK (12*11+t.val) := by unfold nOK; decide +kernel
private theorem ns12 : ∀ t : Fin 12, nOK (12*12+t.val) := by unfold nOK; decide +kernel
private theorem ns13 : ∀ t : Fin 12, nOK (12*13+t.val) := by unfold nOK; decide +kernel
private theorem ns14 : ∀ t : Fin 12, nOK (12*14+t.val) := by unfold nOK; decide +kernel
private theorem ns15 : ∀ t : Fin 12, nOK (12*15+t.val) := by unfold nOK; decide +kernel
private theorem ns16 : ∀ t : Fin 12, nOK (12*16+t.val) := by unfold nOK; decide +kernel
private theorem ns17 : ∀ t : Fin 12, nOK (12*17+t.val) := by unfold nOK; decide +kernel
private theorem ns18 : ∀ t : Fin 12, nOK (12*18+t.val) := by unfold nOK; decide +kernel
private theorem ns19 : ∀ t : Fin 12, nOK (12*19+t.val) := by unfold nOK; decide +kernel
private theorem ns20 : ∀ t : Fin 12, nOK (12*20+t.val) := by unfold nOK; decide +kernel
private theorem ns21 : ∀ t : Fin 12, nOK (12*21+t.val) := by unfold nOK; decide +kernel
private theorem ns22 : ∀ t : Fin 12, nOK (12*22+t.val) := by unfold nOK; decide +kernel
private theorem ns23 : ∀ t : Fin 12, nOK (12*23+t.val) := by unfold nOK; decide +kernel
private theorem ns24 : ∀ t : Fin 12, nOK (12*24+t.val) := by unfold nOK; decide +kernel
private theorem ns25 : ∀ t : Fin 12, nOK (12*25+t.val) := by unfold nOK; decide +kernel
private theorem ns26 : ∀ t : Fin 12, nOK (12*26+t.val) := by unfold nOK; decide +kernel
private theorem ns27 : ∀ t : Fin 12, nOK (12*27+t.val) := by unfold nOK; decide +kernel
private theorem ns28 : ∀ t : Fin 12, nOK (12*28+t.val) := by unfold nOK; decide +kernel
private theorem ns29 : ∀ t : Fin 12, nOK (12*29+t.val) := by unfold nOK; decide +kernel
private theorem ns30 : ∀ t : Fin 12, nOK (12*30+t.val) := by unfold nOK; decide +kernel
private theorem ns31 : ∀ t : Fin 12, nOK (12*31+t.val) := by unfold nOK; decide +kernel
private theorem ns32 : ∀ t : Fin 12, nOK (12*32+t.val) := by unfold nOK; decide +kernel
private theorem ns33 : ∀ t : Fin 12, nOK (12*33+t.val) := by unfold nOK; decide +kernel
private theorem ns34 : ∀ t : Fin 12, nOK (12*34+t.val) := by unfold nOK; decide +kernel
private theorem ns35 : ∀ t : Fin 12, nOK (12*35+t.val) := by unfold nOK; decide +kernel
private theorem ns36 : ∀ t : Fin 12, nOK (12*36+t.val) := by unfold nOK; decide +kernel
private theorem ns37 : ∀ t : Fin 12, nOK (12*37+t.val) := by unfold nOK; decide +kernel
private theorem ns38 : ∀ t : Fin 12, nOK (12*38+t.val) := by unfold nOK; decide +kernel
private theorem negOK (i : Fin 468) : nOK i.val := by
  have batches (a : Fin 39) (b : Fin 12) : nOK (12*a.val+b.val) := by
    match a with
    | ⟨0,_⟩ => exact ns0 b
    | ⟨1,_⟩ => exact ns1 b
    | ⟨2,_⟩ => exact ns2 b
    | ⟨3,_⟩ => exact ns3 b
    | ⟨4,_⟩ => exact ns4 b
    | ⟨5,_⟩ => exact ns5 b
    | ⟨6,_⟩ => exact ns6 b
    | ⟨7,_⟩ => exact ns7 b
    | ⟨8,_⟩ => exact ns8 b
    | ⟨9,_⟩ => exact ns9 b
    | ⟨10,_⟩ => exact ns10 b
    | ⟨11,_⟩ => exact ns11 b
    | ⟨12,_⟩ => exact ns12 b
    | ⟨13,_⟩ => exact ns13 b
    | ⟨14,_⟩ => exact ns14 b
    | ⟨15,_⟩ => exact ns15 b
    | ⟨16,_⟩ => exact ns16 b
    | ⟨17,_⟩ => exact ns17 b
    | ⟨18,_⟩ => exact ns18 b
    | ⟨19,_⟩ => exact ns19 b
    | ⟨20,_⟩ => exact ns20 b
    | ⟨21,_⟩ => exact ns21 b
    | ⟨22,_⟩ => exact ns22 b
    | ⟨23,_⟩ => exact ns23 b
    | ⟨24,_⟩ => exact ns24 b
    | ⟨25,_⟩ => exact ns25 b
    | ⟨26,_⟩ => exact ns26 b
    | ⟨27,_⟩ => exact ns27 b
    | ⟨28,_⟩ => exact ns28 b
    | ⟨29,_⟩ => exact ns29 b
    | ⟨30,_⟩ => exact ns30 b
    | ⟨31,_⟩ => exact ns31 b
    | ⟨32,_⟩ => exact ns32 b
    | ⟨33,_⟩ => exact ns33 b
    | ⟨34,_⟩ => exact ns34 b
    | ⟨35,_⟩ => exact ns35 b
    | ⟨36,_⟩ => exact ns36 b
    | ⟨37,_⟩ => exact ns37 b
    | ⟨38,_⟩ => exact ns38 b
    | ⟨v+39,h⟩ => omega
  have h := batches ⟨i.val/12,by omega⟩ ⟨i.val%12,by omega⟩
  simpa only [Nat.div_add_mod] using h

private theorem subsetBits (i j : Fin 468) (p : Fin 52)
    (pass : ∀ k : Fin 30, base k p.val = true →
      base k (52+i.val) = true ∨ base k (52+j.val) = true) :
    (pw (p.val)) &&& ((nw (i.val)) ||| (nw (j.val))) = (pw (p.val)) := by
  apply Nat.eq_of_testBit_eq
  intro h
  rw [Nat.testBit_and,Nat.testBit_or]
  by_cases pos : (pw (p.val)).testBit h = true
  · have bound : h < 30 := by
      by_contra! le
      have e := Nat.testBit_lt_two_pow ((small p).trans_le (Nat.pow_le_pow_right (by decide) le))
      simp [pos] at e
    let k : Fin 30 := ⟨h,bound⟩
    have on : base k p.val = true := (posOK p k).trans pos
    rcases pass k on with left | right
    · have off : (nw (i.val)).testBit h = true := (negOK i k).symm.trans left
      simp [pos,off]
    · have off : (nw (j.val)).testBit h = true := (negOK j k).symm.trans right
      simp [pos,off]
  · cases e : (pw (p.val)).testBit h <;> simp_all
private def bitGuard (x : Nat) := x.testBit 2 || x.testBit 23
private theorem posGauge (p : Fin 52) : guard p.val = bitGuard (pw p.val) := by
  exact congrArg₂ (· || ·) (posOK p 2) (posOK p 23)
private theorem negGauge (j : Fin 468) : guard (52+j.val) = bitGuard (nw j.val) := by
  exact congrArg₂ (· || ·) (negOK j 2) (negOK j 23)
private def absent (g : Nat) : Prop := ∀ u v : Fin 6,
  let i := member (Fin.ofNat 244 g) u
  let j := member (Fin.ofNat 244 g) v
  i < j → j < 468 → ∀ p : Fin 52, 4 ≤ p.val → p.val ≠ 10 →
    (bitGuard (pw p.val) = true → bitGuard (nw i) = true ∧ bitGuard (nw j) = true) →
    pw p.val &&& (nw i ||| nw j) ≠ pw p.val
private theorem block0 : ∀ t : Fin 4, absent (4*0+t.val) := by unfold absent; decide +kernel
private theorem block1 : ∀ t : Fin 4, absent (4*1+t.val) := by unfold absent; decide +kernel
private theorem block2 : ∀ t : Fin 4, absent (4*2+t.val) := by unfold absent; decide +kernel
private theorem block3 : ∀ t : Fin 4, absent (4*3+t.val) := by unfold absent; decide +kernel
private theorem block4 : ∀ t : Fin 4, absent (4*4+t.val) := by unfold absent; decide +kernel
private theorem block5 : ∀ t : Fin 4, absent (4*5+t.val) := by unfold absent; decide +kernel
private theorem block6 : ∀ t : Fin 4, absent (4*6+t.val) := by unfold absent; decide +kernel
private theorem block7 : ∀ t : Fin 4, absent (4*7+t.val) := by unfold absent; decide +kernel
private theorem block8 : ∀ t : Fin 4, absent (4*8+t.val) := by unfold absent; decide +kernel
private theorem block9 : ∀ t : Fin 4, absent (4*9+t.val) := by unfold absent; decide +kernel
private theorem block10 : ∀ t : Fin 4, absent (4*10+t.val) := by unfold absent; decide +kernel
private theorem block11 : ∀ t : Fin 4, absent (4*11+t.val) := by unfold absent; decide +kernel
private theorem block12 : ∀ t : Fin 4, absent (4*12+t.val) := by unfold absent; decide +kernel
private theorem block13 : ∀ t : Fin 4, absent (4*13+t.val) := by unfold absent; decide +kernel
private theorem block14 : ∀ t : Fin 4, absent (4*14+t.val) := by unfold absent; decide +kernel
private theorem block15 : ∀ t : Fin 4, absent (4*15+t.val) := by unfold absent; decide +kernel
private theorem block16 : ∀ t : Fin 4, absent (4*16+t.val) := by unfold absent; decide +kernel
private theorem block17 : ∀ t : Fin 4, absent (4*17+t.val) := by unfold absent; decide +kernel
private theorem block18 : ∀ t : Fin 4, absent (4*18+t.val) := by unfold absent; decide +kernel
private theorem block19 : ∀ t : Fin 4, absent (4*19+t.val) := by unfold absent; decide +kernel
private theorem block20 : ∀ t : Fin 4, absent (4*20+t.val) := by unfold absent; decide +kernel
private theorem block21 : ∀ t : Fin 4, absent (4*21+t.val) := by unfold absent; decide +kernel
private theorem block22 : ∀ t : Fin 4, absent (4*22+t.val) := by unfold absent; decide +kernel
private theorem block23 : ∀ t : Fin 4, absent (4*23+t.val) := by unfold absent; decide +kernel
private theorem block24 : ∀ t : Fin 4, absent (4*24+t.val) := by unfold absent; decide +kernel
private theorem block25 : ∀ t : Fin 4, absent (4*25+t.val) := by unfold absent; decide +kernel
private theorem block26 : ∀ t : Fin 4, absent (4*26+t.val) := by unfold absent; decide +kernel
private theorem block27 : ∀ t : Fin 4, absent (4*27+t.val) := by unfold absent; decide +kernel
private theorem block28 : ∀ t : Fin 4, absent (4*28+t.val) := by unfold absent; decide +kernel
private theorem block29 : ∀ t : Fin 4, absent (4*29+t.val) := by unfold absent; decide +kernel
private theorem block30 : ∀ t : Fin 4, absent (4*30+t.val) := by unfold absent; decide +kernel
private theorem block31 : ∀ t : Fin 4, absent (4*31+t.val) := by unfold absent; decide +kernel
private theorem block32 : ∀ t : Fin 4, absent (4*32+t.val) := by unfold absent; decide +kernel
private theorem block33 : ∀ t : Fin 4, absent (4*33+t.val) := by unfold absent; decide +kernel
private theorem block34 : ∀ t : Fin 4, absent (4*34+t.val) := by unfold absent; decide +kernel
private theorem block35 : ∀ t : Fin 4, absent (4*35+t.val) := by unfold absent; decide +kernel
private theorem block36 : ∀ t : Fin 4, absent (4*36+t.val) := by unfold absent; decide +kernel
private theorem block37 : ∀ t : Fin 4, absent (4*37+t.val) := by unfold absent; decide +kernel
private theorem block38 : ∀ t : Fin 4, absent (4*38+t.val) := by unfold absent; decide +kernel
private theorem block39 : ∀ t : Fin 4, absent (4*39+t.val) := by unfold absent; decide +kernel
private theorem block40 : ∀ t : Fin 4, absent (4*40+t.val) := by unfold absent; decide +kernel
private theorem block41 : ∀ t : Fin 4, absent (4*41+t.val) := by unfold absent; decide +kernel
private theorem block42 : ∀ t : Fin 4, absent (4*42+t.val) := by unfold absent; decide +kernel
private theorem block43 : ∀ t : Fin 4, absent (4*43+t.val) := by unfold absent; decide +kernel
private theorem block44 : ∀ t : Fin 4, absent (4*44+t.val) := by unfold absent; decide +kernel
private theorem block45 : ∀ t : Fin 4, absent (4*45+t.val) := by unfold absent; decide +kernel
private theorem block46 : ∀ t : Fin 4, absent (4*46+t.val) := by unfold absent; decide +kernel
private theorem block47 : ∀ t : Fin 4, absent (4*47+t.val) := by unfold absent; decide +kernel
private theorem block48 : ∀ t : Fin 4, absent (4*48+t.val) := by unfold absent; decide +kernel
private theorem block49 : ∀ t : Fin 4, absent (4*49+t.val) := by unfold absent; decide +kernel
private theorem block50 : ∀ t : Fin 4, absent (4*50+t.val) := by unfold absent; decide +kernel
private theorem block51 : ∀ t : Fin 4, absent (4*51+t.val) := by unfold absent; decide +kernel
private theorem block52 : ∀ t : Fin 4, absent (4*52+t.val) := by unfold absent; decide +kernel
private theorem block53 : ∀ t : Fin 4, absent (4*53+t.val) := by unfold absent; decide +kernel
private theorem block54 : ∀ t : Fin 4, absent (4*54+t.val) := by unfold absent; decide +kernel
private theorem block55 : ∀ t : Fin 4, absent (4*55+t.val) := by unfold absent; decide +kernel
private theorem block56 : ∀ t : Fin 4, absent (4*56+t.val) := by unfold absent; decide +kernel
private theorem block57 : ∀ t : Fin 4, absent (4*57+t.val) := by unfold absent; decide +kernel
private theorem block58 : ∀ t : Fin 4, absent (4*58+t.val) := by unfold absent; decide +kernel
private theorem block59 : ∀ t : Fin 4, absent (4*59+t.val) := by unfold absent; decide +kernel
private theorem block60 : ∀ t : Fin 4, absent (4*60+t.val) := by unfold absent; decide +kernel
private theorem allRows (g : Fin 244) : absent g.val := by
  have blocks : ∀ (a : Fin 61) (b : Fin 4), absent (4*a.val+b.val) := by
    intro a b
    match a with
    | ⟨0,_⟩ => exact block0 b
    | ⟨1,_⟩ => exact block1 b
    | ⟨2,_⟩ => exact block2 b
    | ⟨3,_⟩ => exact block3 b
    | ⟨4,_⟩ => exact block4 b
    | ⟨5,_⟩ => exact block5 b
    | ⟨6,_⟩ => exact block6 b
    | ⟨7,_⟩ => exact block7 b
    | ⟨8,_⟩ => exact block8 b
    | ⟨9,_⟩ => exact block9 b
    | ⟨10,_⟩ => exact block10 b
    | ⟨11,_⟩ => exact block11 b
    | ⟨12,_⟩ => exact block12 b
    | ⟨13,_⟩ => exact block13 b
    | ⟨14,_⟩ => exact block14 b
    | ⟨15,_⟩ => exact block15 b
    | ⟨16,_⟩ => exact block16 b
    | ⟨17,_⟩ => exact block17 b
    | ⟨18,_⟩ => exact block18 b
    | ⟨19,_⟩ => exact block19 b
    | ⟨20,_⟩ => exact block20 b
    | ⟨21,_⟩ => exact block21 b
    | ⟨22,_⟩ => exact block22 b
    | ⟨23,_⟩ => exact block23 b
    | ⟨24,_⟩ => exact block24 b
    | ⟨25,_⟩ => exact block25 b
    | ⟨26,_⟩ => exact block26 b
    | ⟨27,_⟩ => exact block27 b
    | ⟨28,_⟩ => exact block28 b
    | ⟨29,_⟩ => exact block29 b
    | ⟨30,_⟩ => exact block30 b
    | ⟨31,_⟩ => exact block31 b
    | ⟨32,_⟩ => exact block32 b
    | ⟨33,_⟩ => exact block33 b
    | ⟨34,_⟩ => exact block34 b
    | ⟨35,_⟩ => exact block35 b
    | ⟨36,_⟩ => exact block36 b
    | ⟨37,_⟩ => exact block37 b
    | ⟨38,_⟩ => exact block38 b
    | ⟨39,_⟩ => exact block39 b
    | ⟨40,_⟩ => exact block40 b
    | ⟨41,_⟩ => exact block41 b
    | ⟨42,_⟩ => exact block42 b
    | ⟨43,_⟩ => exact block43 b
    | ⟨44,_⟩ => exact block44 b
    | ⟨45,_⟩ => exact block45 b
    | ⟨46,_⟩ => exact block46 b
    | ⟨47,_⟩ => exact block47 b
    | ⟨48,_⟩ => exact block48 b
    | ⟨49,_⟩ => exact block49 b
    | ⟨50,_⟩ => exact block50 b
    | ⟨51,_⟩ => exact block51 b
    | ⟨52,_⟩ => exact block52 b
    | ⟨53,_⟩ => exact block53 b
    | ⟨54,_⟩ => exact block54 b
    | ⟨55,_⟩ => exact block55 b
    | ⟨56,_⟩ => exact block56 b
    | ⟨57,_⟩ => exact block57 b
    | ⟨58,_⟩ => exact block58 b
    | ⟨59,_⟩ => exact block59 b
    | ⟨60,_⟩ => exact block60 b
    | ⟨v+61,h⟩ => omega
  have h := blocks ⟨g.val/4,by omega⟩ ⟨g.val%4,by omega⟩
  simpa only [Nat.div_add_mod] using h
private theorem upper (K : Finset (Fin 468)) (H : compatible K) : K.card ≤ 244 := by
  have distinct (i j : K) (lt : i.val < j.val) (same : color i.val = color j.val) : False := by
    obtain ⟨p,high,avoid,guardOK,pass⟩ := H i j lt
    have first := recover i.val
    have second := recover j.val
    rw [←same] at second
    have bad := allRows (color i.val) (slot i.val) (slot j.val)
    simp only [Fin.ofNat_val_eq_self,first,second] at bad
    exact bad lt j.val.isLt p high avoid (by simpa only [posGauge,negGauge] using guardOK) (subsetBits i.val j.val p pass)
  have inj : Function.Injective (fun i : K => color i.val) := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with h | h
    · exact distinct i j h eq
    · exact distinct j i h eq.symm
  simpa using Fintype.card_le_of_injective _ inj
end PEqualNP.Research.PlaneCase35GuardOmissionMaximum
open PEqualNP.Research.PlaneCase35GuardOmissionMaximum in
theorem PEqualNP.Research.PlaneCase35GuardOmissionMaximum : (∃ K : Finset (Fin 468), compatible K ∧ K.card = 244) ∧
  (∀ K : Finset (Fin 468), compatible K → K.card ≤ 244) := ⟨existsFamily,upper⟩
