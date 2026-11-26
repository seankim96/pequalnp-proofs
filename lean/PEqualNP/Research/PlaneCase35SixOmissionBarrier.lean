import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Research.PlaneCase35SixOmissionBarrier

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


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private def pw (i : Nat) := (0x80040002000100080000106000001040040001000800040002005000002020020000800400020001004800001010040000400400210008000400020008020008200200008004000200010004010000100100004002008100008202008000080080002001000080004001004000040040001000804040002000802000020020000800424020001000440000010040000400408010008000220000008020600200200008004000110000004010000100104004002200088008002008100080084002001 >>> (30*i)) &&& 1073741823
private def nw (i : Nat) := (0x2e4008c0b8800382e100860b8042282e0008e0b2804282c881120b2040680c809180b2004686c420940b1042600c4081c0b1002702c30106030824302c2010e0b0606086c121840b0406186c0a1900b0242482c081920300a4506c021940b0042680c0091c0ee0008a3b200068ac400981b020248ec0009a3aa000a86a100a22a8102a0ea000aa1a6000c8e9102227a420848e9002323a2000e9a8482902a110a20a8402987a060a08a8142a03a040a89e8082922a010aa2e62004a19820308a6040c83980032865808129948210865080520940a140650085229302062e4a080a39202068a4448880910a240a44089829092122e42084a0902834064080d20901a300a4048c80900a342e2a040a18a41088e28042a988a110ae22044a1886120822124a018841288220a4c01882130822060e0288103a022024e0186420882182830186020cae130a02f84a0908a124a40b8482908a114a2038442889e1082520841a180a104a600840a1c0a0e0c080830b040a0c0c18982c300ae0a0c0a0824b0806090c220820b0c0a070e0028192820a060e0868161a00a054a800814b200a050e8008129241a04869028112a202042c90f80e180ae030e02f80a1908a024a4878061a0820168a028052a802012ca00802934020068e0272004609c4001c270804301c02114270004709940214264408901902034264008d09884128062084c0988013826180830984021c260c0c10982430826080c30981432006048490981032426010ca0180213415c00114d64000d25880130d60404935800134554001515420144150205415400154d4c001915220444d48410935200464d44001d25090520142214425080530540c14105028540540815135010524140215414c40094530406104c08190530006534b01024529042134a100a4d28042924981030525040534901034122244424881130121242414841094d20406904809190d15020574520844d14021534450884d11022574430905d10825134410984110207414321044d0c0419142614045094121042494805090521042294405088511342104a41082530241c1810906060c74161804d050605741218459038700040c94109030704640b0d00102a540640a1d00902434804089511d01c30174061c04d01432104049491d00c341040295408e4008cb38800384e100863380023acca010a13220448cc8011a031082508c4009c930c041acc2010e130606080c12184130406180c0a190130206480c0219412e0408a4b2100612c400980b0302412c0409acaa100a22a140a0ca8102a229840308a450880290c2108a4108cb28840380a120a4128402980a070a0228142a00a030a4126240480983030126040c8896120462524840094301422504852c930206f24a480ac92120632440899c9092120240c0d248a910222294422c8a110a0222c44048891120221c48088851280220c4c0886520822184831884d2800212c241884929022114a200843094f20e0c0ac830306620b4c03c82930222094c21881c38072060e0808161a022050e8008121a40203c601880d3800202c64008071a091c80118471000711c2010c470004711940214c64408931900236c62004e1186020c46100871183030446080c33181032445c08111164200c45880131160204c45508050150a0504540815914c201805228449148211845108071142014c050285431312024c4c0819912c240884a4908b128242844981031125240444909031122044cc48490911152204045288411142214c4448890110a2500432904910c241804269402109252004229441107060444181830105a60044149810104a610040e1c011030704040a1d00101a700439002310e2400c438502110e0408e432904200c8c112432104610c4009c430d04110c2410c030706010c14184030306420b8502042c940130b14024c2c140990aa500ac2a140a10a6100c429042310a2500cc2850290098d010826140c10961204025248410941214424d0810092d2004249481309142240243484008ad10242294420088d110421848300849290020f0c010834304020b4c00081c38041c90111071600401c38101070604441948211064208c41890130061e08041858210060e0c08170a0420596800016380420586810c154a0130542815c14d20170524844c145a010050e052c130a06604b4903c1292420049e1008125a400048e110c114a217043490401078602039602000e3c002038702000cb41010325044c0c58090030f04240b8502002cb40240b0d02002ad40240a95020029e40080a59080028f40040985030025a48040949210024b480008b5100021e4800072c04201c38108065a080018f011c05c28170161a04c054a810014b211c04d2810012d243c038702000cb410002f140600b4d00002b5400009e501c01c3810005a680000f1c0 >>> (30*i)) &&& 1073741823
private def addressAt (i : Nat) := (0x5280911d0962a0678ea1c8660cc64908a92924d41342686529530900f0348ba43987070a1d1082580197d2fb168810811f25ad33a684cf198888d20c68940da25c4c3cc061c58ba7146c1263bb778ee836246564211cb3970247fa0740f63cc7e082883d8739aa355b47692d05a1b44d85b05a5a794ea9dbc6790b11e3c529632c228c50964619d1ba24b058a9a536a6a4c9141f8b0a19ac3584b0561c9c583768ed5db2349db592b2cee9d959800048570e75ce1da7e2fc1f918c6fedf94d25e27c9493e0f07f8ff9053fd5409d9d40ae752079ec3d97b4481ad11a6b6b421332464b0a29252384f48a3d1bc8f91ec7b1e04c81c99b0e466edcdb94758ec3623a4f99f53e1f5bce7d4f35f63cc61ac32d395cb4d6aad4da82896ae882e8a1942e8558bb136226d58cb1a5bac54db9413824fcdc93c2a0bd11457c03189313600c043f0fcb1d646c958fb276417110e8690ce1928e438138600425e8bd41e3f87eede1bcbf6991326650a2a2d4628bc8c91d2364348890ecf42a33c96f2d98c3199706d93519887f0f90b440784f05083c05955f6b057caff57ebf580abd6041542d85d0b02d240138b724c49a6db265b61928c918e3146f8dd1c2a9d52aa92ae564aa24cab07534f0611753845c8bcd386f4028066020252ea60d21a4d2fb31072cad9983765eca41ab2d3fe7f22ea013566b4d4a9115aa3c578b151a79cf22ad3d1c2b84841086110605debbaced9bb3ed9ecd59c6cd67a0ac1482d292534be97b2965e3e4354f99f2c0a8d31aa044098d1532b8d4ea9b5ca415739015c240d6ca0b5ae83504ad4f81efbde60ecad953d27a8c19e9d78aed5eabcd77722e42bdd2998730a95528989506a1168a81472acd1dab547aac4e79d0ebdd84e675d11622446 >>> (11*i)) &&& 2047
private def members : Array Nat := #[0x3a9d4ea753a955, 0x3a9d4ea753a9b6, 0x3a9d4ea753a8ee, 0x3a9d4ea753a993, 0x3a9d4ea753a9a2, 0x3a9d4ea753a93a, 0x3a9d4ea753a9d2, 0x3a9d4ea753a8a5, 0x3a9d4ea753a887, 0x3a9d4ea753a9a6, 0x3a9d4ea753a8d5, 0x3a9d4ea753a8d8, 0x3a9d4ea753a954, 0x3a9d4ea753a8da, 0x3a9d4ea753a8c1, 0x3a9d4ea753a8a1, 0x3a9d4ea753a858, 0x3a9d4ea753a966, 0x3a9d4ea753a999, 0x3a9d4ea753a922, 0x3a9d4ea753a9bf, 0x3a9d4ea753a8e9, 0x3a9d4ea753a996, 0x3a9d4ea753a9c8, 0x3a9d4ea753a9c0, 0x3a9d4ea753a9d0, 0x3a9d4ea753a89f, 0x3a9d4ea753a8cc, 0x3a9d4ea753a8f2, 0x3a9d4ea753a93c, 0x3a9d4ea753a9b3, 0x3a9d4ea753a9a0, 0x3a9d4ea753a8d9, 0x3a9d4ea753a9a8, 0x3a9d4ea753a9ab, 0x3a9d4ea753a9be, 0x3a9d4ea753a91a, 0x3a9d4ea753a881, 0x3a9d4ea753a920, 0x3a9d4ea753a889, 0x3a9d4ea753a944, 0x3a9d4ea753a925, 0x3a9d4ea753a8e8, 0x3a9d4ea753a9b1, 0x3a9d4ea753a9b8, 0x3a9d4ea753a8e0, 0x3a9d4ea753a8f0, 0x3a9d4ea753a934, 0x3a9d4ea753a936, 0x3a9d4ea753a88b, 0x3a9d4ea753a9b7, 0x3a9d4ea753a96a, 0x3a9d4ea753a961, 0x3a9d4ea753a947, 0x3a9d4ea753a907, 0x3a9d4ea753a9c2, 0x3a9d4ea753a9cf, 0x3a9d4ea753a85f, 0x3a9d4ea753a90c, 0x3a9d4ea753a96e, 0x3a9d4ea753a810, 0x3a9d4ea753a8fa, 0x3a9d4ea753a9bd, 0x3a9d4ea753a8f1, 0x3a9d4ea753a87e, 0x3a9d4ea753a972, 0x3a9d4ea753a94c, 0x3a9d4ea753a898, 0x3a9d4ea753a8b8, 0x3a9d4ea753a9ce, 0x3a9d4ea753a9a9, 0x3a9d4ea753a843, 0x3a9d4ea753a99e, 0x3a9d4ea753a8ba, 0x3a9d4ea753a928, 0x3a9d4ea753a9ba, 0x3a9d4ea753a9cc, 0x3a9d4ea753a98a, 0x3a9d4ea753a9cd, 0x3a9d4ea753a950, 0x3a9d4ea753a924, 0x3a9d4ea753a9a3, 0x3a9d4ea753a98b, 0x3a9d4ea753a9b0, 0x3a9d4ea753a968, 0x3a9d4ea753a992, 0x3a9d4ea753a9b2, 0x3a9d4ea753a941, 0x3a9d4ea753a8b1, 0x3a9d4ea753a8b5, 0x3a9d4ea753a8db, 0x3a9d4ea753a9aa, 0x3a9d4ea753a969, 0x3a9d4ea753a86c, 0x3a9d4ea753a95c, 0x3a9d4ea753a9d1, 0x3a9d4ea753a8a0, 0x3a9d4ea753a998, 0x3a9d4ea753a99d, 0x3a9d4ea753a946, 0x3a9d4ea753a96f, 0x3a9d4ea753a948, 0x3a9d4ea753a923, 0x3a9d4ea753a8b9, 0x3a9d4ea753a885, 0x3a9d4ea753a93e, 0x3a9d4ea753a945, 0x3a9d4ea753a9c5, 0x3a9d4ea753a98c, 0x3a9d4ea753a8dc, 0x3a9d4ea753a9d3, 0x3a9d4ea753a949, 0x3a9d4ea753a93f, 0x3a9d4ea753a9c1, 0x3a9d4ea753a88a, 0x3a9d4ea753a997, 0x3a9d4ea753a953, 0x3a9d4ea753a8ef, 0x3a9d4ea753a97a, 0x3a9d4ea753a8af, 0x3a9d4ea753a932, 0x3a9d4ea753a9af, 0x3a9d4ea753a89e, 0x3a9d4ea753a8e1, 0x3a9d4ea753a904, 0x3a9d4ea750ae56, 0x3a9d4ea751acd7, 0x3a9d4ea75369b5, 0x3a9d4ea751d4eb, 0x3a9d4ea7504e22, 0x3a9d4ea7521f0e, 0x3a9d4ea751d8ed, 0x3a9d4ea75178bd, 0x3a9d4ea7531d8f, 0x3a9d4ea7525f30, 0x3a9d4ea7504c25, 0x3a9d4ea75395cb, 0x3a9d4ea7523f21, 0x3a9d4ea75184c0, 0x3a9d4ea75387c4, 0x3a9d4ea750f27a, 0x3a9d4ea7511082, 0x3a9d4ea7531189, 0x3a9d4ea7526735, 0x3a9d4ea7530581, 0x3a9d4ea750a44f, 0x3a9d4ea7513699, 0x3a9d4ea7523d1d, 0x3a9d4ea751a2d2, 0x3a9d4ea752974a, 0x3a9d4ea750ba5c, 0x3a9d4ea753439f, 0x3a9d4ea750361a, 0x3a9d4ea7532995, 0x3a9d4ea752a551, 0x3a9d4ea752e370, 0x3a9d4ea752773d, 0x3a9d4ea0140c03, 0x3a9d4ea576bd5f, 0x3a9d4ea66f399a, 0x3a9d4ea2cd64b0, 0x3a9d4ea5eef37c, 0x3a9d4ea4522510, 0x3a9d4ea08c4224, 0x3a9d4ea4de7139, 0x3a9d4ea0a85228, 0x3a9d4ea1088244, 0x3a9d4ea4462b13, 0x3a9d4ea5369f4e, 0x3a9d4ea351a6d0, 0x3a9d4ea50a8143, 0x3a9d4ea1f4fe80, 0x3a9d4ea100783d, 0x3a9d4ea6372191, 0x3a9d4ea12c9a4c, 0x3a9d4ea1d8e670, 0x3a9d4ea164b45b, 0x3a9d4ea4ba5731, 0x3a9d4ea28d48a2, 0x3a9d4ea37dbcdd, 0x3a9d4ea6e779bb, 0x3a9d4ea2d16eb6, 0x3a9d4ea0000401, 0x3a9d4ea6934ba7, 0x3a9d4ea5e2eb74, 0x3a9d4ea18cc866, 0x3a9d4ea20d0c84, 0x3a9d4ea25d2c95, 0x3a9d4ea0f87e3b, 0x3a9d4ea2492893, 0x3a9d4ea46e3919, 0x3a9d4ea49e4d29, 0x3a9d4ea0d46233, 0x3a9d4ea31186c5, 0x3a9d4ea31d8cc8, 0x3a9d4ea71f8dc9, 0x3a9d4ea271349d, 0x3a9d4ea3ddeaf3, 0x3a9d4ea1248c4a, 0x3a9d4ea2351c8c, 0x3a9d4ea5ceef76, 0x3a9d4ea2ed7ebe, 0x3a9d4ea1208e45, 0x3a9d4ea04c2e16, 0x3a9d4ea3359ccf, 0x3a9d4ea6b759ae, 0x3a9d4ea1a4d468, 0x3a9d4ea3d1f0fd, 0x3a9d4ea753a8f6, 0x3a9d4ea01c1004, 0x3a9d4ea562b757, 0x3a9d4ea178c260, 0x3a9d4ea45e3116, 0x3a9d4ea1acdc6d, 0x3a9d4ea0b45e2c, 0x3a9d4ea40e0501, 0x3a9d4ea753a905, 0x3a9d4ea32992cb, 0x3a9d4ea028180e, 0x3a9d4ea4b6592a, 0x3a9d4ea0543014, 0x3a9d4ea1ecf07c, 0x3a9d4ea5b2d76d, 0x3a9d4ea5fefb7e, 0x3a9d4ea044240f, 0x3a9d4ea19cca62, 0x3a9d4ea0e06e3a, 0x3a9d4ea23d2290, 0x3a9d4ea02c1a09, 0x3a9d4ea2b554a7, 0x3a9d4ea55ab35a, 0x3a9d4ea0c05c2b, 0x3a9d41a0d87232, 0x321e0e880381f, 0x14ca855aa55cac, 0x2c565b3d92c163, 0x1f6fc803e5fefe, 0x1c6e573389c8e7, 0xe877391bcea71, 0xa64e2a940a851, 0x30186c3e0f0985, 0x20d0a84c221b0b]
private def color (i : Fin 468) : Fin 242 := Fin.ofNat 242 ((addressAt (i.val)) / 6)
private def slot (i : Fin 468) : Fin 6 := Fin.ofNat 6 ((addressAt (i.val)) % 6)
private def member (c : Fin 242) (k : Fin 6) := (members[c.val]! >>> (9*k.val)) &&& 511
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
private def tabAt (i : Nat) := (0xfffffffffffff0ffffffffffffeeeffffeeffec0eeffffeeffecfffdbe7ffedf30ffdbe7ffedf3eeedbe7eeede00eedbe7eeede0ffffffffffdff0fffffffffdffeeeffffeefdec0eeffffeefdecfffdbe7ffedf30ffdbe7ffedf3eeedbe7eeede00eedbe7eeede0ffffffffeffff0fffffffeffffeeeffffeeffec0eeffffeeffecfffdbe7feedf30ffdbe7feedf3eeedbe7eeede00eedbe7eeede0ffffffffefdff0fffffffefdffeeeffffeefdec0eeffffeefdecfffdbe7feedf30ffdbe7feedf3eeedbe7eeede00eedbe7eeede0ffffffffffffffffff0fffffffffff0ffffffffffff00ffffffffff0ffffffffffff0f0ffffffffff00fffffffffff000fffffffff0ffffffffffff0ff0fffffffff0f0ffffffffff0f00fffffffff00fffffffffff00f0fffffffff000ffffffffff0000ffffffff0ffffffffffff0fff0ffffffff0ff0fffffffff0ff00ffffffff0f0ffffffffff0f0f0ffffffff0f00fffffffff0f000ffffffff00fffffffffff00ff0ffffffff00f0fffffffff00f00ffffffff000ffffffffff000f0ffffffff0000fffffffff00000ffffffffffffffffffffffffffffff0fffffffffff0ffffffffffff00ffffffffff0ffffffffffff0f0ffffffffff00fffffffffff000fffffffff0ffffffffffff0ff0fffffffff0f0ffffffffff0f00fffffffff00fffffffffff00f0fffffffff000ffffffffff0000ffffffff0ffffffffffff0fff0ffffffff0ff0fffffffff0ff00ffffffff0f0ffffffffff0f0f0ffffffff0f00fffffffff0f000ffffffff00fffffffffff00ff0ffffffff00f0fffffffff00f00ffffffff000ffffffffff000f0ffffffff0000fffffffff00000fffffffffffffffffbbf7fffff7ffb7f7fffff7fffb3b77ffff77f77f7fffff7fff77b3f7fff7f7f73777ffff77ff733377fff777fffffffffffff0ffbbf7fffff70fb7f7fffff7f0fb3b77ffff77077f7fffff7ff077b3f7fff7f7073777ffff77f0733377fff7770fffffffffff0fffbbf7fffff0ffb7f7fffff70ffb3b77ffff70f77f7fffff7f0f77b3f7fff7f0f73777ffff770f733377fff770ffffffffffff00ffbbf7fffff00fb7f7fffff700fb3b77ffff70077f7fffff7f0077b3f7fff7f0073777ffff7700733377fff7700ffffffffffffffffefffdbfbffffdfffdbfbfffffdeffd9bbbfffdfffdbf7fffffdfefdbd3fbfffddffd9b7bffffddefd993bbffbfffdbf7fffffbffedbf5bfbffbfdfdbd3fbfffbfdedbd1bbbffbdffd9b77ffffbdfed9b53fbffbddfd9937bfffbdded9913bbfffffdbf7fffff7fffcbf7dbfbf7ffddbf5bfbff7ffdcbf59bbbf7fdfdbd3f7fff7fdfcbd3d3fbf7fdddbd1b7bff7fddcbd193bbf7bffd9b77ffff7bffc9b75bfbf7bfdd9b53fbff7bfdc9b51bbbf7bdfd99377fff7bdfc99353fbf7bddd99137bff7bddc99113bbf7fffffffffffffefefffffefffefefffffefffedeeeffffeeffecdfffffefffedfcfefffefefededeffffeeffecdceefffeeefeccfffffefffedfbefeffeffeedfafefffefefede9eeeffefeeede8dffffeeffecdbcfeffeefeecdadefffeeefecc9ceeffeeeeecc8ffffefffddfbfefefefffcdfbefeffeffeddfadeeefeffecdfacdfffefefdde9fcfefefefcde9edeffefeedde8dceefefeecde8cffffeeffdcdbbefefeeffccdbafeffeefedcda9eeefeefeccda8dfffeeefdcc9bcfefeeefccc9adeffeeeedcc89ceefeeeeccc88 >>> (52*i)) &&& 4503599627370495
private def window (x g : Nat) := (x >>> (5*g)) &&& 31
private def lookup (g u : Nat) := (tabAt (32*g+window u g))
private def survivors (u : Nat) := (0xfffffffff12f0 : Nat) &&& lookup 0 u &&& lookup 1 u &&& lookup 2 u &&& lookup 3 u &&& lookup 4 u &&& lookup 5 u
private theorem keep : ∀ p : Fin 52, (0xed0f : Nat).testBit p.val = false → (0xfffffffff12f0 : Nat).testBit p.val = true := by decide +kernel
private def tabOK (g : Nat) := ∀ (x : Fin 32) (p : Fin 52),
    window (pw (p.val)) g &&& x.val = window (pw (p.val)) g →
    (tabAt (32*g+x.val)).testBit p.val = true
private theorem tab0 : tabOK 0 := by unfold tabOK; decide +kernel
private theorem tab1 : tabOK 1 := by unfold tabOK; decide +kernel
private theorem tab2 : tabOK 2 := by unfold tabOK; decide +kernel
private theorem tab3 : tabOK 3 := by unfold tabOK; decide +kernel
private theorem tab4 : tabOK 4 := by unfold tabOK; decide +kernel
private theorem tab5 : tabOK 5 := by unfold tabOK; decide +kernel
private theorem window_and (x y g : Nat) : window (x &&& y) g = window x g &&& window y g := by
  apply Nat.eq_of_testBit_eq
  intro h
  simp only [window,Nat.shiftRight_and_distrib,Nat.testBit_and]
  generalize (x >>> (5*g)).testBit h = a
  generalize (y >>> (5*g)).testBit h = b
  generalize (31 : Nat).testBit h = c
  cases a <;> cases b <;> cases c <;> rfl

private theorem lookupHit (p : Fin 52) (u g : Nat) (cert : tabOK g)
    (eq : (pw (p.val)) &&& u = (pw (p.val))) : (lookup g u).testBit p.val = true := by
  let x : Fin 32 := ⟨window u g, Nat.lt_succ_of_le Nat.and_le_right⟩
  apply cert x p
  change window (pw (p.val)) g &&& window u g = window (pw (p.val)) g
  rw [←window_and,eq]
private def absent (g : Nat) : Prop := ∀ u v : Fin 6,
  let i := member (Fin.ofNat 242 g) u
  let j := member (Fin.ofNat 242 g) v
  i < j → j < 468 → survivors ((nw (i)) ||| (nw (j))) = 0
private theorem rows0 : ∀ t : Fin 11, absent (11*0+t.val) := by unfold absent; decide +kernel
private theorem rows1 : ∀ t : Fin 11, absent (11*1+t.val) := by unfold absent; decide +kernel
private theorem rows2 : ∀ t : Fin 11, absent (11*2+t.val) := by unfold absent; decide +kernel
private theorem rows3 : ∀ t : Fin 11, absent (11*3+t.val) := by unfold absent; decide +kernel
private theorem rows4 : ∀ t : Fin 11, absent (11*4+t.val) := by unfold absent; decide +kernel
private theorem rows5 : ∀ t : Fin 11, absent (11*5+t.val) := by unfold absent; decide +kernel
private theorem rows6 : ∀ t : Fin 11, absent (11*6+t.val) := by unfold absent; decide +kernel
private theorem rows7 : ∀ t : Fin 11, absent (11*7+t.val) := by unfold absent; decide +kernel
private theorem rows8 : ∀ t : Fin 11, absent (11*8+t.val) := by unfold absent; decide +kernel
private theorem rows9 : ∀ t : Fin 11, absent (11*9+t.val) := by unfold absent; decide +kernel
private theorem rows10 : ∀ t : Fin 11, absent (11*10+t.val) := by unfold absent; decide +kernel
private theorem rows11 : ∀ t : Fin 11, absent (11*11+t.val) := by unfold absent; decide +kernel
private theorem rows12 : ∀ t : Fin 11, absent (11*12+t.val) := by unfold absent; decide +kernel
private theorem rows13 : ∀ t : Fin 11, absent (11*13+t.val) := by unfold absent; decide +kernel
private theorem rows14 : ∀ t : Fin 11, absent (11*14+t.val) := by unfold absent; decide +kernel
private theorem rows15 : ∀ t : Fin 11, absent (11*15+t.val) := by unfold absent; decide +kernel
private theorem rows16 : ∀ t : Fin 11, absent (11*16+t.val) := by unfold absent; decide +kernel
private theorem rows17 : ∀ t : Fin 11, absent (11*17+t.val) := by unfold absent; decide +kernel
private theorem rows18 : ∀ t : Fin 11, absent (11*18+t.val) := by unfold absent; decide +kernel
private theorem rows19 : ∀ t : Fin 11, absent (11*19+t.val) := by unfold absent; decide +kernel
private theorem rows20 : ∀ t : Fin 11, absent (11*20+t.val) := by unfold absent; decide +kernel
private theorem rows21 : ∀ t : Fin 11, absent (11*21+t.val) := by unfold absent; decide +kernel
private theorem allRows (g : Fin 242) : absent g.val := by
  have batches (a : Fin 22) (b : Fin 11) : absent (11*a.val+b.val) := by
    match a with
    | ⟨0,_⟩ => exact rows0 b
    | ⟨1,_⟩ => exact rows1 b
    | ⟨2,_⟩ => exact rows2 b
    | ⟨3,_⟩ => exact rows3 b
    | ⟨4,_⟩ => exact rows4 b
    | ⟨5,_⟩ => exact rows5 b
    | ⟨6,_⟩ => exact rows6 b
    | ⟨7,_⟩ => exact rows7 b
    | ⟨8,_⟩ => exact rows8 b
    | ⟨9,_⟩ => exact rows9 b
    | ⟨10,_⟩ => exact rows10 b
    | ⟨11,_⟩ => exact rows11 b
    | ⟨12,_⟩ => exact rows12 b
    | ⟨13,_⟩ => exact rows13 b
    | ⟨14,_⟩ => exact rows14 b
    | ⟨15,_⟩ => exact rows15 b
    | ⟨16,_⟩ => exact rows16 b
    | ⟨17,_⟩ => exact rows17 b
    | ⟨18,_⟩ => exact rows18 b
    | ⟨19,_⟩ => exact rows19 b
    | ⟨20,_⟩ => exact rows20 b
    | ⟨21,_⟩ => exact rows21 b
    | ⟨v+22,h⟩ => omega
  have h := batches ⟨g.val/11,by omega⟩ ⟨g.val%11,by omega⟩
  simpa only [Nat.div_add_mod] using h
end PEqualNP.Research.PlaneCase35SixOmissionBarrier
open PEqualNP.Research.PlaneCase35SixOmissionBarrier in
theorem PEqualNP.Research.PlaneCase35SixOmissionBarrier : ∀ K : Finset (Fin 468),
  (∀ i j : K, i.val < j.val → ∃ p : Fin 52, (0xed0f : Nat).testBit p.val = false ∧
    ∀ k : Fin 30, base k p.val = true →
      base k (52+i.val.val) = true ∨ base k (52+j.val.val) = true) → K.card ≤ 242 := by
  intro K witnesses
  have distinct (i j : K) (lt : i.val < j.val) (same : color i.val = color j.val) : False := by
    obtain ⟨p,allowed,pass⟩ := witnesses i j lt
    have first := recover i.val
    have second := recover j.val
    rw [←same] at second
    have blocked := allRows (color i.val) (slot i.val) (slot j.val)
    simp only [Fin.ofNat_val_eq_self,first,second] at blocked
    let u := (nw (i.val.val)) ||| (nw (j.val.val))
    have zero : survivors u = 0 := blocked lt j.val.isLt
    have hit := subsetBits i.val j.val p pass
    have yes : (survivors u).testBit p.val = true := by
      simp only [survivors,Nat.testBit_and,keep p allowed,lookupHit p u 0 tab0 hit,
        lookupHit p u 1 tab1 hit,lookupHit p u 2 tab2 hit,lookupHit p u 3 tab3 hit,
        lookupHit p u 4 tab4 hit,lookupHit p u 5 tab5 hit,Bool.true_and]
    simpa [zero] using yes
  have injective : Function.Injective (fun i : K => color i.val) := by
    intro i j eq
    by_contra ne
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => ne (Subtype.ext e)) with h | h
    · exact distinct i j h eq
    · exact distinct j i h eq.symm
  simpa using Fintype.card_le_of_injective _ injective
