import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975Family5Mask
open PlaneFirstAndSeparation PlaneFirstAndBudget

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
  x ||| ((b 0 &&& b 13) <<< 26) ||| ((b 0 ||| b 14) <<< 27) |||
    ((b 1 &&& b 13) <<< 28) ||| ((b 1 &&& b 18) <<< 29) ||| ((b 2 &&& b 15) <<< 30)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def base : List Column := List.ofFn (fun j : Fin 31 => input j.val) ++ [fun _ => false, fun _ => true]
def omittedFlags : Nat := 0x88f8000008000

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x1cae4f238fc6e2f1387c2e0f037fbedeef377badcec359abd469747a2d0e833f9ecee733598cbe5b2b94c9e4b218fc76371788c3e17017fbe5eef378bbddae973b85b2d768b3596c960afd7abb5cadd6ab358abd5aa34da55228b42a0d027f3e9ecf2773a9bcda6b3499cca633097cba572a94c9245208fc7a3b1b8d46631158a44a230e86c32150581405fefe7dbe1eef67abd1e6ec753a1b4d162b0d78bb5cad96aaf56aad54a44fa79389a4ca5d1c8d46229128743215088341204fe7e3e9ecf2783b9d8e873381bcda6c359a0ce663298cc45f2f174b85a2c960ae562913c984a2491c8c45219047e3e1e0ec72381a8d06632188c05e2d160ac54291409c4c2511888421c0d86832180a85026110803c1a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x32004683108250b1042603102070310027030c0418308243030804383060608304861030406183028640b0242483020648300a4503008650b00426830024702a000aa2900232288003a284029828102a2a8042a8262004a26080c2a6040c826000ca258081225208422508052250085224a080a248081aa44488824428902440898a424848242084a24080d2a4068c0a4048c824028d02290422222044a221848222104a222024e021908222130a0221282422120a42a114a202110a222108252a104a60210287020c0c182090c222082c302060e08a054a802052c802050e802042c9020386022030e022028642a024a482018682a0168a0a014aa02012ca0200a4d0a0068e01c0011c19002341880138184021c182030c1810324980432818021349700045964000d162004c9604049960004d9540015950005594c0019948811194841099480119944001d94241481422144142014c940c141940414914021549310025929042192804299250405924040d1222444122044c9210425920406912024649150205911422191102259108251910426190c0419909850190941219090521107060490506059048611103250410307041028740901c301901870190143211012524900c341100a5500c8011a0c4009c0c2010e0a8102a8a050a80910226090303488851280883130086120c084929088452888825308081838288143a008121a48710007864008d062004e861008786080c386040c9859080385108078508053050285484c081904b090204a090a849810384949018490903848811384849098454881845088584448890442894043090684249480422944841c181841818384149810412984040a1d084069c083890038385021838102303210468310027830d04183090438305061030306482c500982c140902a940202a140a8290423828940382850290263404026140c824d08182450890229442821848302124a4820d0c1020b4c082070e081c580181c181181908238189013818582101838308165a0001638048150a05814d20181492118145a0101438140130a06812d24081278408125a4001238448114a21810d241810786080e580800e3c0000e1c0880c941180c580900c3c1000a950280a790080a590800a3d0080985030092d20008b51080879200070e048065a080063c0480586818054a810052c84804d281004b49000387020032d04802f140802d340002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3ffffffffffffffffff8000000000000000000000000000000000000000000001ffff800000000000003fffffffffffffe000000000000000000000000000000000003f0000000000001fe000000000000ffff0000000000000000000000000000000007ffff0000000080ffffc000000070007fffffff00000000000000000002000083c0007c000000007c001ff8000006003f0000007fffffe0000000000000f000201e0001ff00001021800803e00000c0107800003fe0000fffff8000000007000808c01080700004003c03000f0009180023fc001c0fe007e0003fff0000027002001c000027c0010451006084700203820101e000060f030fe01f807f800027002121821c021e004100700c002700812080600e0080c640060f8e3c383f000000400002d984ecf0100000d138fb78080f262e64f020101820842001939864053004201042200544000102000242730024088480650c245b08310848a13ba900440901260048205902104980249015048d020134a94541316294ef130a51bc480900004284024a0b8080022088004140a04010012380404160a129455c95b600000000000000000000000000000000037f000000003dfefe7df7bdffe6c6790000000dfee0ddffaba000000000000000000037b7f9a00000077cef7b75ec4543fba000000f803dfa60000001fd06fea800000000000003ece800000ecf5ae41a3f65c000001fc35f42f00000007c3be811f80000000000000005ed600036a480000000000000000002bc03bf0000e3ff431e003f87fc0000000000001fe01ff0000277039e7000787e0000000000000048375c003c7e00006f8000000001f03fc0fe07b83f499c00c300ba0fc1b180218000166000c3178009c000f6000001e6ec03ec00004e36c00eb380001c3b4c0307e0c000000034c28125800500140004bec6b816b24005a100bc41ec100050403854001c10808000000542800a04020085acadb0ee48004808174f2f515408000f9586428490000d2a0000002a2040000000000000000000000ddee1667da06c23320f8a00b441880c2006310000522000000eb7f0c7bd881d0000000000000002d012ee760885d0f06060080022002000000000000000000000037fc6f9bfec740001bf4ff0e3bd9cd4f8f030c103404 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010000000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xffffffffffffffffc70bf8ff8bfffffe0ff1b30ffffffffffffffffc6fff2dffde77f2bf27fb30fffffffffffffff2bf0ffb87fdeffffc673f130fffffffffffffffffffffb9f0de77ffff0b1b30fffffffffffffff2860ffb9ffff77ffff731b30ffffffffffff47fffffffbbf6d769657ffffff0fffffffffffffcd2bffffbbfff2fd9fff098b30ffffff83ffd5ffffff0bfbbf6f2fd9ffffffb30fffffffffffffff247fffbbfffffd6491ff1b10fffffffffffffcdfff0ff2fffffb56fff271b30fffffffff6ff47f27ffffbbffd7b5657fff1ff0ffffffffffffffffc70ff2ffff2ffffd1271b10ffffe5fffffffff27ffffb87ff24ff4bffc5fd0ffffffffffd6fff247fffbbfffffff4bfff1b10ffffff83fffffffffffff2ff0f2b7f2bf0bfb30fffffffdffd647ffff0ff2ffffffff2bf27fb30fffffffdcfff4bfffffffb87ff2b7ffc6fff130ffffff81f67ffff2bffffbbf0f2ffffff0bfff0fecfe4fff6bf48c2440bf8ff8bfffffffff1ff0fecfe4fff6ff44d2840ffffffff77fffffffff0fecfe481cfd5fccfff0bffffff2699ffffffff0fedfe5fff6bf44c2460bffffffffd657fff1ff0ffffff89d6954bf2840fffffffffcefff331ff0fedfe489cfd548cfff0bffffff2ffffc6fffff0fffffffffffffffffffff8e68a14ff491ff1fd0ffffffffffff4ffffffff2e6fe1fff2a027fff0fffffffffffffffffffff8c78a1fff93ffc5130ffffffffffff4ff244fff8e68a1fff93fff1ff0fffffffffffffcdfc4ffffdffff69993f718ff0fffffffffffffcefc4ffffdf97f4fffd1731fd0fffffffffffffffffffff2df95e77f2bf271ff0fecffffff67f47f2fffffffffff77f93fff1ff0ffffffffffffffffc4ffffe66f2fd9491fd8fd0fffffffdcfff47ffffffffe6ff269993ffd8ff0ffffffffffff4fffffffffc797ffd6546fc5ff0fffffffddffffcdfffffffe60d7fd657f0b1ff0fffffffff6bf47ffc60bffe697ffd657fff1ff0ffffffffffd6ffffff0bffc79724ffffffc5110ffffff8dc67fffffc4ffffe697fffffd1ff1fd0ffffff81dffffffffffff2e6972fff2bf27fff0ffffffffffff4ce2ffffffffff2fff9060bfff0ffffff8fffd64ccfff0bffffffffff906fffff0fffffffddfd647f2c6ffffffffffff93f0b1ff0fffffffffffffff2bffff8ff6ff68efcd318ff0fecfe6fff67ffff27ffff8ff8bf4fffffff1fd0ffffffffffff4ffffffff2ff8bffce28d27fff0fffffffff6bffff2bffff8ff8bffcefff331ff0fedffffffffffce287fff8fffffffffe00b1ff0ffffffffffffffffffffffdf6de68efcd318ff0fffffffff6ffffffc4ffffdffff4ce4bf331fd0ffffff8bffffffffc4fff2dffdefff29127ffd0ffffe5fffffffce2c4ffffdfffffff491ff1fd0ffffffffffff4bffff0fffc7fff74efff305130fffffffff6ff4bffc40fffdffff74efcd331ff0fecfe5ffffff47fffffff2dffde77f2bf27fff0feefffffffff48efff0ffffffff77ffc673fff0feefe4fff67f47ffc6ffffff0ff77ffffff1ff0feefe6ffffff44cfff0bfffffff69657ffffff0ffffff8dffff4bffffffffff6f268efcdfffff0feeffffdffd5fcd2bfffffffff2fd9fff0bfff0feeffffff6fffccfc7ffffffffffd6491ff1fd0ffffffffffff4fffffffffc7fd7fce54633fff0ffffffffffff4ff2ffffffff0fffce54d0b1ff0ffffffffffff4ff2c70fffffffffce54dfffff0ffffe6fff6bffcd2ffffffff0fffd6fff0b1ff0fffffffff6fffffffffff2ffff24ce28d271fd0fffffffdfffffff2ff0fffffff24ce4bf331fd0fecfff89fffffceffffff2ffff24fffff27ffd0feefe5fdcfd6ffffffffffc7ff2fff4bfffffd0ffffff8bffff4ffffffff2ffff2fce28d27fff0fffffffddfffffffffffffc70f2fcefc60bfff0fffffffddfd5ffffff0fffc7ff2fcefff305130ffffff8ff695ffffc7ffffff0fffcefffff1ff0fedfe683ffd6fffffffff2ff0f2fff2bffffff0ffffe48ddfff48efffffffffff2ffffc60bfff0ffffff81c61747f2450bfbbfffffff93fffffffc7ffe483fffffcd2850ffbbffffffffff73ffffcbffe483ffd5fccfc60bfbbfffffd9ffffd8b3fc7ffe581c63f44c27ffffbbffd7b56fffffffffc7ffe587ffd7fcc2450bfffffffffffd1fffb10ffffff85e6154bf2850ffbbfffffcefff33fb3fcbffe485c6ff48c27ffffbbffffb7ffc6ffffffc7ffe481e63ffcd2bffffbbffffffffff0bffffffffffffffffffffc5fff8df89efff92073fb3ffffffffdcfffffffc5fff8e6897b56560ffffffc7ffffffffd6ffffff0bffe68a1fff4bffffb10ffffffffffd643f27ffff8fffe1b7f93ffc5ffffffffffdcfd643f245fff8fffe1b7f93ffffffffffffffff63ffcdffffffb9f97f75657f73ffffffffff83ffd6ffffc5fffb9f95efff93f73fb3ffffffffffffffff246fffba6fd769657ffd8ffffffffffdeffffcdffffff2e6fff6992bf27fb3fffffffffffd7fffffffffb876ff699906fff13fffffffffffd7fff246fffba6ffffd993ffd8b3fffffff81c63ffffffffffba6957b5657fffffffcbfffffff67fffffff0bfbbf97ffff4bffc5110c7ffffffffffffffc5fffba6fff4ff4910bfb10c7ffff87ffffffffc50bffe697fffffd1fffb10fffffffdefff40effffff2c797fb7ffc627ffffffffff87f65643f27ffffbbfffffff93ffc5ffffffffffde63f47ffc5fffba6fffb7f93f0bfb3fffffffffffffffffc5fff8df89efcefcd33fb3ffffffffffffffff287fff8fffe1fcefcd318b3fffffffffffd5fccfc7fff8ffffffd9fe0fd8b3fffffffffffff43fffffff8ff897b4e54d33fb3fffffe6fff63f40cfc5fff8ffffffd6fe0fffb3fc7fffffdffd6fffffffffffffe14ff4bf0bfb10c7ffe6ffffd6ffffff0bffff8a1fff4bffffb10fffffffdf615fff2bffff8ff8a1b4efff33ffffc3ffe4fdc67ffff27ffff8ff8bfb7fffffc5ffffffffffdffff48e2bffff8fffffb7ffe00bffffffffffffffffffffc5fffb9fffffce54d33fb3ffffffffff6fffff2bffffb87fdefcefff30513fffffff8bffd5ffffc5fffb9ffdefcefcd33fb3fc3ffe5ffffd6ffffc6fff2dfffffff2bf27fb3fc3ffff8bfffffce2bffffbbffffffffc6705fffc3ffe683fffffcc27ffffbbf6d7fd6ffffd8fffffffe6ffffd7fffffffff2ff6fffce28dfd8b3ffffffffdeffffff2bffffb876fffcefc630513fffffff87fffffff287fffbbfffffcefcd318b3fc7fffffdffffffffff0ffbbffd7ffffcd33fb10ffffff89ffff43fffffffbbffd7b4e54d33fb3fc3fffffdf6fffcdfff0ff2fffffb56fff27ffffc7fffffff617fffffffffbbf0fffce4bf0bffd0c7ffffffffd7ffffc50fffffffffce4bf33fb10cbfffffdeffffcefc70ffffffffffffd127fb10ffffffffffd7fffffffff2c7fffb4e28627f13ffffffffff6d743ffc7fff2ffffffce2bf27fb3ffffffffde6fffff2bffffb87fffb4efff305fffffffff87f63f4bf2bffffbbf0ffb4efcd0bffffffffe5fdefff40effffff2c7fffb7f2bf27ffffcbffe683f67f47fffffff2ff0ffb7f2bfffffffcacfffffffd744c244ffffffffffd993fffffffc6dfff83f63ffccfc50bffff957fd6fffffffffc6cfff87f63ffccfc40bffff97fffffd1ffffd0fecffffdcfd548c244fff8fffff6bffe0fd8ffffedfe4fdc695fff27f0bf8ff8a1fffffffff13fc6cfe48bf6154bffc4fffffffdefcefcdffffffc7ffe483f61547ffc5ffffdf0deffffffffffffffffe485cfd548cfff0bffff6fffd9fc6fff13fcbfffffdefd544d286ffffffffffd9fff098fffc7ffff8bf63ffccfc50bfffffd7ffffd1ffffd0fedfff81d6bffcdfc60ff2fffd7fd6fff27ffffffffe589c6bf4cc27fffffffffffd6546ffffffcbffe5fdc6d7fff27f0bffffffffff4bffc5fd0cacfe587f6974fffc4fff2ffffffff28dffffffcadfe4fdd695fff2bf0fffffffffcefff305fffc6dfe487f6154bffc5ffffff0fffcefcdfffffffecffffff63f43fffffff8ff8bf74e93ffffffffedfffffffff40c245fff8e6ffffd6560ffffffc6cffffdcfd6ffffff0bffe68a1fff4bfffffd0fecffffdd63fffffc4fff8e68a1fce93f33ffffc2cffffddffffcefc4fff2e6fffffffe027ffffc2dfffffffd6fff27ffff8fffe1fff93ffff13fffffffffffff43f2c4ffffdffdefce90dfd8ffffecfff8ff63f43ffffffffff97f74efcdffffffc2cfff83f67ffffffffff2ff95e77f2bfffffffc6efffffffd644d2c5ffffdfffffff93f0bffffc2effffdcffffccfc6ffffe6fd769657ffd8fffcbffffffffffffffc4ffffe6fff4fffcd318fd0cbfffffffffffccfc40bffe66fffff491fd8fd0fecfff87ffff43fffffff2e66ff6bffcd27fffffeefffffffd743fffffffffffff68e90633f13ffffffffdefd743f2c4ffffffffffce93f318ffffecfff81effffcdffffff2e66ff6992bf27fffffeefffffffd740cfffffffffffffd9906fff13fc3fffffff6bffff2ffffffff957fcefff305fffffffff8dd63fffffc5ffffe6957fcefcdffffffc3ffff8ff6bffccfffffffff97ffd6fc6fc5fffc7fffffdd63ffcdfc5ffffe60fffd657f0bffffc7fffffff617ffffffffffe697f4ce4bf33ffd0caeffffff67fffffff0bffff97ffff4bffc5110c6effffdeffffcefc5ffffe6fffffffd10bffd0fedfff87fffffffffffff2ff97ffce286fff13ffecfff87f6bfffffc4fff2e697ffff28d27fffffffffffff697fff2ffffffff97ffce93ffc5fffffffff85d6174ff2c5ffffe60fffce93f0bffffcadfff81d67ffcdfc6fff2e60ffffffff0bffffcbfffffddfff4ce2ffffffc7ffffff9060bfffffecfffffffff43ffc4fff2dffde6992a0fd8ffffffffffffffffffffffff8c76de699fff70513ffecffffffffffff284fff8dffff6bffe0718fffc7ffffffffd6fffffffff8df89efff4bf73ffd0fecfe4fff63ffff2bffff8df8bf74efcd33fffffffffffffffffffffffff2c789e77f2bf24513ffecffffff67f40efc4fff2fffff77f2a0ffffffc3fffffff67ffce2bffff8ff8bf77ffff705fffffffe4fff63f48e285fff8dffffffffe00bfffffffffffffffffff27ffff8c7fd7696546fc5fffffffffffffff40c247fff8ffffffd6560fd8ffffffffffffffffffffffff2ff6e14d92bf258fd0fffffffffffffff27ffff8ff6fffd9491fd8fd0c2cffffdfffffff2bffff8fffff6bffcd318ffffecffffdffff43fffffff2fffe16bf2a027fffffffffffdcfd5fffffffff8c7fe1699ffffff13fc7fffffff63ffffffffff8ff0d7fd64910bffd0c7fffffff63fffffff0bffff8974d6fffffffd0fedffffffffffffffffff2ff897fd628624513ffedffffff6bffff27ffff8ff8bffd657ffc513ffecffffdf656fffffffff2ff8a14fffff27ffd0c2cfe6fff6bf43ffc4fff2ff8bffce28d27ffffc6dfe4fdd63f4bf2bffff8fffe1fcefff0bfffffedffffddfd6fffffffff2c7fe1fff2bf27f13ffedfe6fdd67f4cefc7fff2ffffffff2a00bfffffedffffddffffff2bffff8c7fe1ffffff08513fffffffffffffffffffffffc76d769654670513fc3ffffffffff40d2c6ffffdfffffd657f718fffc3ffe48fffd5ffffc4fffffffdefcefcdfd8ffffecfff83fffffffffffff2df6defd9fff258ffffeefff8fffd5ffffffffffff6de699fc6fff13fffffe483ffd5fcd286ffffdf0defd9fff098fffffffffffffffffffff0fffc7fff4d64bf73f110c7ffffffffffffffffffffdf0d7fd6fd10bffd0feefe5fff63f43ffc5fffffffff74e54dfffffffffffffffffffffffffff2c7fd775628624513fffffe5fff6fffcdfc6fff2dffff7562bf27ffffc3fffffff6ff43f2fffffffffd775657ffc5ffffeeffffff63f44dfffffffff0ff75657f0bffffc7ffffffffffffffc40fffdffdefce48d33ffd0fffffffffffffffffffff2c7fdefff28627f110ffffffffffffffffffffffc70de4ff486085110ffffffffffd6fff2ff0fffc7ffffff4bf73f110c7ffff8fffd6ffffc5ffffff0defff491ffffd0c2effffff6d5fffffffffffffde74effffc513fffffe58bffd643fffffff2c7fde77f28627f13fffffe48ff67f4bffffffffc70ff77ffc6fc5fffffffffffffffffffffffffc76d74d6486fc5110fffffffffffffff2ffffffff0d74d6491098fd0ffffe68ffffffccfc70bffff6d7fd6fd1fd8fd0ffffff81fffffcdffffff2ff6d76962bf27ffffffffff8dcfff40cfffffffff6d7696fc6fffffffffffffdffff44d2fffffffffff69657f0bffffcbffff87ffffffffc4fff2ff6fffd9fd1fd8fd0cbffffffffffffffffffffc70fffd94bf085110cbffffffffd7ffffff0bffff6fffd94bffc5110cbffe6ffffd7fff2c7ffffffffffff491098fd0fecfe687ffff43fffffff2ff6ff6bffcd27ffffcaefe485efd54bf287ffffff0fffcefcdfd8fffffffe681efd744dffffff2ffffffd92bf0bfffffeefe4fdefd54bffffffffc7fff699fc60bf13fc6effffdfffffff2ff0ffffffd7ffffff33ffd0ffffe5fdc6ffffffffffffc7fd74d64bffc5fd0c7ffff8df63fffffffffffff0d74fffd10bffd0c2dfff8bffffffffc7fff2fffd7fff28d27ffffc3ffe5fdd6bffff2ffffffffffffce57f305fffc7ffe68ff63f4fffffffffff0fffce54dfffffffedfff89dffffffffffff2c7fd7ffffc627f13ffedfff83f6bffffffffff2ff0d7fd62bf0bffffcacffffde6ffffffff0ff2fffff4cefff27ffd0c6efe6fff617ffffffffffff0fffce4bf0bffd0cbfffffffffffffffffff2c70ff4fffc6085fd0cbfffffdeffffcefff0fffc7fffffffc627ffd0cbffe687f67ffcefc7fff2ff0fffff2910bffd0cbfffffde67ffff2fffffffffff4ff4bf085fd0fedfe587ffd7fffffffff2ffffffce28627f13fcbffe4fff695ffffffffffff0fffcefff08513ffedfff87ffff4ceffffff2ff0fffff286fff13f >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
private theorem boardOK (w : Fin 26) (j : Fin 257) : (boards (w.val)).testBit j.val = true → (mins (w.val)) &&& (negativeWords (j.val)) = (mins (w.val)) := by
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
  | ⟨a+26,ha⟩ => omega
set_option maxRecDepth 12000 in
private theorem block0 : ∀ r : Fin 8, (union (r.val+0) (List.range 26) ||| (1 <<< (r.val+0))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block1 : ∀ r : Fin 8, (union (r.val+8) (List.range 26) ||| (1 <<< (r.val+8))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block2 : ∀ r : Fin 8, (union (r.val+16) (List.range 26) ||| (1 <<< (r.val+16))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block3 : ∀ r : Fin 8, (union (r.val+24) (List.range 26) ||| (1 <<< (r.val+24))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block4 : ∀ r : Fin 8, (union (r.val+32) (List.range 26) ||| (1 <<< (r.val+32))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block5 : ∀ r : Fin 8, (union (r.val+40) (List.range 26) ||| (1 <<< (r.val+40))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block6 : ∀ r : Fin 8, (union (r.val+48) (List.range 26) ||| (1 <<< (r.val+48))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block7 : ∀ r : Fin 8, (union (r.val+56) (List.range 26) ||| (1 <<< (r.val+56))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block8 : ∀ r : Fin 8, (union (r.val+64) (List.range 26) ||| (1 <<< (r.val+64))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block9 : ∀ r : Fin 8, (union (r.val+72) (List.range 26) ||| (1 <<< (r.val+72))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block10 : ∀ r : Fin 8, (union (r.val+80) (List.range 26) ||| (1 <<< (r.val+80))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block11 : ∀ r : Fin 8, (union (r.val+88) (List.range 26) ||| (1 <<< (r.val+88))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block12 : ∀ r : Fin 8, (union (r.val+96) (List.range 26) ||| (1 <<< (r.val+96))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block13 : ∀ r : Fin 8, (union (r.val+104) (List.range 26) ||| (1 <<< (r.val+104))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block14 : ∀ r : Fin 8, (union (r.val+112) (List.range 26) ||| (1 <<< (r.val+112))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block15 : ∀ r : Fin 8, (union (r.val+120) (List.range 26) ||| (1 <<< (r.val+120))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block16 : ∀ r : Fin 8, (union (r.val+128) (List.range 26) ||| (1 <<< (r.val+128))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block17 : ∀ r : Fin 8, (union (r.val+136) (List.range 26) ||| (1 <<< (r.val+136))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block18 : ∀ r : Fin 8, (union (r.val+144) (List.range 26) ||| (1 <<< (r.val+144))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block19 : ∀ r : Fin 8, (union (r.val+152) (List.range 26) ||| (1 <<< (r.val+152))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block20 : ∀ r : Fin 8, (union (r.val+160) (List.range 26) ||| (1 <<< (r.val+160))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block21 : ∀ r : Fin 8, (union (r.val+168) (List.range 26) ||| (1 <<< (r.val+168))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block22 : ∀ r : Fin 8, (union (r.val+176) (List.range 26) ||| (1 <<< (r.val+176))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block23 : ∀ r : Fin 8, (union (r.val+184) (List.range 26) ||| (1 <<< (r.val+184))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block24 : ∀ r : Fin 8, (union (r.val+192) (List.range 26) ||| (1 <<< (r.val+192))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block25 : ∀ r : Fin 8, (union (r.val+200) (List.range 26) ||| (1 <<< (r.val+200))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block26 : ∀ r : Fin 8, (union (r.val+208) (List.range 26) ||| (1 <<< (r.val+208))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block27 : ∀ r : Fin 8, (union (r.val+216) (List.range 26) ||| (1 <<< (r.val+216))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block28 : ∀ r : Fin 8, (union (r.val+224) (List.range 26) ||| (1 <<< (r.val+224))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block29 : ∀ r : Fin 8, (union (r.val+232) (List.range 26) ||| (1 <<< (r.val+232))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block30 : ∀ r : Fin 8, (union (r.val+240) (List.range 26) ||| (1 <<< (r.val+240))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block31 : ∀ r : Fin 8, (union (r.val+248) (List.range 26) ||| (1 <<< (r.val+248))) = 2^257-1 := by decide +kernel
set_option maxRecDepth 12000 in
private theorem block32 : ∀ r : Fin 1, (union (r.val+256) (List.range 26) ||| (1 <<< (r.val+256))) = 2^257-1 := by decide +kernel
private theorem checked (i : Fin 257) : (union i.val (List.range 26) ||| (1 <<< i.val)) = 2^257-1 := by
  have h (q : Fin 33) (r : Nat) (hr : r < 8) (hs : r+8*q.val < 257) : (union (r+8*q.val) (List.range 26) ||| (1 <<< (r+8*q.val))) = 2^257-1 := by
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
  obtain ⟨w,hw,on⟩ := member (List.range 26) full
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

private theorem baseGood (p : Fin 52) (a b : Fin 468)
    (cover : pos p.val &&& (neg a.val ||| neg b.val) = pos p.val) :
    ∀ w ∈ base, good p.val (52+a.val) (52+b.val) w := by
  intro w hw
  rcases List.mem_append.mp hw with raw | constants
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp raw
    have eq := congrArg (fun k : Nat => k.testBit j.val) cover
    simp only [Nat.testBit_and,Nat.testBit_or] at eq
    intro hp
    have yes : (pos p.val).testBit j.val = true := by simpa [input,p.isLt] using hp
    rw [yes,Bool.true_and,Bool.or_eq_true] at eq
    simpa [input,show ¬52+a.val < 52 by omega,show ¬52+b.val < 52 by omega] using eq
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at constants
    rcases constants with rfl | rfl <;> simp [good]

private theorem readGood {p a b : Nat} {s : List Column} (h : ∀ v ∈ s, good p a b v) (j : Nat) :
    good p a b (wire s j) := by
  unfold wire
  rw [List.getD_eq_getElem?_getD]
  cases e : s[j]? with
  | none => simp [good]
  | some v => exact h v (List.mem_of_getElem? e)

private theorem orGood (gs : List (Nat × Nat)) (s : List Column) {p a b : Nat}
    (h : ∀ v ∈ s, good p a b v) : ∀ v ∈ gs.foldl addOr s, good p a b v := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact h v old
    · obtain rfl := List.mem_singleton.mp last
      have hl := readGood h g.1
      have hr := readGood h g.2
      unfold good at *
      simp only [Bool.or_eq_true] at *
      tauto
end PEqualNP.Research.Plane975Family5Mask

open PEqualNP.Research.Plane975Family5Mask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Family5Mask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
    (tail : List Gate) (out : Nat),
    let s := ors.foldl addOr base
    let firstAnd := both (wire s left) (wire s right)
    let final := tail.foldl step (s ++ [firstAnd])
    (∀ p : Fin 52, firstAnd p.val = true → omittedFlags.testBit p.val = true) →
    (∀ p : Fin 52, wire final out p.val = true) →
    (∀ n : Fin 468, wire final out (52+n.val) = false) →
    9 ≤ tail.countP Prod.fst := by
  intro ors left right tail out
  dsimp only
  intro support hp hn
  apply separated_bound _ tail out _ hp hn
  refine ⟨idx,?_⟩
  intro i j lt
  obtain ⟨p,off,cover⟩ := retained i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact orGood ors base (baseGood p _ _ cover) w old
  · obtain rfl := List.mem_singleton.mp last
    intro on
    have no := support p on
    rw [off] at no
    contradiction
