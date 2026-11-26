import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975ResidualSharedMask
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
def omittedFlags : Nat := 0x6100000060000

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x160ae56eb358abd5aa952a853a9b4ca5d2a9145a250e8541a04fa793b9d4da6933994c6612f974b2572893496472290c823f1d8dc6a33188b456291389446210f87432150883c1a0b0481405fafb7d3e1eef67abd1e6f1783bddaec75ba9d2e872b89c2df6eb6db4d86bb59aad369345a0cf66b298ac461b017cbd5e2ed74b95c2d96ab459ac560af572b558ab552a550a75329548a25027d3c9c4da6932974b255249147235188b45225108743215088341204fe7e3e9ecf4793c1dcec74399c4e06f371b4d86b3519ccc6531988be5e2e970b65a2c960ae562913c9c4b251248e462290c82401f8f8783b1d0e46e361a8d06632188bc5c2c158a852281389446221088034190c0582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x2042c90a024a482018682a014aa02012ca0200a4d0a0068e01c4001c1c02114194021419020341900234988412818821301880138184021c182030c98143201812124181032498043281802134964000d9604049960004d954001594c001994841099480119944001d94241481422144142014c940c141940815194041499304061930006592c040992840299280429126040c9250405924040d122044c9210425920406912024649150205914021591142219110225910c24191082519104261110207490c841190c0419909412190905219088511908412910825301070604106060c90506059048611902c34010287409024348901c301901870190143211012524900c341100a5500e2000e0e100860e0008e0c881120c8011a0c420940c4009c0c301060c2010e0c101860c021940b810220b100260b010268a850280a8102a8a450880a430840a4108c0a2100e0a100a68a070a08a050a80a030a409890120981032094301409102260909212090303408a110a08891128887120888512808831308865208086120c884d2800849290884528808430940838302882d30008293028825308881c380081838288161a088143a008121a4880f180880d380080b19088071a00720046871000787000478644089864008d062004e8610087860c0c186080c386040c98590803858801385808138540815053080685108078508053050285484c480984c081904b090284a490804a090a8498103849490184909038488113848490984548818450885844488904428940430906842694084249480422944841c181841818384149810412984840c1c1040a1d084069c0839002383890038385021838102303290428310027830d04183090438305061030306482c500982c140902a940202a140a82984038290423828940382850290263404026140c824d081824508902434840223444821848302124a4820d0c1020b4c082070e081c580181c1811819482181908238189013818582101838300170a048165a000161a048154a018150a05814d20181492118145a010143814812d24001292428125a4001238448114a21810d241810786080e580800e1c0880c941180c580900c3c1000b850280a590800a3d00809850380949210092d20008b51080879200072c040070e048065a080063c04805c28180586818054a810052c84804d281004b49000387020032d04802f140802d340002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3f80000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffe00000000000000000000000000000000000000000000001fffc0000000000000fffffffffffffc000000000000000000000000000000000c001fff80000000007ff00000000001ffffffffffc00000000000000000000000000e003ffc0000003807ffc0000000ffc00000001fffffff0000000000000000e000801801fe00000003801f800000701fe000000ffc00007fffff00000000000e0038038000fe000181300c3e0000000e0ffc000781fe003f80007ffc000040a0813201386060f00030070100fc0003008601e00000c0f8183fe03e01ff8010002000e012000067020600400861e0084020e00f00101862001c0f18e0f03f07000e0000049606287882901020008f8211184e6478840300c18980404e679862400000060000c883b31000008906763806420480332585445820331124833baa90424892c8115120b5000143006a96da22804934d548a8130b49555e492551be3a90900400040408014108114928205b00004001516008046b020112127915b60000000000000000000002fefdfff707800000000007bfcff3e767fbfb198679da000000000000000000000000000000000bdfb7fcc80000003dfcceedb7cc4556000000017e806df4a8000000000000000000000000007ecf4000001b6daae41c14760000003f807fe8000000607dfa400000000000000000001feec0006ea48011df837e000007c3fe33c00007c0fff800007f87ff000000000000007f801ffbe000000000000000006660ef000787fc6f00003c3f8000077c0000000003f03a30000c1fe0587800e1800000000000014b818000e1c2f0004e0001ec000001e468f9f000361cccd8030007c3d538007100000000001698280936000a00d000050bee08d840008b944023c4001da45001000e6810802000000025028028100200410b8bbe93da0044840aa83b2025908007100d84880001a2a00000006900800000f8db62c23ee880e0273f63c9a044021dc0e800b2201100cd002a220001a22008000000000000000003e774636c01480e6bb8b60841ba1f01018004009000200000007f8ff6dfdf8c7400000000000003dfed8ff074f7b3cca7e1f0630c07404 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010000000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xfffaa6ffffff4cd2ffff3fffffffff57ffffff0feea65ffffffffffff0b3ffffff4ffffffc5110fffabfffffff4fffff0fffffffffff2bffffff0fffaffffffff4fffff0fffffffffffffffff130fedaa48ff6954fffc7ffffff0fffcefcdfffff0feda66ffffff4fffffff32ff0fffff2bffffff0fffa64ffffff4cefffff3fc7ffffffffffc5ff0ffffff81cffffffffffe7fe6957b56fffffffe8fffffffff63ffcdffffe7fff0ffb6993f0bffe8fffffffffffffcdffffefffffd775657f73ffe8ffffff83fffffffffffefaff0de769fff0bffe8ffffffffffd5fcdfff0efffffde769fff73ffe8fffffffffffffccffffefaff6fffd9fc6fc5fe8ffffe4ffffffffffc6feffea0ffffffff098fe8ffffe4ffffffffffc60affea6fffffffffd8fe8ffffe5fdcffffffffffeffeafd7b56fffffffe8ffffe5fdc617fccfc50affffffffe9fffffffd0fffffffff6fffffffffcfffffffb4efff305128ffffe4fdeffffffffffcffea0ffb7ffcd0bffe8ffffe4fdeffffff2850cfaeafffb7ffff33ffe8fffffffff6fffccffffeffffffffe9fc6fc5fe8ffffe4fde63ffcdffffeffeaffffe9fff0bffe8ffffffffffff40cfc5fe7fe6fd7b56fe0fffffffffffffdcfd6ffffffffffc78a1b7f93ffc5ffffffffffdcfd643ffc5ffffe6fe1b7f93ffffffffffa3ffff63ffcdffffe7bbf957fd6fff73fffffffffffdcfffffffc6fe7ba6fd7fd6ffffd8ffffffa3f87fffffccffffe7bbfffffd9906fc5ffffffa3fffffd7fcc246fe7ba6ffffd9ffffffffffffa3f81c63ffccffffe7fff957b7fffffffffffffa7fffffffffffff0bfbbf97ffffffffc5110fffa7ffdeffffffffffe7ba60ff4fffff0bffd0fffa7f87ffffffffc50bfba697fffffffffffd0ffffff87fffffceffffe72ff97fb7ffc6245ffffffa3ffde67f40dfc6fe7fe6fffb7ffff27ffffffffff87f67f40c27ffe7bbfffffff906ffffffffffffffffd5fffffffef8ff89e77ffff70513fffffe4ffffd5fcefc5feffdffdeffffe0fffffffffffffffffffccfc7fefffffd7fd6560fd8ffffffffffdcfd5fffffffeffc7fe1699ffffff13ffffffffdcfd5fccfc7fefffffe16bfffffd8ffffffaa6ffffffffffff0affff897fd6fffffffd0ffffe6fff63ffffffffcf8ff897b7f57f33ffffffffe6fff63f40cffffefffffd7fd6fe0fffffffffa66ffffd6ffffff0affff8a1ffffffffffd0fffffffdf615fffffffffffffe1b4efff33ffffffffe4fdc655ffffffffffc78a1b7fffffff13ffffffffdf615fceffffefffffe1b7ffff0bffffffffff8bffffffffc5fcfb9ffd7fff54dfffffffffa25fffffffcdffffeffdffd7fd6fff73ffffffffff8bffd5fffffffffbbffdefcefc6fc513ffffa3f8bffd5ffffc5fffbbffde74efcdffffffffffff8bffd6fffffffef2fffdefff286fff13fffffe583ffd6ffffc6fef2fffde77f2bfffffffffffff8bffd5fce2bffffbbffdeffffc6fffffffffa7f83ffd5fff2bffffbbf0deffffffffffffffffe6fffffffcdfc6feffff6d7696fff258fffffffe683fffffff246fefbbffd7fffffffd8ffffffa24fdeffffffffffcfb876ffffffff33ffffffffe487fffffff287fcfbbf6ffffffcdfd8fffffffe6ffffd7fcdffffeffff6fffd92bffffffffffa2487fffffccffffeffc7ffffd9fc6fffffffffaa4fffffffcd2bffefffffff699fff098ffffffabfffffffffffff0cfbbffd74cefff33ffd0fffabf8bfffffcc27f0bfbbfffffd6fffffffd0ffffff89ffff43fffffcfbbffd7b7ffcdffffffffffe5fdf6fffcdffffefffffd7b56fff27fffffffa7fffffffffffff0ef2c7fffffffff27f110fffa7ffdeffffcefc70efffffffffffff27ffd0fffa65fffffffff27f0bfb87fffffffffffffd0fffa25ffffd7fffffffcffc7fffb4e2bfffffffffffe5fff6d743ffc7fcfffffffb4e2bffffffffffa24fde6fffff2bffcffc7fffb4effffffffffffaa487f63ffffffffcfbbf0ffb7ffcdffffffffffe5fdefff40effffeffffffffff28627ffffffffe6fff656fcdffffeffff0ffb7f2bf0bfffffffffffdcffffffffffe7fe6fe14e9fe0ffffd0ffffffffffff4ffffffcffe6fe1fff90d33ffe8ffffffffffff4ccffffe7ffffe1fff920ffffe8fffffffffffffcdfc4fe7fe6ffffd92bf258fe8fffffffffffffff244fe7ae6ffffff93ffd8fe8fffffffddffffcdffffe7afffd7fd6fff0bffe8fedfff83fffffccfff0a7ffffd7fd6fffffffe8fffffffffffffffffffcfae697f4ce90d33ffd0ffffff87f617fccfff0a7fff97ffe9fffffffd0ffffff87ffff4ffffffcfaff97ffff90dffffe8fedffffff617fcdffffe7fffffffe9fff0bffe8ffffffffffffffffc4ffffdffdefd9fe0718fe8fffffffffffffffffffcf8ff89e74efcd33ffe8fffffffff615fcfffffffffffde769fe073ffe8fffffffdcffffffffffff8ff6e16bfffffc5128fffffffdcfffffffc4ffffeafe1ffffe0fd8fe8fffffffffffffffffffff8c7897fff57ffc5128ffffffffffff4cffffffffea0d7fff5600bffe8ffffe7ffffff4fffc50bffff897fff560ffffe8ffffe7fdc63fffffff0bffea8a14fffffffffd0ffffe4fddfd5fffffffcffea8a1fcefffffffe8fffffffff6bfffffffffffc70e1fe9fff085fe8fffffffff695ffffff0bffff8a1fffffffc5128fffffffddfd5fcffc5ffffeafe1ffffff0bffe8ffffffffffffffffc4ffffdf6defd92bffd8fe8ffffff83fffffff284fffadffdefffffffd8fe8ffffff83f63ffffffffffaff0d777f57f0bffe8ffffff8bffd5fffffffcfafffde74efcdffffe8fefffffff6fffcdfff0ff2fffde7692bf27ffe8feffff83f615fffffffffaff0defe9fffffffe8feffe785cffffff2440bfaffffffffffffd8fd0ffffe7fdefffffffc4ffffea6ff6bf2bf258fe8fffffffffffffff2bffffaff0ff6bffc6085128feffff87fffffff27f0bfaff6ff6bfffffc5128fefffffdeffffff286fffafffffffffff098fe8fffffffdc6fffffffffffafffd74ffffffc5fd0feffff89cfffffffc50bffeafd74fffffffffd0ffffff8bffff4ffffffff2fffd7ffffc6245128fffffffddfff4cdfc60ffffffd7fff2bf27ffe8ffffff8bffff4ff27ffffafffd7fffffffc5128ffffe781dffffffffffffaea0d7ffffffffffe8ffffe5ffffd7ffffff0cffeafff4ce2bf27ffd0ffffffffffffffffff0ff2fffff4e92bf245110fffffffde6fffcffc40ffffffff4e9fff27ffd0fefffffff6d7fff27ffffafffff4ffffffc5fd0ffffffffffff4ffffffcffffffffce286fc5128ffffe5ffffff4fffc40cffeaffffff28dffffe8fffffffffffffffffffcfaff0ffffffc6085128fedffffffffffff2bf0cfaffffffffffffc5128fedfe487ffff4fffc5fcffea0ffffffcdffffe8ffffffffffff4fffffffffff0fffe9286085fe8ffffffffffd74cffff0fffffffffff286fc5fe8ffffe7fff6974fffc6ffffff0fffe92bfffffe8ffffff87f6bf4cf2bfffffff0fffe9fc6fc5fe8fffa7ffffffffffffffe78dffdeffffe073ffd0fffffffffffffffffffcf8df89e74e90d33ffffffffffffffd640effffe7fff89e77f92073fffffffffffff6bffccffffe78fffd7fd6fc6fc5ffffeda3ffffffffccfc5fe7ffffd7fd6fe0fffffffffa7ffdcfffffffff0bf8e68a1ffffffffffd0feda3ffddffffffffffcf8e68a1fcefff33fffffffffffddfd6fffffffe7fc7fe1fff2bf27f13ffffffffddfd6fcefc4ffffe6fe1fff2bf27fffffedffffdcfd6fff27fffffc78a1fff93ffff13fffffffffffffffffc4fcffdffdefce90dfd8fffffffffffffffffffc4fe72dffdefd92bf258ffffffffffffffffcd2c4fe7fdffdeffffff718ffffeeffffff63ffcdffffe7ffffd7756fff73fffffffafffffffffffffffcffdf95e4cefffffffd0feefff8ff63f43fffffcffff95e77f90dffffffffffff83f656fffffffff2ff95e77f2bfffffffffffff83f616fcd2fffe7fff0defff93fffffffffffff8ffffffccffffe7ffffd7696fc6fc5ffffeeffffdcfffffffc6fe7fe6fd7fd6ffffd8ffffffaffffffffffffc4fcffe6ffffcefff318fd0fffaffffffffffffff0a7fff6fffd9ffffc5110fffafffffffffccfc40a7fff6fffffffffd8fd0ffffffffffffffffc4fcf2e66ff6bf28dfd8ffffeeffffdefff43fffffcfffffff6bf93f33f13ffeeffffdefff43f2c4fcfffffff6bf93f318ffffffa3ffdeffffcdffffe7fe6ffffd9fff258ffffeefffffffd740cffffe7fffffffd9fc6fff13ffffffffff6bffffffffcffc7957fcefff305ffffedfff8ddfffffffc5fcffe6fd7ffffcdffffffffffff8ff6bffccffffe7ffffd7fd6fc6fc5ffffedafffddffffcdffffe7fe6fd7fd6fff0bfffffffafffde63ffffffffcffe6fff4cefffffffd0fffa7ffffffffffffffe7fc70ff4fffff085110feea7ffff67fffffff0bffff97ffffffffc5110feea7ffdeffffcefc5ffffe6fff4fffff0bffd0feda3fffffd7fffffffcf2ff97ffceffffc513ffeda3f87f6bfffffc4fcf2e6fffffffcdfffffffedffffff697fff2fffcffffffffce93ffc513ffedaff85d6174ff2c5fcffe6ffffffffffffffffedfff87fffffceffffe72fffffffffc627fffffeda7f81d67ffcdfc6fe72e6fffffffff0bfffffedfff87ffff4ce2fffe7fffffffff9060bffffffffffffffd5ffffc4fcf8dffdefcefcdfd8fffffffffffffffffffc4fff2dffdefd92a0fd8ffffffa3fffffd5fcfffffff8fffdefd9fff73f13ffffa3fffffd5fcf284fff8fffdefd9fff73fffffffa67fffffffffffffff2df89efff2bfffffd0fffa24fff615ffffffffffdf89e74efffffffffffffffffffd6ffffffffffff89e77f2bf24513fffffe7fff65643ffc4ffffdffdefff2a0fffffffefffffff655fff2bffff8fffde77fffffc513ffefa64fff615fce285fff8dffdeffffe00bffffffffe7fdcffffffffffff8c76d76bf57ffc5ffffeffffffffff43f247fff8fffd7fff560fd8ffffffabffffffffffffffff2fffe14d9fff258fd0fffaa6fffffffff27f0bf8ff6fffffffffd8fd0ffffffffffffffffc4fcf2fffe16bf28d258ffffffffffdffd5fff2bffffffffe16bffff318ffffffffffdffff40ffc4fffffffe1fd9fe0258ffffefa3ffdcfd5ffffffffffc7fe1699ffffffffffffabffff63ffcfffffff8fffff4d6fe00bffd0fefaa6fff63fffffff0bffff8bffd6fffffffd0fffffffff6bffffffffff2c7897fd62bf245ffffffa27fff6bffff27fffffc7897fd6ffffc5ffffffabffdd63f4cffc5fffffffd7fd6fe00bfffffefa7ffdf616fffffffff8fffe14fffff0bffd0fedfe6fff6bffffffffcf2ff8a1fff28dfffffffedaa4fdd615fff2bffff8fffe1fcefff0bffffffffe7fddfd6ffffffffffc7fe1fff2bf27f13fffffe6fdd6564cefc7fffffffe1fff2a00bfffffffa7ffddfd5fff2bffff8c7fe1ffffff0bf13fffffff8ffffffcffffffffff6d7fff546705fffffffe783fffffff2c6ffffdf6d7fff57ffd8fffffffff8fffd5fffffffcffff6de68efc6fff13fffffe48fffd5ffffc4ffffff6de6bffcdfd8ffffffa2783fffffffffffff2df6defffffffd8fffffffff8fffd5fcffffffffff6defd9fc6fffffffffae483ffd5fcd286ffffff0defffffffd8ffffffae5fffffffff2ff0cffdfffffff57f33ffd0fffaffffffffffffff0fffffffffd657f705110fffafffffffffcf2c50fffffffffd6fff73ffd0fffffffff6fffffffffcfffffd774e546fc5ffffeefe5ffffff43ffc5fcffdffd7fff57fffffffffffff8bfffffcfffffff2fffd7756fc627fffffefa3f83f6ffffffc6fff2fffd7756fffffffffffffff8bf6ff40f2fffffffffd7fd6fc673fffffffae783f63fffffffffffdf0d775657ffffffffffa7fffffffffffff0ff2fffdeffffff245110fffa7f8bfffffcefc40ff2fffdeffffff27ffd0fffa7fffffd6fff2ff0ffffffff4fffff73f110feea678ff616ffffc5ffffdf0ffffffffffffd0feefff8bf6d5fffffffffffffde74efc6fff13ffeffff8bffd643fffffff2fffdefff286fff13fffffff8ff655fcefffffffff0de77ffc6fc5ffffffaffffffffffffff0bffc76d7fffffffff110fffaa68fffffffffc70bffff6d7ffffffffffd0feffff81fffffffffffff2fffd76bffff258fffffffe78dcfff43ffffffffc7fd76bffc6ffffffffffff81fffffff2fffffffffd76bffff098ffffffabffffffffffffffcf2ff6fffcefcdfd8fd0fffae7ffffd7ffffff0bffff6fffffffffc5110feeabffdefd7fcf2c7ffffffffffd9fff0bffd0ffffe687ffd743fffffcffff6fffff28dfffffffeefe4fdeffffffffffcffc76ff6bfffffff13ffeefe485effffff287fcfffffff6bfffffd8ffffefaa681efd7fcdfc6fff2ffffffd9fff098ffffffafffdeffffcf2bfffffc7fff699fc6085ffffffabffdfffffffffffcffff0d74cefff0bffd0feeabffdfffffff2ff0ffffffd7fff57f33ffd0fffafffdc6ffffffff0bffc7fd7fd657fffffd0fffabf8df63ffcfffffffffffff4d6fff0bffd0ffffff89dffffffffffcf2c7fd7ffffc6fc5fffc2dfe58bffffffffc7fcf2fffd7fff2bfffffffffffe5fdd6bffff2fffcffc7fd7fce57ffc5ffffedfe6ffffff4ff2fffcffff0d7fff54dfffffffffa3f89dffffcfffffff2c7fd7ffffc6fffffffffabf81d6bffffffffff2ff0d7fd6fff0bfffffffabffff6d7ffffff0ff2fffff4cefff27ffd0feeaa6fff617ffffffffffff0ff4cefffffffd0fffa7ffffffffffffffff2c70ff4fffff085110fefa7ffdefffffffff0ff2fffffffffff27f110fefa7f87f67fffffc7fff2ff0ff4fffffffffd0fffa67fde67ffff2ffffffc70ff4fffffffffd0feda25ffffd7fffffffcf2c7ffffff2bffffffffedae4fff6bffffffffcffc70fffceffffff13ffffa6787f67f4fffffffffff0fffff286fc5fff >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
theorem diagonalSeparated (k : Nat) :
    separated (base ++ [both (wire base k) (wire base k)]) := by
  refine ⟨idx,?_⟩
  intro i j lt
  obtain ⟨p,_,cover⟩ := retained i j lt
  refine ⟨p,?_⟩
  intro w hw
  rcases List.mem_append.mp hw with old | last
  · exact baseGood p _ _ cover w old
  · obtain rfl := List.mem_singleton.mp last
    simpa only [good, both, Bool.and_self] using readGood (baseGood p _ _ cover) k

end PEqualNP.Research.Plane975ResidualSharedMask

open PEqualNP.Research.Plane975ResidualSharedMask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975ResidualSharedMask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
