import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975AdditionalMask
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
def omittedFlags : Nat := 0xf0000f000

-- Fixed-width fields pack each finite table into a natural literal.
private def indices (i : Nat) : Nat :=
  (0x1d3e9747a1cfe572791c7e371789c3e170781bfdf6f779bbdd6e76fb5da6bf5bacd5ea751a5d268f3f9ecee733598cbe5b2b94c9e4b218fc76371588bedeef579bbddaeb74b9dc6e16eb5da6d164b1d86c15dae56eb358abd5aab54a9d4aa350a7536994ba55269146a2d0a83409dcea6f369acd2673298cc25f2e95caa451f8ec5a291389446210f874220f0682405fafb7d3e5eef67abd1e6ee76bb1d6ea74389b4d667b3594c662b1186c260b017cbd5e2ed74b95c2d96ab458ac15ead55aa952a853a993e9e4ca592a9247a35188b452210e8441a08fc7d3d1e4f073389c0de6531178b0492310c823e1e0ec72381a8d06632188c05e2e168b0562a148a04e261288c44210e06c34190a85026110803c1a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff

private def positiveWords (i : Nat) : Nat :=
  (0x40020000800040010000020a00000102002000040020000800040010000020100100002001000040002008800001008020000100100002001000040002000401000008008000100080002000100020080000400400008004000100008001004000020020000400200008000400080200001001000020010200400020004010000080080001000808020001000220000004010000080080001000800011000000200800004004400080041000880020010040400200208004002000044000000802080010010c002001 >>> (31*i)) &&& 0x7fffffff

private def negativeWords (i : Nat) : Nat :=
  (0x390023038800383840218b804228380023832004683108250b1042603102070310027030c0418308243030804383060608304861030406183028640b0242483020648300a4503008650b00426830024702c8001a2c080922c0009a298003229082122900232288003aa844288284029828102a22808292a8042a826000ca258081225208422508052250085224a080a248081aa44488824428902440898a424848242084a24080d2a4068c0a4048c824028d0228042a222044a21808322128242a124a402120a422110a222108252a106860a104a60210287020c2c1020c0c1820a0c0a2082c30a064a082060e082050e80204a490a044a882042c902028642a024a482018682a014aa02012ca0200a4d0a0068e01c801181c4001c1c2010c1c021141c0011c194021419020341900234988412818821301880138186020c184021c9824308182030c181032498043281802134960004d9540015950005594c0019948811194841099480119944001d94241481422144142014c940c141940414914021549280429924040d122044c91402159110225910c24191082519104261110207490c841190c0419908851190841291082530106060c9048611902c340102874090243481022544901870190143211012524900c341100a5500ca010a0c881120c8011a0c420940c4009c0c2010e0c021940a8102a0a4108c098901209810320943014092120609102260909212090303408a910288a510808a110a08891128887120888512808831308865208086120c884d280084929088452880843094882d30008293028825308081838288143a008121a4880f180880d380080b19088071a0864008d062004e86040c985880138580813854081505208468508053050285484c480984c081984a490804a090a849090384881138484909844488904428948426940842494804229440412984840c1c1040a1d084069c08309043030306482c1409828502902124a4020b4c081c580181c18118189013818582101838308165a0001638048150a05814d20181492118145a0101438140130a06812d240012924281278408125a4001238448114a21810d241810786080e580800e3c0000e1c0880c941180c580900c3c1000a950280a790080a590800a3d000092d20008b51080879200070e048065a080063c0480586818054a810052c84804d281004b49000387020032d04802f140802d340002b5408027940801c38180169a0800f1c0 >>> (28*i)) &&& 0xfffffff

private def boards (i : Nat) : Nat :=
  (0x3fffffffffffffffffff800000000000000000000000000000000000000000001fffffc00000000000003fffffffffffffe000000000000000000000000000000f80001ffe00000000001ffff8000000000fffffffffe00000000000000000000000000e00ffff0000000f8003fff0000007f00000000ffffff80000000000000010000000400060000000000100070000000600000007000003f0000000000001078000701e000ff800001c0060007e000000fe0000007e000187ffffc00000004038012408c01403c00101c00f0100f800e160fe000030fe0033e0001fff000010138001801c00019f80441814405063000c4800fc008460c0118fe00fc07f8000013800012182e02c30100b001c10017821023861c0210c1c00060fc71e383f0000000010000008010700004000020003800080001c000101010084100093986020298904201022004a4000004080ca393404290669c220406848318424213ba888022011012608c1129008481260508a5000026aaad2051b289294b7898a51bc024048000042805914389202008804209448442820d804036d30a114a2bc95b6000000000000000000000000000000000003f7fffe3c000001eff7befff6c679000000000dfee5dffb5a0000000000000000000000001dfbf9037ce7bdbdec45021fdd0000000c01eed600000000e0775a800000000000000016000007675ae42ed1fb06f80000fa0ebc028fc0000f81f68003807df20000000005eeb00036a4800000000000000000002e39f0efc0073ffcc01fc0ffc007cfe00000000fe01ff000000c3f039e0000f3e000000000000001a800078ff40018f0c000000001f0383e07f000b83f5de00630000283f2780f1800000000063803be2000fb000001e7776018b28000517100681f0e00044c6030049438018800000161800280140005d5f637fa96b2484e8a0b7da17b044bd402f4e6245008768904034280050402007c2d654730ee5801b241d17d4bd5c05440ad80659101c0f32030000015104000000000000000000000007f1b78597882120f4e804410c6804c240630800052200000007f37f0c7b8202800000000000000395bac00a02d870020200a001000200000000000000000000000000ff1b7de4340000000002f59e09678f0186003404 >>> (257*i)) &&& 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mins (i : Nat) : Nat :=
  (0x20000001000000080000004000000200000010000000800000040000002000000100000008000800400000020000001000000080000004000000200000010000000800000040000002000000100000008000000400000028000001 >>> (28*i)) &&& 0xfffffff

private def packed (i : Nat) : Nat :=
  (0xfffffffffffffff2860ffaffffffe9fff731b3fffffe4ffffffffffff0affea6f2fffffffffb3fffffe5fdcfffffffc6ffffeafd7b7f57fff1fffffffffffffff4bffffffffffff2b69fc6fff128fffffffdc6d5ffffc6ffffffff2b69ffffffb3ffffa7ffdc6554bf2470bffffff2fffffffffb30fffa7fffffffffffc60fffdfffffff2bf27fb30ffffffffffff4bffff0ffbbffff77ffc6705130fffa7ffffffffff2bffffb9f0ffffffff0b1ffffffa7ffffffffff2860ffbbffffffffff73fff0ffffe6ffffff47ffff0afbbf6fffff57ffffff0fffffffdffd5fffffffffbbfff2699fff0bfffffffaa4ffffd5ffffff0affff6fffd9ffffffb30ffffffffffffffffc7fffbbfffffd6fd1ff1b10fffffffdffffffffff0ffffffd7b56fff271ff0fffabffdc6ff47f27ffffffffd7b56ffffffff0ffffffffffffffffc70fffffff24fffd1271b10ffffe5ffffd6fff27ffefb87ff2fff486ffffffffffffffffd6fff247fffbbfffffff491ff1b10fffffffdffd6ffffffffffff0f2b7f2bf0bfffffffffffdffd647ffff0fffffff2b7ffff27fffffffa7ffdcfff4bffffffffc7ff2b7ffc6fff130fffffffdf655fff2bfffffffff2b7ffff0bfffffecfffffffff47f27f0bfaff6f26bf93fffffe8fffffffddffffffffffff2e6972fe9fff271ffffffffffff6bffff27f0bfaff97ffe9fffff1ffffecffffffffffff2bfff3aff6deffffff718fffffffffffffffffffff0f32dffde7692bf271fe8fecffffff6fffff2bf0ffafffff77ffff731ffffecfe4fdcfffffffff0b3fea6ffffffffffffffffffffffffff4fffffff3affffffff546fff128fedfe5fdcffffff246ffffeafd7fff57fff1ffffecfe4fdd695fff284ffffeaff2fe9fffffffffffffe5fddfffffffc40f3feaff2fff2bf27fffffedfffffffd54bffff0bfaffff2ffffc6fff128fffa7ffdc6564ff2440bffff97ffff93fff1ffffffffffffffffff2c4ffffdffff69993f718ff0ffffffffffffffffc4ffffdf95effffd1731fd0fecffffffffffffffffe72ff95e77f2bf27fff0fffffffff67f47f2c4fffffffff77f93f731fffffffffffffffffffc4ffffe6ff2fd9491fd8ffffffafffdcfff47ffff0bffe66ff699ffffffff0ffffffffffff4fffff0bffff97ffd6546fc5ff0fffffffddffffff2ffffffe60d7fd6fff0b1ffffffafffff6bfffffc60bffff97ffd6fffff1ffffeeffffffffffffffffe7fff9724ff486fff110fffffffdc67fffffc4ffffe6ff24ff491ff1ffffffa7ffddfd6fffffffff2e6ff2ffffff27ffffffffffffffff4fffffffffc70f2fff9060bfff0ffffffffffd64fffff0bffff97ffff906fff130fffffffddfd6fff2c6ffffe6ff2fff93f0bfffffecaa4fdcfd54bffff0b3fff6fffffffffffffffecfe6fdc656fff244ffffffffffff491ff1ffffffae4fffffffff284ff3fdf6fffd9fff718fffffffffffffffffffc4ff32dffdefff291271fffffffffffffd6fff2ffff3ffffde4ff48673f13fffffe5fffffffff2c4ffffdfffffff491731ffffecae4fff6ff4bf2840ffffffff77ffff73fff0feca65ffffff47ffff0ff2fffff77ffff27fff0ffffffffffff4bffffff3fff0de77ffc60bfff0feefffffffff4bffff0ffffffff77ffc673f130feefe4fff67ffff286ffffff0ff77ffff0b1ffffffffffdfffffff2ffff3ffffd76bf57f098ffffeefe6ffffff47ffff0b3fff6fffff57fffffffffffe6ffffffffffc4ff3fff6fffd9491fd8ffffeeffffdffd5ffffffffffffff2699fff0bfffffffffffff6ffffffffff3fc7fd74d6486fc5ffffeeffffff6fffff247fffffffff4d6491ff1ffffedaa5fdd6bf4ff2c70f3ffffd7fff57fffffffffffe6fdd6bfffffffff32ff0d7fd6fff0b1ffffffae5ffffff4fffffff3fc7ffffff546fffff0ffffe6fdd6bffff2ffffffff0d7fff57f0b1ffffecffffdffffffffc4fff2ffff24fffd1271ffffeefe5fdcfd6ffffffffffc7ff2fff486fffffffecaa5fddfff4fffff0ff2ffff2ffffff27fff0fedae4fddfd54bffff0ffffffffffffc6fff130fedfe4fdd695fff287ffffff0f2ffffff0b1ffffedfe6fddfd6ffffffff3fff0f2fff2bf0bffffffffe4fddfff4bffffffffc70f2ffffc60bfff0cbffffffffffffffc60bffe66fffff93ffd8b28fffffffff63fffffff0bffff957b56fffffffe8ffffffffffffffffc50bffe697f4e9fd1fffb10fffffffde63fffffc5ffffe6fffb6993f0bfb3ffffffffff61747ffff0bffff97ffe9ffffffb3fc7ffffffffffffffc50fffdffff77f57f73fb28fffffffff63ffff2bffefaff0de769fff0bffe8c7ffffffffd5fff2bf0ffafffdeffffff73fb28ffffffffffff4bffff0affff6ff699fc6fff128fffffffdeffffff286fefaeafffffffff098b3fcbffe4ffffffffffc60affea6ffffffffffffffffffffffffffffffc5feffeafd7ffffd1fffb10c7ffe5fdcfff47fffffefffffd7b7ffffffffe8fffffffff6d7fff27ffefaffffffe9486fc5fffffffe5ffffd7ffffc50bffeaffffff491fffb3fc7ffe4fde6154bf2850ffaffffffe9ffffffb3fcbfffffff6ff4bfffffefffffffb7ffc6fc5fe8ffffe4fde63ffff2bffffaea0ffb7ffff0bfffffffa3ffdc61643ffc50bffff97ffff93ffffb3ffffa3ffffffffffffffffb9f957fd6fff73fb3fc3ffffffffd6fffffffe7bbf95efff93f73fb3fffffffffffffffffc60bfba66d7fff57ffd8b3ffffa3ffdefffffffc6ffffe6fff6bffff258b3fffffffffffd743fffffffbbf6ff699906fffffffffa3fffffd7fff2460bffff6fffff93ffd8b3ffffa3ffdc63fffffff0bffe697fb56ffffffffffffffffffffffffffffe7bbf97ffff486fc5110ffffffffffffffffc5fffba6ffffff4910bfb3ffffa7fffffffffffc50bffe697fffffd1fffb10ffffffffffff43fffffff2ff97fb7f28627f13ffffffffff65643f27ffffffffffb7f906fc5ffffffa7ffde63f47ffc5ffffe6fffb7ffff0bffffc3fa24ffffd5fff2470affff6fffffffffd8fffc3fa26fdc63f43f27ffefffffd7b7ffffffffffc7fa66ffffd6fff2450bfffffffffffd1fffb10fffa25ffffffffffc50efb9fffffd657f73fb3fc3fa24ffffd5fff2850ffbbffffffffff73ffffffffffffffff43fffffefffffde77f286245fffc3ffe5ffffd6ffffc60fffdfffffff2bf27fb3fc3ffffffffff43f2bffefbbffde77ffc6705fffc7fa64fffffffff2bffefb9f0deffffff0bffffc3fffffdfffffffffffef2ff6d76bffff27ffffc3ffe6fffffffff27f0affff6fffff57ffd8fffffffe6fdefd743fffffeffff6ff6992bf27fffffffa24ffffff43fffffeffc76ff699fc6ffffffcbfabffdeffffff2bffffbbf0ffffffff098fffc7fabfffffffffffc50bfbbfffffd6fd1fffb10c3fffffdf6ffffffff0ff2fffd7b7ffff27fffffffffffffffffffffffef2c7ffffff286245110cbffffffffffffffc70ff2ffffffff29127fb10cbfa65fffffffff27ffffb87ffffff486ffffd0ffffe6ffffffffffc5fefbbf0fffff4910bfb3fc3fffffde6d743ffc70ffffffffb7f2bf27ffffc3fa24fde6ff43f2bffffffffffb7ffc6fc5fffc7faa4fde63f4bf2bffffbbf0ffb7ffff0bffffffffe5fdefff43ffffffffc7fffb7f28627ffffcbffe6fde67f47ffffffffff0ffb7f2bf0bffffcbffffffffffffffc4fe7ae6fff4fffd1fd8ffffecffffdefffffffc4fe7fe6fff6bffff258fe8cacfffffffff47f27f0a7fff6fffffffffd8fe8c7fffffddffffffffffe7ae60d7ffffff0bffffc6dffffff63fffffff0a7fff957fd6fffffffe8fecffffff63fffffc4fffae697f4e9fd1ffffffc6dffffdd617ffffc5fe7ae60fffe993f0bffffcecfe4fdcfff4bf2440bffea6fffffffffd8fffc6dfe7fdcfff4ff2450bfffffd7fff57fffffe8fffffffffffffffffffff2df6de6992bf258fe8cecffffffffffff2bffffafffdeffffff718ffffffffffff63ffffffffffaff0d775657f0bffe8ffffffffffffffffc4fffadffdefe949173ffffc6cffffff63f4bf2bf0ffafffff77ffff73ffffcecffffff6ff47ffff0ffffffde77f2bf27ffe8fefffffff615fff2bffffaff0ff769fff0bffffcbffffffffffffffc4ffffea6ffffffd1258fd0fffffffffffffffffffffaff6ff4d9486fc5110cbffe7fffffffff244ffffeaffffff491fd8fffffffe7fdefff47ffc4ffffeafff6bf2bf27fffffffffffdefff4bfffffffafffff6bffc6085fe8feffffffffff4bffff0bffff6ff6bffc6fff128fefffffdeffffff286fffafffff6bffff098ffffffffffffffffffffffffac7fd74d6486fc5fd0feffe5fdcfffffffc5ffffeafd74ff491ffffffffffffffffff4ffffffff2c7fd7fff28627ffe8cffffffddfffffffc60fffeafd7ffffff27ffffcfffffffffff4ff27ffffaffffffff546fc5fe8c7ffe7fddfffffffffffffea0d7ffffff0bfffffffffffffffffffffffff2fffff4e928627f110ffffe5fde6ffffffc4ffffeafff4ff29127fffffefffffff6d7fff27ffffaffffffff486fff110cbfffffdd6974fffc40fffffffffff2bf27ffe8cadffffff6954bf2bf0ffffffffffffc6fff128fedfe4fdd615fff285fffaea0ffffffff0bffffffffffffffff4fffffffffff0fffe9286085fe8ffffffffffd74fffff0ff2ffffffff28627f128ffffe7fdd697ffffc6ffffea0fffff2bf0bffffcbfffffff6bf4bf2bffffaff0fffe9fc6fc5fe8c2da3ffdc63fffffc50bffff97ffd6fffffffffc6ca7ffdc63fffffc40bffe6fffffffd1ffffd0c2dffffff65643f27f0bffffffffff906fffffffffa3ffffffffffffffe72df6defd9fff258fffc3fffffffffffff2c4fe7ffffdefff93f718ffffeeffffff63f43f2fffe7fff97f75657f73ffffc7ffffffffffffffc4fe7fdf95effffd173ffffc2cffffff67ffffffffe72ff95e77ffff27ffffc6effffff61647f2fffffffffdefff93f0bfffffeefffffffff43fffffe7ffffd76bf546fc5fffc2effffdcfffffffc60a7fff6d7fffffffd8ffffffffffffffffffffffe7fff6ff4d9486fc5110cbfaffffffffffffc4fe7fe6fffffffd1fd8fd0c2ca3ffdefd743f2c4ffffff6fffd993ffd8ffffeca3ffdefffffffc4fff2e6fff6bffff258ffffeefffffffd743fffffffffffff699906fff13fc3fffffff6bf43ffffffffff957fd6546fc5fffc7fafffddfffffffffffffe60d7ffffff0bfffffffffffffffffffffffe7fff0ff4ff486085110caeffffff67fffffff0bffff97fffffc6fc5fd0feea7ffdefffffffc5ffffe6fff4fffd10bffd0c6dafffdd6174ff2c5ffffffffffff93f0bfffffedfffffffd643fffffe72ff97ffff28627ffffcada7ffdd67fffffc6fff2e6fffffffff0bffffcbffffffffd64ff2ffffffffffffff90608513fc2ca27fff65643ffc4fff2fffde77f2bf27ffffc6fa64fff6154bf285ffffff0de77ffff0bffffc2ffe6fdcfff43f2470bffff6fffff57ffd8ffffefa24fdcfd543ffff0bfffffff6bffc6fff13fc6daa4fdd6154bf285fffffffffffffff0bffffceda66fdd6564fffc7fff2ff0fffff2bf0bffffffffffffffff43ffffffffff6ff69654673f13fc3ffe7fffffffff2c6ffffdfffffff57f718ffffffa27fffffffffffffff2df6defd9fff27fffffeefffffffd543ffffffffff6de699fc673ffffcffae4ffffd5fff286fffffffdeffffff098fffffffffffffffffffffffffc7fd74d6fc6705110ffffffffffffffffc5ffffdf0d7fd6fd10bfffffeefe5fff63f43f2c50ffffffff77f57f73ffffffffffffffff43fffffff2fffd775628627fffffefa3ffff6ffffffc60ff2dfffffd6fff27fffffffffffff6ff43f2fffffffffff77f546705ffffffae7fff63f47f2ffffffdf0fffff57f0bffffc7fae5fffffffff2c40fffdffdefff49173ffd0fffffffffffffffffffff2c7fde4ff28627f110cffa7fffffffffffc40ff2dffffffffd127ffd0ffffffffffffffffffffffc70de4ff486085110cfffffffffd6fff2ff0ffffffdeffffc6705fd0ffffe7ffffd6ffffc5ffffdf0defff4910bffd0c2effffff6d543f2bf0ffffffff77ffc6fff13ffeffffffffd643fffffffffffde77f28627f13fceeffffff67f4bffffffffff0ff77ffc6fc513fffffffffffffffffffffffc76d74d6fc6fc5110cfffffffffffffffc7fffffffd7fd6fd1098fd0cfffffffffffffffc70bfffffd7fd6491fd8fd0c2fffffdfffffffffffff2fffd76bffff27fffffeefe7fdcfff43ffffffffc7fff6bf546ffffffcffffffdffff47f2fffffffffd76bffff0bffffcbfabfffffffffffc4fff2ff6fffd9fd1258ffffffffffffffffff2ffffffc70fffd9486085fd0fffae7ffffd7ffffff0bffff6fffd9fc6fff110cbffffffffd7fff2c7ffffffffffff491098fd0caeaa4fdefd54bf287fffffffff6bffff0bfffffefaa6fdefd747fffffff2fffff6bffff0bfffffeeafffdefff4bffffffffc7fff6bffc60bf13fc6eabffdf63fffffc50ffffffd7fd6fd1ffffd0cffafffdc6fffffffffffffffd74d6fc6fc5ffffffffffdf63fffffc5ffffff0d74d6fd10bffffc2da3ffdd6bfffffc70ff2fffd7ffffff27ffffc3fa25fdd6bf43f2ffffffffffffff546fc5fffc7faa6fdd63f4ff2ffffffff0d7fff57f0bfffffffa3ffddfff43fffffff2c7fd7fd628627ffffcffabffdd6bffffffffff2ff0d7fd62bf0bffffcacabffde6ffffffc40ff2fffff4ff29127fffffeefe6fde617fff2c5ffffff0fffff4910bfffffffffffffffffffffffff2c70ff4ff286085110fefa7ffdefffffffff0ff2fffff4fffc627f13ffefffffff67fffffc7fff2ff0ff4ff2910bffd0ffffe7fde67ffff2ffffffff0ff4fffc6085ffffeda25fddfd743ffff0fffffffffff286fff13fcbfae4fdd6bf4bf2bfffffff0ffffffc6085ffffffa67ffffd64fffffffffc70fffff286fff13f >>> (156*i)) &&& 0xfffffffffffffffffffffffffffffffffffffff


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
end PEqualNP.Research.Plane975AdditionalMask

open PEqualNP.Research.Plane975AdditionalMask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975AdditionalMask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
