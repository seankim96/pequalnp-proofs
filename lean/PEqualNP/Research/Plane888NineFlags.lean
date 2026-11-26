import PEqualNP.Research.OrderThreePlanePrefixData
import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane888NineFlags
open OrderThreePlanePrefixData PlaneFirstAndSeparation PlaneFirstAndBudget

def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 &&& b 13) <<< 26) ||| ((b 0 ||| b 14) <<< 27) |||
    ((b 1 &&& b 13) <<< 28) ||| ((b 1 &&& b 18) <<< 29)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def base : List Column := List.ofFn (fun j : Fin 30 => input j.val) ++ [fun _ => false, fun _ => true]
def omittedFlags : Nat := 0x1604e3

private def indices : Array Nat := #[
    0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12,
    13, 15, 16, 17, 18, 19, 20, 22, 24, 26, 30, 32,
    33, 34, 35, 37, 40, 41, 42, 44, 46, 47, 48, 49,
    50, 51, 53, 55, 59, 62, 63, 64, 65, 69, 73, 74,
    75, 76, 78, 79, 80, 83, 86, 87, 88, 89, 90, 92,
    93, 94, 98, 101, 102, 103, 106, 107, 108, 110, 111, 112,
    115, 118, 119, 120, 121, 123, 125, 126, 127, 130, 131, 132,
    133, 134, 135, 136, 137, 138, 140, 141, 142, 145, 146, 149,
    150, 151, 153, 154, 155, 156, 157, 158, 159, 162, 163, 164,
    165, 166, 168, 170, 171, 173, 175, 176, 177, 178, 179, 180,
    181, 182, 183, 185, 188, 189, 190, 192, 195, 196, 197, 198,
    202, 205, 208, 209, 211, 213, 214, 215, 218, 219, 221, 223,
    225, 226, 227, 229, 231, 232, 233, 234, 235, 236, 237, 239,
    240, 241, 243, 244, 245, 246, 249, 250, 251, 254, 256, 257,
    258, 259, 260, 261, 262, 263, 266, 270, 271, 272, 273, 276,
    278, 279, 280, 281, 282, 283, 285, 287, 288, 289, 290, 292,
    293, 294, 297, 298, 299, 300, 303, 306, 307, 309, 310, 311,
    313, 314, 315, 317, 318, 319, 320, 321, 322, 323, 328, 330,
    331, 333, 334, 335, 336, 337, 338, 340, 341, 342, 343, 344,
    345, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357,
    360, 363, 364, 366, 369, 371, 372, 374, 375, 376, 377, 381,
    383, 385, 386, 387, 389]

private def positiveWords : Array Nat := #[
    201334785, 268443650, 8200, 8704, 134234114, 134234116, 134234128, 134235136, 32772, 32776, 32800, 34816,
    65544, 65552, 65600, 69632, 134348801, 131088, 131104, 131200, 537133058, 262176, 262208, 262400,
    524292, 524352, 524416, 524800, 1048584, 1048704, 1048832, 1049600, 2097168, 2097408, 2097664, 2099200,
    4194336, 4194816, 4195328, 4198400, 142606337, 8388672, 8389632, 8390656, 16777218, 16777344, 16779264, 16781312,
    167772161, 33554436, 33554688, 33558528]

private def negativeWords : Array Nat := #[
    134279616, 134310304, 134333313, 134379840, 177472, 134402880, 208132, 231170, 308368, 134533761, 339076, 134564481,
    134579841, 408580, 134633992, 462340, 470020, 134773024, 570640, 134826273, 134841603, 134895880, 724226, 754946,
    801808, 135026697, 135042065, 924680, 135297120, 135320129, 135350817, 135420480, 1217090, 135451200, 1247750, 1325076,
    135551489, 135565841, 135596549, 1448452, 1587248, 135827475, 135858211, 135874593, 136058897, 136343776, 2172068, 136414339,
    2241604, 2266178, 2372740, 136597641, 136615041, 136643717, 2495500, 2503684, 136859689, 136877059, 136905763, 2757642,
    2790402, 137106441, 3158116, 137400387, 137416769, 137429031, 3313730, 137891875, 137908257, 137953315, 138439104, 4235728,
    4270468, 138510723, 138527105, 4335940, 138561864, 4393222, 4466836, 138692745, 138741893, 138955017, 138969363, 139004163,
    139020545, 139034883, 4851978, 139086088, 4917506, 139200537, 5253204, 139493459, 139528199, 5441542, 139724821, 139986963,
    140017683, 140052483, 140525769, 140542147, 140558529, 140574855, 140607619, 6422606, 140771469, 141557831, 141590595, 141623303,
    7471174, 142635424, 142660480, 8462756, 142689184, 8487810, 142758664, 8557314, 142791424, 8585990, 8618754, 8663188,
    142889608, 8688272, 8695952, 8786444, 143151400, 143159584, 8950034, 9048330, 9449524, 9474578, 9503270, 9572870,
    9711636, 9965618, 10498212, 144724136, 10551462, 10620942, 10752140, 10760324, 11014186, 145248296, 11538470, 11599910,
    12062754, 12591508, 12616082, 12648838, 12681602, 12714254, 12779782, 12845212, 12853396, 13107482, 13140242, 14680206,
    14745734, 14811150, 16819536, 151044929, 16852260, 151077665, 16917828, 151143240, 16942912, 16975620, 17008384, 151291409,
    151324165, 151356929, 17171980, 17237508, 17311024, 151535913, 151586081, 151782425, 151815185, 17834100, 152060513, 152109605,
    152306197, 152338961, 152371717, 18883684, 153108585, 153158693, 19006540, 153355277, 153420805, 19268620, 153617449, 153682977,
    153879561, 154140773, 154206245, 20980052, 155205961, 155222353, 21102924, 155451421, 155713817, 155746577, 155975705, 156237909,
    156270673, 156499989, 157286477, 23199820, 157548557, 158335045, 25174324, 159400744, 25232164, 25239844, 25428508, 25690424,
    25698608, 26214964, 26222644, 26280484, 26477076, 29360412, 29368596, 29622300, 29884696, 167799008, 33596624, 33631392,
    167856800, 33654402, 167922248, 33719874, 33754626, 33785346, 33827984, 168053384, 33851024, 33858704, 33885824, 33893504,
    33951240, 34090032, 34147362, 34212874, 34352144, 34613360, 168839776, 34636370, 34671138, 168905248, 34736706, 35129394,
    35194914, 169885928, 169894112, 35685570, 35718306]

private def boards : Array Nat := #[
  0x37fb7db7de3828000000000000f7fda3f863ba7389e7066181a04, 0x19d8c03a000000000000000003e7dd32ec06a1eebb96c222e9e02860500d00080, 0xfe77e8ce3eda0d2539eacf5d08a09ba07401690240e540cc0001a440, 0x20090841a0c9c5d16d00a4082aa036809904018402c29000294800000a204000,
  0x8b23405f7c43fa8003390804786003346800001ce0440800000132805040100, 0x17b66001a0fbc0006c38e70030001f1e53001a0000000003a45006d00500a0002, 0xe4e000c60002d87a0586001cc00000000000169c0c0018c5c0032003b0000039, 0x1e000fc3e0000000000000000199e0dc00783e17c0001c7c0003ce00000001f07,
  0x161bc03780000707fc67e0000f07fe00001fe3fc00000000000fe00ff, 0x7c15bf01a580000007c0ffa8000000e0b7f400000000000000000f7e000daa4, 0x1801ff7ac00000001fe81dff54000000000000000000000003ef7c0000dd5b5d0, 0x1f7fcd5a00000000000000000000000000000002f7dbf94000001ddcdb6bec4a,
  0x17efbff9c60000000001dfbdf33bbbf266339, 0x4032a40e4524000800821005410208512480a000040049c0408561081107255b, 0x62400852000800100104200a80002080311560140092945101082812f22a4a2f, 0x808032a400001220002102d0c4140002465a44590824068592128223249413b5,
  0x11304c3380830000492484b631058810400638862313927220420cc4440d99cc6, 0x40903c00000804024000c7c20600208887c108021c0380418c3008788e1e0f8, 0x11fc009041248138718f8001800c100f8001004201c00020fc10f80f01ff00, 0x181e000101800701c001f00006013020f000000383fe00383f001f000ffe0000,
  0x1fe000001e023806007e00000001c03f00001e03fc00003fc0001ffff0000000, 0x1e00000000003c007ff8000003801ffc000001ffc0000003fffffe00000000000, 0x1e003fff8000000003ffe000000001fffffffffc00000000000000000, 0x1fffc0000000000003fffffffffffe000000000000000000000000000,
  0x1ffffffffffffffffc000000000000000000000000000000000000000, 0x1fffffffe00000000000000000000000000000000000000000000000000000000]

private def mins : Array Nat := #[
  0x8000001, 0x2, 0x4, 0x8,
  0x10, 0x20, 0x40, 0x80,
  0x100, 0x200, 0x400, 0x800,
  0x1000, 0x2000, 0x8004000, 0x8000,
  0x10000, 0x20000, 0x40000, 0x80000,
  0x100000, 0x200000, 0x400000, 0x800000,
  0x1000000, 0x2000000]

private def packed : Array Nat := #[
  0xcada6787f6564ffffffff2ff0fffffffffc8fff, 0xcadae487f6954ffffffcffff0fffceffffff13f, 0xfeda25fff697fffffffff2ffffffceffffc813f, 0xcaea6785e656fce2fffffffffffffffff0bffd0,
  0xfeffff87f67ffffffffff2ff0ff4ffffffc8fd0, 0xfefa7ffde67fffffff0ffffffff4fffff24813f, 0xfeeaa6fff617ffffffffffff0ff4cefffffffd0, 0xcacabffff6d7ffffc4fffffffff4ceffffc8fff,
  0xcffabf83f6bffcdfffffffff0fffd6fff088fff, 0xc2da3f89d6bffcffff0ff2ffffffd6ffffc8fff, 0xc7ffe68ddfff4fffffffffff0d7ffffcd0bffff, 0xc2dfe589dfff43f2ff0ffffffd7ffffcd33ffff,
  0xc2dfff8bf6bffffffffcf2fffd7fceffffc8fff, 0xfffabf8df63ffcfffffffffffff4d6fff0bffd0, 0xceeaff89c6fffccfff0bffffffffd6ffffff110, 0xc6eabffdfffffff23f0ffffffd7ffffff33ffd0,
  0xc7fabffdfffffffffffcffff0d74cefff0bffd0, 0xcaeafffdefd5fcf2fffffffffff699fff098fff, 0xfefaa681efd7fcdffffff2fffff699ffffc8fff, 0xfeefe4fdeffffff2fffcfffffff6bffcd31813f,
  0xfecfe687ffff43ffc4fff2fffff6bffcdfc8fff, 0xcbfae7ffffd7fff27f0bffffffffd9ffffd8110, 0xcbffe6fffffffff2c4fcfffffffffffcd318fd0, 0xcbffe6fffffffffffffcf2ff6ffffffcdfc8fd0,
  0xcffffffdfffffcd2ffffffffffffd657f098fff, 0xfeefe78dcfff43f27f0bfffffff6bf57ffd8fff, 0xfeffff81fffffffffffff2ff6d76bfffffc8fff, 0xcfffff8ffffffff27f0bffff6d7fff57ffd8fd0,
  0xceea648ff655ffffffffffff0defffffffff13f, 0xfeffff8bf65643fffffff2fffff77fffffc813f, 0xc2efff8bf6d5fffffffffffffdefcefcdfff13f, 0xcffa7fffffd6fff2ff0fffdffffffffff73f110,
  0xcffa7f8bf67fffffc4ffffdffff4ffffffc8fd0, 0xfffffffff67ffffffffff2fffde4ffffffc8110, 0xc7fae5fffffffffffffcffdffdefcefffffffd0, 0xfffae783f63fffffffffffdf0d777f57fffffff,
  0xfeea258bf6ff40f2ff0fffdffd7fff57f73ffff, 0xfefa3ffff6ff40dffffff2fffff756ffffc8fff, 0xfeefe58bffff43fffffcfffffd777f54dffffff, 0xfffafffff63ffcffff0fffdfffffd6fff73ffd0,
  0xcffae483ffd5fcd2fffffffffdefd9fff098fff, 0xfffa2783ffffffffc4fff2df6defffffffc8fff, 0xc3ffe48ffffffff2c4ffffdffdeffffcdfd8fff, 0xc3fffffffffffff2fffcffdf6deffffff31813f,
  0xffffe7fffffffcd2ffffffdf6fffd657f718fff, 0xceda64fddfd54ceffffffffffe1ffffff0bf13f, 0xc6daa4fdd615fff23ffffffffe1fcefffffffff, 0xc3ffe6fff6bffffffffcffff8a1fceffffc8fff,
  0xfefa7ffdffd6fff23ffff8fffff4fffff0bffd0, 0xfffffffdf67fffffffffffff8a14ffffffc8fd0, 0xfffabffddfff4cf23ffffffffd7fff5600bffff, 0xfeda27fdc6bf40c27f0bffff897fff560ffffff,
  0xfffffffff6bffcffffffffff8bffd6560248fff, 0xfedfe6fddffffff23ffcf8fffd7fff57f33ffff, 0xfefabffff63ffff23f0bf8fffff4d6fffffffd0, 0xfefabffffffffff23ffff8fffff4d6fff0bffd0,
  0xfefa3ffdcfd5fff27ffff8fffe16bfffffd813f, 0xfffffffdffff40fffffff2ff6e16bffe0248fff, 0xc2cfe4fdfffffffffffcf8fffe16bfffffd8fff, 0xfffabffffffffff244fff8fffff4fffe0fd8fd0,
  0xcffffffdfffffffffffffffffe1fd9fe0248fd0, 0xfeffffffffff43f27ffff8fffd76bf57ffd8fff, 0xfefa64fff615fce23ffff8df0de77ffe00bffff, 0xffffe7fff67f43ffc4ffffff89e77ffe0fc8fff,
  0xfffffffff67ffffffffff2ff89e77ffe024813f, 0xfeca24fff615ffffffffffff89e74efffffffff, 0xfffffffff67ffffffffff2df89e4ffffffc8fd0, 0xfffa3ffffffffcffc4ffffdffdefd9fe0fd8fff,
  0xffffffffffd5fffffffff8dffdefd9fff71813f, 0xc3ffe4ffffffffffc4fcf8dffdeffffcdfd8fff, 0xcada7ffddfd64ce2fffe7ffffffffffff0bf13f, 0xfeda7f81d67ffcdffffe72e60fffffffffc8fff,
  0xc6daff85d6174ff23ffcffffffffce93fffffff, 0xfffa3f87f6bfffffc4ffffe697ffceffffc8fff, 0xfffa3ffff6bfffffffffffe697ffce93f24813f, 0xfeea7ffdeffffceffffe7fe6fff4fffff0bffd0,
  0xfeea7f85c67fffffff0bffe697ffffffffff110, 0xfffafffde63fffffc4ffffe6fff4cefffffffd0, 0xfffaff81dffffcdfffffffe60d7fff57f0bffff, 0xfeda3f8dc6bffccfff0bffe6957ffffffffffff,
  0xffffff8ddfffffffffffffe6957fff54d33ffff, 0xfeefffffffd740c27fffffffffffd993ffd813f, 0xfeca3ffdeffffcdfc4ffffe6ffffd9fff248fff, 0xfffffffdefd743f2c4ffffffffffff93f318fff,
  0xffffffffffd7fff2ffffffffffffce93f31813f, 0xfffa3ffdefffffffc4fff2e6fff6bffcdfc8fff, 0xfffafffffffffcc244ffffe6ffffd993ffd8fd0, 0xfffaffffffd7fff27ffe7fffffffd993ffd8110,
  0xffffffffffd7fff2ffffffe6ffffce93f318fd0, 0xfeeffffdcfff43f27ffe7fe6fd76bf57ffd8fff, 0xfeefff83f616fcd23fffffff0defff93fffffff, 0xfecfff83f67ffffffffe72ff97f77fffffc8fff,
  0xffffff8ff63f43ffffffffdf95e77f90d33ffff, 0xfffaffffffffffffffffffdf95efce90dffffd0, 0xfeefff83f63ffcdffffe7fff957756fffffffff, 0xc3fffffffffffcd2fffe7fffffffd993f718fff,
  0xc2cffffffffffcdffffe72fffdefd9ffffc8fff, 0xfffffffffffffff2c4ffffdffdefce90d318fff, 0xfedffffdcfd643f27ffffffffe1fff93ffff13f, 0xfffffffdd67ffcefc4ffffe68bfffffe0fc8fff,
  0xfffffffff67ffffffffe7fe68a1fff92024813f, 0xfffa3ffddffffff204fff8e6fe1ffffff33ffff, 0xfffffffff6bfffffffffffe68a1fcefcd248fff, 0xfeca7ffdcffffffffffe78e6fff4fffffffffd0,
  0xfeda3ffdcffffccffffe78e6fd7fd6fffffffff, 0xfecfffffffd640e23ffffffffdefff92073ffff, 0xfffffffff67ffffffffe7fff8bf77ffe0248fff, 0xfffffffffffffffffffcf8df89e74e90d33ffff,
  0xfffa7ffffffffffffffe78dfffffff92073ffd0, 0xfedfe485d6954cfffffffaff0fffe9ffffff128, 0xfffffffff6974cffff0fffffffffe9fff24813f, 0xfedfe487ffff4ffffffcfaff0ffffffcdffffe8,
  0xfedffffddfd54fffff0cfafffffffffff33f128, 0xffffe5fdd6bf4fffc4fcffeaffffffffffc8fff, 0xfefffffff6d7fff27f0bfafffff4ffffffff110, 0xfffffffde6d7fcffc4fffffffff4e9ffffc8fff,
  0xfffffffff6d7fcfffffffffffff4e9fff24813f, 0xfecfe5fdeffffff23f0fffeafff4fffff33ffd0, 0xfffffffde6ffffffc4fcffeafff4ceffffc8fff, 0xffffe781dfff4ff23ffffaffffffff57f0bffe8,
  0xfedfe58bffff4ff27f0bfaffffffff57ffff128, 0xfffffffdd6bffcdfff0fffeafd7fd6fff248fe8, 0xfffffffff6bffcdfffffffea0d7fd6fff088fff, 0xfeffff89cffffffffffffaeafd74fffffffffd0,
  0xfeffff87fffffff27f0bfaff6ff6bfffffd813f, 0xfefffffffffffffffffffaea0ff6bffff098128, 0xfecfe7fdefffffffc4fff2ea6ff6bffff248fe8, 0xfecfe785cffffff244fffaffffffffffffd8fd0,
  0xfeffff83f615fffffffffadf0deffffffffffe8, 0xfffffffff6fffcdfc4fffffffde769fff248fe8, 0xc6cfe48bfffffffffffcfadffdeffffffffffe8, 0xfecfff8bf63ffcf23f0ffadffdeffffff73ffd0,
  0xffffe783fffffffffffffadf0d777f57fffffe8, 0xcfffff83fffffffffffffaff6de6bfffffd8fe8, 0xfffffffddfd54cfffffffffffe1fe9fe00bffe8, 0xfffffffff6954fffff0bffff8bffe9fe0fff128,
  0xffffe4fddfff4fffc4fcffeafe1ffffcdffffe8, 0xffffe7fdc63fffffffffffea8a14fffffffffd0, 0xffffe7ffffff4fffff0bffff8bffd6560ffffe8, 0xffffffffffff4cffffffffeafd7fd65600bffe8,
  0xfffffffdcffffff244fff8eafe1ffffe0fd8fe8, 0xfffffffffffffff27ffff8fffe16bfffffd8128, 0xfffffffff63ffcffffffffdf89e769fe073ffe8, 0xc6cfe4fffffffffffffcffdf89e77ffffffffe8,
  0xcfffffffffffffffc4ffffdffdefd9fe0718fe8, 0xfedfffffffd74cd23fffffffffffe993f0bffe8, 0xfffffffff697fcdfffffffff97ffe993ffc8fff, 0xffffff87ffd74ff23ffffaffffffff90dffffe8,
  0xfffffffff6bfffffc4ffffe697ffcefcdfc8fe8, 0xfecfff87f63ffccfff0bffff97f4e9fffffffd0, 0xfecffffdeffffff23ffcfaff97f4fffff33ffd0, 0xfedfff83ffff4fffff0bffff957fff57fffffe8,
  0xffffffffffff4cd23ffe7aff0d7fff57f0bffe8, 0xfecffffffffffff27ffe7affffffff93ffd8fe8, 0xcbfffffffffffcdffffe7ffffff69993f248fe8, 0xffffffffffff4ccfff0a7fff8bffe9920ffffe8,
  0xffffffffffff4ffffffcffe6fe1fff90d33ffe8, 0xc6cffffffffffccffffe7ffffe14e9fe0ffffd0, 0xffffe6fde67ffffffffeffff0ffb7ffff088fff, 0xffffe5fde65640efff0ffffffffb7ffff248fff,
  0xfffabf87f615fffffffffbbf0ffb4effffffb3f, 0xfffa3f85e6d543ffff0ffffffffb4effffff13f, 0xfffa6685e63ffce23ffffbbf0ffffffffffffd0, 0xfffa6587ffd6fcc27f0bfbbffffffffffffffd0,
  0xfffffffde67ffcefff0efffffff4fffff248b10, 0xfffabf87ffd7fff23f0ffbbfffffcefffffffd0, 0xfffffffff6fffffffffcf2fffff4cefff248b10, 0xfffffffdf6fffcdffffefffffffb56fff248fff,
  0xffffff89ffff43f23ffffbbffd7ffffcd33ffff, 0xfffffffdf6ff43fffffffffffffb4e54dfc8fff, 0xfffabf8bfffffcc23ffffbbffd7fd6fffffffd0, 0xfffabf8bfffffff23ffffbbffd7fcefff33ffd0,
  0xfffaa4ffffd5fcdffffefbbf0fffd9fff098b3f, 0xfffa2487ffd5fcc27f0bfbbfffffd9ffffd8fff, 0xffffff87fffffffffffcfbbf6ff6bffcd318b3f, 0xffffe683fffffff27ffffbbffd76bf57ffd8fff,
  0xc3ffe6fffffffcdffffeffff6d7ffffff248fff, 0xfffa6483ffd5fff23ffffbbf0defffffffffb3f, 0xfffa248bffd5fcefff0efbbffdefffffffff13f, 0xfffa3f8bffd5fffffffffbbffdefceffffffb3f,
  0xfffa2583fffffcd23ffffbbffd7fd6fff73ffff, 0xfffffffff6fffcdffffeffdffff756fff248fff, 0xfffa3f8bfffffff23ffffb9ffd7fff54dffffff, 0xfffffffdffd5fceffffefffffe1b7ffe00bfb3f,
  0xffffe4fdc65540cfff0bfffffe1b7fffffff13f, 0xfffffffdf615fffffffffffffe1b4effffffb3f, 0xfffa66ffffd6fff23f0bf8ff8bf4ffffffffb10, 0xffffe6fdc63f40cffffffffffd7b56fe0ffffff,
  0xfffffffdf63f43ffffffffff897b7f57f33ffff, 0xfffabffffffffff23f0af8ff8bffd6ffffffb10, 0xffffffffffd5fcc27ffef8fffe1fd9ffffd8fff, 0xc3ffe4fdffd5fffffffcfffffe1ffffff318b3f,
  0xfffffffffffffff27ffef8fffd7fd6560fd8fff, 0xffffe4ffffd5fceffffef8df89e77ffe073fb3f, 0xfffffffff615ffffffffffdf89e74efcdfffb3f, 0xfffa7ffdeffffcd23ffe7ba6fffb7f93f0bffff,
  0xfffa3f85c65640c27f0a7fffffffff93ffff13f, 0xfffffffde67f43ffffffffe697fb7ffff248fff, 0xfffa7f87fffffff23f0bfba697fffffffffffd0, 0xfffa3f81c63fffffffffffe6957b7ffffffffff,
  0xfffa3fffffd7fff27ffe7bbfffffd993ffd8fff, 0xfffffffffffffffffffe72e66ff69993f248b3f, 0xffffff83fffffff27ffffba6fd76bf57ffd8fff, 0xffffff83ffd6fff23ffffbbf95efff93ffffb3f,
  0xfffffffff67ffffffffe7fff95e77f93ffc8b3f, 0xfffa3f83fffffff23ffffbbf957fd6fff73ffff, 0xfffffffdcfd643fffffffffffe1b7f93ffffb3f, 0xfffa7ffffffffffffffe78e6fe1fff920fffb10,
  0xfffffffdcffffffffffe7fe6fd7b56fe0fffb3f, 0xffffffffffd6fff23ffe7ffffdefff92073fb3f, 0xffffe4fde63ffcdffffefffffffb69fff0bffe8, 0xffffe4fdc6d5fccfff0affffffffe9ffffff128,
  0xfffffffdeffffff23f0ffaeafffb7ffff33fb28, 0xfffffffffffffffffffcfaea0ffb7ffcd0bfb28, 0xc7ffe5fdcffffccffffeffeafd7fff57fffffe8, 0xffffe483fffffff27f0afaff6fffffffffd8fe8,
  0xcbfffffffffffcdffffeffeaffffd9fff098b28, 0xc7ffffffffd5fcdfff0efffffdeffffff73fb28, 0xc7ffffffffd5fcdffffeffff0defe9fff0bffe8, 0xc7ffff8bffd5fffffffcfffffdeffffcdfffb28,
  0xc7fffffffffffcdfff0efffffd7fff57f73fb28, 0xffffff83f617ffffff0bffff97ffe9ffffffb28, 0xffffffffffd7fcdffffe7ffffffb6993f0bfb28, 0xc7ffff83fffffccfff0a7fff957b7ffffffffe8,
  0xfffffffffffffff27ffe7affffffd993ffd8b28, 0xffffff8dd655fce2ffff3fff0f2ffffff0b1fff, 0xffffff83f656fffffffff2ff0f2fffffffc8ff0, 0xffffff8ff695fff2ffffffff0f2fcefffff1fff,
  0xfffffffdd695fff2ff0fffffff2fcefff33113f, 0xffffff8bf6bf4fffc4fff2ffff2ffffcdfc8ff0, 0xfffffffdc656fff27fffffffff24fffffff1110, 0xfffffffdf656fcefc4ff3fffff24ffffffc8fff,
  0xfffffffdf6fffff2c4fffffffff4fffff331fff, 0xfffffffff6fffffffffff2ffff24cefcdfc8fd0, 0xfffffffff6bffcd2ffffffff0fffd657f0b1fff, 0xfffffffff6bf4cc27f0b3fffffffff57fff1ff0,
  0xfffffffff6bffcdfff0f3ffffd7fd6fff248ff0, 0xfffffffff6bffcdfffff32ff0d7fd6ffffc8fff, 0xfffffffff6bf4ff2ff0fffffffffce57f331ff0, 0xfffffffff6bffff2ffffffff0fffce54d0b1fff,
  0xfffffffff6fffcc27fff3ffffff4d657fff1fff, 0xfffffffdffd5fcd2ffff3fffff2fd9fff098fff, 0xfffffffdfffffff2c4ffffff6f26bffcd318ff0, 0xfffabffdcffffcc2440b3fff6f2fffffffd8fd0,
  0xfffffffffffffcd2ffff3ffffff69657f098ff0, 0xfffffffff67ffff2ffff3fff0ff77ffff0b1fff, 0xfffffffff67ffce2ff0f3ffffff77ffff731130, 0xfffffffff67fffffc4ff32dffde77fffffc8ff0,
  0xfffffffff6fffff2c4ffffdfffffcefffff1fff, 0xfffffffff6fffff2fffffffffff74efff331130, 0xfffffffff67ffce2c40fffdffffffffffff1fff, 0xfffafffffffffcd2c4ff3fdfffffd9fff718ff0,
  0xfffffffffffffff2c4fcffdf6deffffcd318ff0, 0xfffffffff67ffff27f0b38fffe1ffffffff1130, 0xfffffffff67fffffffff38ff0e1ffffe00b1130, 0xfffffffff67ffcefc4ff3fff8bfffffe0fc8ff0,
  0xfffffffff695fffffffff8ff8a1fcefff331ff0]


private def flag (i w : Nat) := (packed[i]! >>> (6*w)) &&& 63
private def contribution (i w : Nat) : Nat :=
  let k := flag i w
  if k < 52 ∧ omittedFlags.testBit k = false ∧
     positiveWords[k]! &&& (negativeWords[i]! ||| mins[w]!) = positiveWords[k]!
  then boards[w]! else 0

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
private theorem bits0 : ∀ j : Fin 257, boards[0]!.testBit j.val = true → mins[0]! &&& negativeWords[j.val]! = mins[0]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits1 : ∀ j : Fin 257, boards[1]!.testBit j.val = true → mins[1]! &&& negativeWords[j.val]! = mins[1]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits2 : ∀ j : Fin 257, boards[2]!.testBit j.val = true → mins[2]! &&& negativeWords[j.val]! = mins[2]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits3 : ∀ j : Fin 257, boards[3]!.testBit j.val = true → mins[3]! &&& negativeWords[j.val]! = mins[3]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits4 : ∀ j : Fin 257, boards[4]!.testBit j.val = true → mins[4]! &&& negativeWords[j.val]! = mins[4]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits5 : ∀ j : Fin 257, boards[5]!.testBit j.val = true → mins[5]! &&& negativeWords[j.val]! = mins[5]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits6 : ∀ j : Fin 257, boards[6]!.testBit j.val = true → mins[6]! &&& negativeWords[j.val]! = mins[6]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits7 : ∀ j : Fin 257, boards[7]!.testBit j.val = true → mins[7]! &&& negativeWords[j.val]! = mins[7]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits8 : ∀ j : Fin 257, boards[8]!.testBit j.val = true → mins[8]! &&& negativeWords[j.val]! = mins[8]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits9 : ∀ j : Fin 257, boards[9]!.testBit j.val = true → mins[9]! &&& negativeWords[j.val]! = mins[9]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits10 : ∀ j : Fin 257, boards[10]!.testBit j.val = true → mins[10]! &&& negativeWords[j.val]! = mins[10]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits11 : ∀ j : Fin 257, boards[11]!.testBit j.val = true → mins[11]! &&& negativeWords[j.val]! = mins[11]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits12 : ∀ j : Fin 257, boards[12]!.testBit j.val = true → mins[12]! &&& negativeWords[j.val]! = mins[12]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits13 : ∀ j : Fin 257, boards[13]!.testBit j.val = true → mins[13]! &&& negativeWords[j.val]! = mins[13]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits14 : ∀ j : Fin 257, boards[14]!.testBit j.val = true → mins[14]! &&& negativeWords[j.val]! = mins[14]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits15 : ∀ j : Fin 257, boards[15]!.testBit j.val = true → mins[15]! &&& negativeWords[j.val]! = mins[15]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits16 : ∀ j : Fin 257, boards[16]!.testBit j.val = true → mins[16]! &&& negativeWords[j.val]! = mins[16]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits17 : ∀ j : Fin 257, boards[17]!.testBit j.val = true → mins[17]! &&& negativeWords[j.val]! = mins[17]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits18 : ∀ j : Fin 257, boards[18]!.testBit j.val = true → mins[18]! &&& negativeWords[j.val]! = mins[18]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits19 : ∀ j : Fin 257, boards[19]!.testBit j.val = true → mins[19]! &&& negativeWords[j.val]! = mins[19]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits20 : ∀ j : Fin 257, boards[20]!.testBit j.val = true → mins[20]! &&& negativeWords[j.val]! = mins[20]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits21 : ∀ j : Fin 257, boards[21]!.testBit j.val = true → mins[21]! &&& negativeWords[j.val]! = mins[21]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits22 : ∀ j : Fin 257, boards[22]!.testBit j.val = true → mins[22]! &&& negativeWords[j.val]! = mins[22]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits23 : ∀ j : Fin 257, boards[23]!.testBit j.val = true → mins[23]! &&& negativeWords[j.val]! = mins[23]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits24 : ∀ j : Fin 257, boards[24]!.testBit j.val = true → mins[24]! &&& negativeWords[j.val]! = mins[24]! := by decide +kernel
set_option maxRecDepth 12000 in
private theorem bits25 : ∀ j : Fin 257, boards[25]!.testBit j.val = true → mins[25]! &&& negativeWords[j.val]! = mins[25]! := by decide +kernel
private theorem boardOK (w : Fin 26) (j : Fin 257) : boards[w.val]!.testBit j.val = true → mins[w.val]! &&& negativeWords[j.val]! = mins[w.val]! := by
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

private theorem positiveRows : ∀ p : Fin 52, positiveWords[p.val]! = pos p.val := by decide +kernel
private theorem negativeRows : ∀ i : Fin 257, indices[i.val]! < 468 ∧ negativeWords[i.val]! = neg indices[i.val]! := by decide +kernel
private def idx (i : Fin 257) : Fin 468 := ⟨indices[i.val]!, (negativeRows i).1⟩

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
  by_cases ok : k < 52 ∧ omittedFlags.testBit k = false ∧ positiveWords[k]! &&& (negativeWords[i.val]! ||| mins[w]!) = positiveWords[k]!
  · simp only [contribution,← show k = flag i.val w from rfl,ite_eq_left ok] at on
    obtain ⟨bound,off,cov⟩ := ok
    let p : Fin 52 := ⟨k,bound⟩
    have sub := boardOK ⟨w,List.mem_range.mp hw⟩ j on
    refine ⟨p,off,?_⟩
    change pos p.val &&& (neg indices[i.val]! ||| neg indices[j.val]!) = pos p.val
    rw [← positiveRows p,← (negativeRows i).2,← (negativeRows j).2]
    apply Nat.eq_of_testBit_eq
    intro b
    have c := congrArg (fun t : Nat => t.testBit b) cov
    have d := congrArg (fun t : Nat => t.testBit b) sub
    simp only [Nat.testBit_and,Nat.testBit_or] at c d ⊢
    change (positiveWords[k]!.testBit b && (negativeWords[i.val]!.testBit b || negativeWords[j.val]!.testBit b)) = positiveWords[k]!.testBit b
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
end PEqualNP.Research.Plane888NineFlags

open PEqualNP.Research.Plane888NineFlags PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane888NineFlags : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
