import PEqualNP.Research.OrderThreePlanePrefixData
import PEqualNP.Research.PlaneFirstAndBudget

namespace PEqualNP.Research.Plane975Mask
open OrderThreePlanePrefixData PlaneFirstAndSeparation PlaneFirstAndBudget

def extend (x : Nat) : Nat :=
  let b (i : Nat) := (x >>> i) &&& 1
  x ||| ((b 0 &&& b 13) <<< 26) ||| ((b 0 ||| b 14) <<< 27) |||
    ((b 1 &&& b 13) <<< 28) ||| ((b 1 &&& b 18) <<< 29) ||| ((b 2 &&& b 15) <<< 30)
def pos (i : Nat) := extend (positive[i]!)
def neg (i : Nat) := extend (negative[i]!)
def input (j : Nat) : Column := fun r =>
  (if r < 52 then pos r else neg (r-52)).testBit j
def base : List Column := List.ofFn (fun j : Fin 31 => input j.val) ++ [fun _ => false, fun _ => true]
def omittedFlags : Nat := 0x10100001103f3

private def indices : Array Nat := #[
  0x0, 0x1, 0x2, 0x3, 0x4, 0x5,
  0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
  0xd, 0xf, 0x10, 0x11, 0x12, 0x13,
  0x14, 0x15, 0x18, 0x19, 0x1a, 0x1c,
  0x1e, 0x21, 0x22, 0x23, 0x26, 0x28,
  0x29, 0x2a, 0x2b, 0x2c, 0x30, 0x31,
  0x32, 0x33, 0x38, 0x3b, 0x3e, 0x3f,
  0x41, 0x45, 0x46, 0x49, 0x4b, 0x4e,
  0x4f, 0x53, 0x56, 0x57, 0x58, 0x59,
  0x5a, 0x5b, 0x62, 0x65, 0x67, 0x6b,
  0x6d, 0x6e, 0x6f, 0x70, 0x73, 0x76,
  0x78, 0x79, 0x7b, 0x7d, 0x7e, 0x7f,
  0x82, 0x83, 0x84, 0x86, 0x8a, 0x8c,
  0x8d, 0x8e, 0x8f, 0x92, 0x95, 0x96,
  0x97, 0x99, 0x9c, 0x9e, 0x9f, 0xa2,
  0xa4, 0xa6, 0xa7, 0xa8, 0xaa, 0xab,
  0xaf, 0xb2, 0xb4, 0xb9, 0xbb, 0xbc,
  0xbe, 0xc0, 0xc3, 0xc5, 0xc6, 0xc8,
  0xca, 0xcd, 0xd0, 0xd1, 0xd3, 0xd5,
  0xd7, 0xdc, 0xdd, 0xe0, 0xe2, 0xe8,
  0xe9, 0xea, 0xeb, 0xee, 0xf1, 0xf3,
  0xf4, 0xf5, 0xf6, 0xf7, 0xf9, 0xff,
  0x101, 0x102, 0x104, 0x106, 0x107, 0x108,
  0x10a, 0x10d, 0x10e, 0x110, 0x111, 0x112,
  0x114, 0x116, 0x118, 0x119, 0x11a, 0x11b,
  0x11d, 0x11e, 0x11f, 0x120, 0x122, 0x124,
  0x125, 0x126, 0x129, 0x12a, 0x12b, 0x130,
  0x132, 0x133, 0x136, 0x137, 0x13a, 0x13b,
  0x13e, 0x13f, 0x140, 0x141, 0x143, 0x145,
  0x147, 0x148, 0x149, 0x14b, 0x14d, 0x14e,
  0x151, 0x152, 0x153, 0x156, 0x157, 0x158,
  0x159, 0x15c, 0x15d, 0x15e, 0x15f, 0x160,
  0x161, 0x162, 0x163, 0x165, 0x168, 0x16b,
  0x16c, 0x16e, 0x16f, 0x170, 0x171, 0x173,
  0x174, 0x176, 0x179, 0x17b, 0x17c, 0x17d,
  0x180, 0x181, 0x183, 0x185, 0x187, 0x188,
  0x18a, 0x18c, 0x18d, 0x18e, 0x190, 0x192,
  0x195, 0x198, 0x19a, 0x19d, 0x1a2, 0x1a3,
  0x1a4, 0x1a5, 0x1a7, 0x1ab, 0x1ac, 0x1ad,
  0x1ae, 0x1af, 0x1b0, 0x1b2, 0x1b3, 0x1b4,
  0x1b7, 0x1b8, 0x1b9, 0x1ba, 0x1bb, 0x1bc,
  0x1bd, 0x1c2, 0x1c3, 0x1c4, 0x1c7, 0x1cb,
  0x1cd, 0x1cf, 0x1d1, 0x1d2, 0x1d3]

private def positiveWords : Array Nat := #[
  0xc002001, 0x10002002, 0x2008, 0x2200, 0x8004002, 0x8004004,
  0x8004010, 0x8004400, 0x40008004, 0x8008, 0x8020, 0x8800,
  0x10008, 0x10010, 0x10040, 0x11000, 0x8020001, 0x20010,
  0x20020, 0x20080, 0x20040002, 0x40020, 0x40040, 0x40100,
  0x80004, 0x80040, 0x80080, 0x80200, 0x100008, 0x100080,
  0x100100, 0x100400, 0x200010, 0x200100, 0x200200, 0x200800,
  0x400020, 0x400200, 0x400400, 0x401000, 0x8800001, 0x800040,
  0x800400, 0x800800, 0x1000002, 0x1000080, 0x1000800, 0x1001000,
  0xa000001, 0x2000004, 0x2000100, 0x2001000]

private def negativeWords : Array Nat := #[
  0x800f1c0, 0x80169a0, 0x801c381, 0x8027940, 0x2b540, 0x802d340,
  0x32d04, 0x38702, 0x4b490, 0x804d281, 0x52c84, 0x8054a81,
  0x8058681, 0x63c04, 0x8065a08, 0x70e04, 0x72c04, 0x8087920,
  0x8b510, 0x92d20, 0x8098503, 0xa3d00, 0x80a5908, 0xa9502,
  0xb0d02, 0xc3c10, 0x80c5809, 0x80c9411, 0xe3c00, 0x8107860,
  0x810d241, 0x8114a21, 0x123844, 0x8125a40, 0x130a06, 0x143814,
  0x8145a01, 0x8149211, 0x163804, 0x183830, 0x8189013, 0x8190823,
  0x81c1811, 0x82070e0, 0x20b4c0, 0x2124a4, 0x223444, 0x243484,
  0x8245089, 0x8250485, 0x26140c, 0x263404, 0x8285029, 0x8289403,
  0x8290423, 0x8298403, 0x303064, 0x8309043, 0x8310027, 0x8381023,
  0x8389003, 0x8390023, 0x84069c0, 0x40a1d0, 0x412984, 0x8418183,
  0x422944, 0x8424948, 0x430906, 0x442894, 0x8444889, 0x8450885,
  0x8484909, 0x8488113, 0x8490903, 0x8498103, 0x84c0819, 0x502854,
  0x8508053, 0x8510807, 0x520846, 0x8540815, 0x8580813, 0x8588013,
  0x8590803, 0x86040c9, 0x8610087, 0x62004e, 0x864008d, 0x8700047,
  0x8710007, 0x88071a0, 0x80b190, 0x880d380, 0x8121a4, 0x88143a0,
  0x8825308, 0x830306, 0x843094, 0x86120c, 0x883130, 0x8885128,
  0x889112, 0x8a110a, 0x903034, 0x910226, 0x921206, 0x930206,
  0x943014, 0x981032, 0xa030a4, 0x8a050a8, 0xa100a6, 0xa2100e,
  0xa43084, 0xaa100a, 0xb01026, 0xb21006, 0xc02194, 0xc2010e,
  0xc30106, 0xc4009c, 0xc42094, 0xca010a, 0xe2000e, 0x100a550,
  0x900c341, 0x1012524, 0x9014321, 0x9018701, 0x1022544, 0x1032504,
  0x9048611, 0x9050605, 0x106060c, 0x1082530, 0x9084129, 0x9088511,
  0x9090521, 0x9098501, 0x90c0419, 0x1102074, 0x9104261, 0x9108251,
  0x9110225, 0x9140215, 0x9150205, 0x1202464, 0x9204069, 0x9210425,
  0x122044c, 0x1222444, 0x924040d, 0x9250405, 0x9280429, 0x9290421,
  0x92c0409, 0x9300065, 0x9310025, 0x1402154, 0x9404149, 0x1422144,
  0x944001d, 0x9480119, 0x94c0019, 0x9500055, 0x9540015, 0x960004d,
  0x964000d, 0x9700045, 0x1802134, 0x9804328, 0x1812124, 0x182030c,
  0x1830304, 0x184021c, 0x186020c, 0x1882130, 0x1900234, 0x1902034,
  0x1c0011c, 0x1c02114, 0x1c2010c, 0xa0068e0, 0x200a4d0, 0x2012ca0,
  0xa014aa0, 0xa024a48, 0x2028642, 0x2030e02, 0x2038602, 0x2042c90,
  0xa044a88, 0x2048690, 0x204a490, 0x2052c80, 0x2060e08, 0x2082c30,
  0x2090c22, 0x20a0c0a, 0x20b0c02, 0x20c0c18, 0x20c2c10, 0x2102870,
  0xa104a60, 0x2108252, 0x2120a42, 0x2128242, 0x2130a02, 0x2180832,
  0x22024e0, 0xa2040e8, 0x22084c2, 0x22104a2, 0x2218482, 0x222044a,
  0x228042a, 0x22a040a, 0x24028d0, 0xa4048c8, 0x24080d2, 0x242084a,
  0x2442890, 0x24a080a, 0x2500852, 0x2520842, 0x262004a, 0xa8042a8,
  0x2808292, 0x28102a2, 0x2818282, 0x288003a, 0x2900232, 0x2908212,
  0x2910222, 0x2980032, 0x2a000aa, 0x2a100a2, 0x2a8002a, 0x2c0009a,
  0x2c8001a, 0x2e0008a, 0x3002470, 0xb004268, 0x3008650, 0x300a450,
  0x3020648, 0x3060608, 0x3080438, 0x3082430, 0x3102070, 0x3202460,
  0x3220448, 0x3800238, 0x3840218, 0x3880038, 0x3900230]

private def boards : Array Nat := #[
  0x3fd7f37df3340000000077edfc23ef30730cc101a04, 0x3fff7b3f3e1c0700000000000000019bb2ec206ddce123ee0030401900080, 0x7df7e6e3ef206c97f75f0e47c3a0b5050ee04d0001a440, 0xf1cbd08cab8802910851a99d155011401a8a80a901a011480015000004404000, 0x1e7358b9154022e26813e847c8002b29026403154100e7220800005a80a040100, 0x1af0c7da8012e1860068e1c006c3965818011e330c80000002d502a80a00a0002,
  0x1c7c00073c9cf800198002a3a0d8e0046000000002a1600cc300580360000039, 0x2b0785c7c000f87800000000000000645c004f96000e3c003b80000001f07, 0x727c0b80000f8fe9c000f3f8000f1fc000000001fe00ff, 0x160d807780001f0137c05e8000007c07340000e0ba000000000000036c000daa4, 0x1bf4000003f407fef30000001fe81efea00000000000000000eef0001bbdb5d0, 0x3ec035ff9ae80000000000000000000000017b5fd400006dfb76bec4a,
  0x3ef5fd380000001b3dddfb7ee66339, 0xe24000044040c2c83aa14028088208ca444511458002025c108f8c9322f255b, 0x80008080810010c8008010010410140008021a820014840110812e4424a2f, 0x3002501050a0065100000000008a126000004030084a0292a01120489413b5, 0x246000610148660050004a250c2b81010a02c4508c9324c2220481199cc6, 0x10c00006a281c1907841600200c0004c19aa0c8b0081001c000c404711e1e0f8,
  0x408000004000061f80018154130610700604100c010210e0000f84781e01ff00, 0x83014880830207e0000200181c001f80080820f0001c1f0038f007801ffe0000, 0x104000f030003f800000c02606007e00000303f00061fe0003f0007ffe0000000, 0x1802700403fc0000000003807ff80000103fc00007e000003ffff80000000000, 0x38007fc000000007003ff800000001fc0000007ffffffc000000000000000, 0x1e003fff800000000007ffc00000000001ffffffff80000000000000000000000,
  0x1fffc000000000000007fffffffffffffe0000000000000000000000000000000, 0x1ffffffffffffffffff8000000000000000000000000000000000000000000000]

private def mins : Array Nat := #[
  0x8000001, 0x2, 0x4, 0x8, 0x10, 0x20,
  0x40, 0x80, 0x100, 0x200, 0x400, 0x800,
  0x1000, 0x2000, 0x8004000, 0x8000, 0x10000, 0x20000,
  0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000,
  0x1000000, 0x2000000]

private def packed : Array Nat := #[
  0xcada6787f6564fffffffffff0fffff2bfffffff, 0xcadae487f6954bffffffffff0fffcefcdffffff, 0xcadfe587f6974ffffffcf2ffffffff28dffffff, 0xfeefe785e656fce2fffffffffff4fffd10bffff, 0xfeffff85e67ffceffffff2ff0ff4fffd10bffff, 0xcafa7f85e67ffcefff0ff2fffff4fffd1ffffff,
  0xfeefe687f617fffffffcffff0fffff48dffffff, 0xcacabf87f6fffffffffff2fffff4cefcdffffff, 0xcffaa683f6bf47fffffff2ff0d7fff2bfffffff, 0xcedfe589d6bf4cffff0ffffffd7fff2bfffffff, 0xc7ffe68fffff4fffffffffff0d7fff54d0bffff, 0xfedfe589dfff4ff2ff0ffffffd7fff54d33ffff,
  0xfedabf8bffff4ffffffcf2fffd7fff28dffffff, 0xffffff8df63ffcffffffffff0d7fd6fd10bffff, 0xceeaff89c6fffccfff0bfffffd74d6fd1ffffff, 0xc6efff89ffffffffff0ffffffd74fffcd33ffff, 0xc7ffff8dfffffffffffcffff0d74fffcdffffff, 0xcaeafffdefd548f2bfffffffffffd9fff098fff,
  0xcafaa681efd744dffffff2ffffffd92bffd8fff, 0xcaefe485efff4bf2bffcffff0ff6bfffffd8fff, 0xcacfe687fffffffffffcf2ff6fffff2bffd8fff, 0xcbffe6ffffd7fcf2ffffffffffffd94bf098fff, 0xcbfae7ffffd7fcc2ff0bffffffffd94bffd8fff, 0xcbfabf87fffffcfffffff2ff6fffd9291fd8fff,
  0xcacfe6fffffffff2fffcfffffff4ff4bffd8fff, 0xcffffffdffff47f2fffffffffd76bf57f098fff, 0xceefe78dcffffff2ff0bffff6d76bfffffd8fff, 0xceffff81fffffffffffff2fffd76bfffffd8fff, 0xcffffffdfffffff2fffffffffd74ff491098fff, 0xceea648ff6554bffffffffdf0ff77ffffffffff,
  0xcefa658bf656fffffffff2dffdefff2bfffffff, 0xfeeae48bf6ff4bfffffcffdffff74efffffffff, 0xfffa67ffffd6fff2ffffffdf0defff4bfffffff, 0xcffa65ffffd6fce2ff0fffdffdefff4bfffffff, 0xc6cae5fffffffffffffcffdffff4ce4bfffffff, 0xfffae7fff63f47ffffffffdf0fffd657f0bffff,
  0xfeeae5fff6fffcf2ff0fffdfffffd657f73ffff, 0xceffe5fff6ff47ffff0ff2dffff7562bfffffff, 0xfffae7fff63fffffffffffdf0fffd64910bffff, 0xcffae483ffd5fcd2bffffffffdefd9ffffd8fff, 0xcfffe783fffffffffffff2df6defff2bffd8fff, 0xffffe48fffffffffffffffdf6defcefcd318fff,
  0xcfffe783fffffff2ffffffdf6d7fff57f718fff, 0xceda7ffddfd548e2bffffffffe1ffffe00bffff, 0xcffffffdd6564ceffffffffffe1fff2a00bffff, 0xc6daa4fdd6154bfffffcf8ff0e1ffffcdffffff, 0xfefffffdf616fcefffffffff0e14fffd10bffff, 0xfffabffff63f4cffffffffff0fffd65600bffff,
  0xfedfe7fff6bf4ccfff0bf8ff8bffd6560ffffff, 0xc6dfe6fff63f4ffffffcf8ff8bffff54dffffff, 0xfefabffff63ffccfff0bffff8bf4d6fd1ffffff, 0xfffabffff63ffcfffffff8fffff4d6fd10bffff, 0xcefffffdcfd548c2bffffffffe1699ffffd8fff, 0xcecabffdfffffcfffffff2fffe16bf2a0fd8fff,
  0xfecffffdfffffff2bffff8ff6ff6bffcd318fff, 0xfffffffffffffffffffcf2ff6e16bf28d318fff, 0xfefa64fff63ffce2bffff8df0ff77ffffffffff, 0xfffa67fff67ffffffffff2df8bf77f2bfffffff, 0xc6cfe4fff63ffffffffcffdf8bf77ffffffffff, 0xcfffffffffd5fcf2bffffffffdefd9fe0718fff,
  0xcffffffffffffffffffff2dffde6992a0718fff, 0xfffffffffffffffffffcf8df6de6bffcd318fff, 0xcada7ffddfd64ce2ffffffe6ffffff93f0bffff, 0xcada7ffdd67ffcdffffe72e60ffffffff0bffff, 0xfffaff85d6174ff2ffffffe60fffce93f0bffff, 0xffffff85d6bf4ffffffff2e697ffce28d33ffff,
  0xfeea7ffdeffffce2fffe7fe6fff4fffff0bffff, 0xcaea7f85c67ffccfff0bffe697f4fffffffffff, 0xfffafffde63fffffffffffe6fff4ce4bf33ffff, 0xc7fafffddffffcdffffe7fe6fd7ffffff0bffff, 0xfedaff8dc6bffccfff0bffe6957fd6fffffffff, 0xc7faff8ddfffffffffffffe6957ffffcd33ffff,
  0xcaeafffdcfd7fcc2fffe7fffffffd9ffffd8fff, 0xcacffffdefff44dffffe72ffffffd9ffffd8fff, 0xcacffffdeffffff2fffcffe6fff6bf93f318fff, 0xcacffffffffffffffffcf2e6fff6bf28d318fff, 0xfeeafffdcfff47f2fffe7fe6fd76bf57ffd8fff, 0xc6ea7f83f61644d2fffe7fdffdeffffff0bffff,
  0xfeca7f83f67ffffffffff2df95e77ffffffffff, 0xfffaff8ff63ffffffffcffdf95e74efcdffffff, 0xc7fa7f8ffffffceffffe7fdf95effffd173ffff, 0xfeeafffff63ffcdffffe7fdffff756fff73ffff, 0xfffffffffffffcd2fffe7fdffff69993f718fff, 0xfffffffffffffffffffe72df6defd92bf718fff,
  0xfffffffffffffff2ffffffdf6defce90d318fff, 0xfeda7ffdcfd64ccffffff8e6fe1fff920ffffff, 0xc7fffffddffffffffffcf8e6fe1fff90d33ffff, 0xc6ca7ffdcffffffffffff8e6fe14ff4bfffffff, 0xc6dffffdcfff4ccffffe78e6fd7fd6fe0ffffff, 0xfeca7ffffffffceffffe78df8bf77ffe073ffff,
  0xfffffffffffffffffffcf8df89e74e90d33ffff, 0xfedfe485d695fcf2bfffffeaffffe9fff0bffff, 0xffffe7fdd697fcdfffffffea0fffe92bf0bffff, 0xcbffe5fdd6974cffff0fffeaffffe92bfffffff, 0xfedfe485dffffffffffcfaea0ffffffff0bffff, 0xcadfff85dfff4bf2bf0ffaeafffffffff33ffff,
  0xfeffe585c6d7fccfffffffeafff4e94bfffffff, 0xfecfe5fdefffffffff0cffeafff4fffff33ffff, 0xc7ffe781dffffffffffffaea0d7ffffff0bffff, 0xfeffe589cffffffffffffaeafd74ff4bfffffff, 0xcafffffdeffffcd2bffffafffff6bffff098fff, 0xcaffff85cfff4bf2bf0bfafffff6bfffffd8fff,
  0xcbffe781efff47fffffff2ea6ff6bf2bffd8fff, 0xcbffe787fffffffffffffaea6ff4d9491fd8fff, 0xfeffe483f615ffffffffffdf0defe9fffffffff, 0xc6cfe48bffff4bfffffcfadffff77ffffffffff, 0xffffe58bfffffcfffffffadffde4e949173ffff, 0xc6cfe5fffffffffffffcfadffde4ff4bfffffff,
  0xffffe7fff63f47fffffffadf0ff75657fffffff, 0xcfffff83ffd5fff2bffffafffdefd9ffffd8fff, 0xc7fffffddfd5fcffffffffeafe1fe9fff0bffff, 0xcffffffdc69548cfff0bffeafe1fe9fffffffff, 0xc7ffe4fddfd5fffffffcffeafe1ffffff33ffff, 0xffffe7fdc63fffffffffffea8a14ff4bfffffff,
  0xc7fffffddffffcffffffffea0d7fff5600bffff, 0xcffffffdcffffffffffff8eafe14ff491fd8fff, 0xffffe4fff63f48ffffffffdf8bf769fe0ffffff, 0xffffe7fff63ffffffffff8df8bf4e949173ffff, 0xfedffffdd617fcdffffe7fe60fffe9fff0bffff, 0xfecfff85c63ffccfffffffe697f4e9fffffffff,
  0xfecffffde63ffffffffffae697f4cefff33ffff, 0xc6dfff81cfffffffff0bfae6957ffffffffffff, 0xc7fffffddffffcdffffe7ae6fd7ffffff0bffff, 0xcacffffffffffccffffe7affffffd9fd1fd8fff, 0xfecffffdc63ffffffffe7fe6fe14e9fffffffff, 0xcbffe6fff65647ffffffffff0ffb7f2bffffb3f,
  0xcbfa6585e656fcefff0effffffffff2bffffb3f, 0xfffabf87f63f4bfffffffbbf0fffcefcd0bfb3f, 0xffffff85e6d54bf2bf0ffffffffb7ffff33fb3f, 0xfffabffde6d7ffffff0ffffffffb4e2bf33fb3f, 0xffffe687fffffceffffeffff0fffff4910bfb3f, 0xfffffffff617fffffffcfbbf0fffce48d0bfb3f,
  0xfffaa581f6ff44dfff0ffffffffb562bffffb3f, 0xffffff89ffffffffff0ffbbffd7b7ffcd33fb3f, 0xc7fabf8bfffffccfff0afbbffd7fff491fffb3f, 0xcbfabffffffffcd2bffeffffffffd9fff098b3f, 0xcbffe487ffd5fcc2bf0affff6fffd9ffffd8fff, 0xcbffe6ffffd7fcdffffeffffffffd92bffd8fff,
  0xcbffe487fffffff2bffcfbbf6ffffffcd318fff, 0xcbffe6fffffffffffffcffff6fffff28d318b3f, 0xffffe683ffffffffff0afbbf6d7fff57ffd8b3f, 0xc7fa6483fffffffffffefb9f0deffffff0bfb3f, 0xfffa648bffd5fce2bf0ffbbffffffffff73fb3f, 0xffffe5ffffd6fcdfff0effdffdefff2bf73fb3f,
  0xffffff8bffd5ffffff0ffbbffdefcefcd33fb3f, 0xffffe5fffffffcdfff0effdfffffd657f73fb3f, 0xffffffffffffffffff0cffdffd774e54d33fb3f, 0xc7fffffdffff48effffefffffe1ffffe00bfb3f, 0xffffe4fdc65548cfff0bffff8bfb7fffffffb3f, 0xfffffffdf615fffffffffffffe1b4efcd33fb3f,
  0xc7ffe6ffffd6ffffff0bffff8a1fff4bffffb3f, 0xfffffffdfffffceffffefffffe1fff4910bfb3f, 0xffffe6fff63ffccfff0affff8bfb5657ffffb3f, 0xfffffffffffffffffffcf8ff897b4e54d33fb3f, 0xffffffffffd5fccfff0affff6e1699fe0fd8b3f, 0xfffffffffffffffffffff8fffe168efcd318b3f,
  0xfffffffffffffffffffff8ff6d7696560fd8b3f, 0xffffe4fffffffceffffeffdf89e77ffe073fb3f, 0xfffffffffffffffffffff8df89e74efcd33fb3f, 0xfffa7ffdefd647ffffffffe60ffb7f93f0bfb3f, 0xfffa7f85c656ffffff0bfbbf97ffffffffffb3f, 0xfffffffdeffffffffffffba60ff4ff4910bfb3f,
  0xffffff81c63fffffff0bfbbf957b7fffffffb3f, 0xcbffffffffd7fccffffe7ba6ffffd993ffd8b3f, 0xfffffffffffffffffffffba66d76bf57ffd8b3f, 0xffffff83ffd6fffffffffb9f95efff93ffffb3f, 0xfffffffffffffffffffe7b9f95775657f73fb3f, 0xfffffffdcfd6ffffff0bffe68a1b7f93ffffb3f,
  0xfffffffff63fffffff0bffe6897b56560fffb3f, 0xfffffffffffffceffffe7fdffdefff92073fb3f, 0xffffe4fde63ffcdfffffffeafffb69fff0bfb3f, 0xcbffe4fdc6d548cfff0bfffffffb69ffffffb3f, 0xfffffffdeffffffffffffaea0ffb4efcd0bfb3f, 0xffffe5fff617fccfff0affffffffe94bffffb3f,
  0xfffffffdefffffffff0fffeafff4ce4bf33fb3f, 0xc7ffe5fdcfff47ffff0afaeafd7fff57ffffb3f, 0xffffe5fffffffccfff0afaeafd7fff491fffb3f, 0xcbfffffffffffcd2bffeffeaffffd9fff098b3f, 0xc7ffffffffd5fcd2bf0fffffffffe9fff73fb3f, 0xffffffffffd5fcdffffeffdf0de769fff0bfb3f,
  0xffffff83f61747ffff0bffff97ffe9ffffffb3f, 0xffffffffffd7ffffffffffe60ffb6993f0bfb3f, 0xffffff87f63fffffff0bfaff97ffe9fd1fffb3f, 0xfedfe48dd655fce2bfffffff0f2ffffffff1fff, 0xfedfe683f656fffffffff2ff0f2ffffffff1fff, 0xfffabf8ff695ffffffffffff0f2fcefffff1fff,
  0xfffaff89d6954bffff0fffffff2fcefffff1fff, 0xfeefe589c656fcc2ffffffffff24fffffff1fff, 0xfecfff89f67ffceffffff2ffff24fffffff1fff, 0xfffffffdf6fffff2fffffffffff4ce4bf331fff, 0xfffffffdf6fffffffffff2ffff24cefcd331fff, 0xffffe6fff6bffcd2ffffffff0fffd657f0b1fff,
  0xfffae5fff6bf4cc2ff0b3fffffffd6fffff1fff, 0xfedabffff6bffcdfff0f32ffffffd6fffff1fff, 0xffffe6fff6bffcdfffff32ff0fffd62bfff1fff, 0xfffffffff6bffff2ffffffff0fffce54d0b1fff, 0xfeeffffff6fffccfffff3ffffff4d6fd1ff1fff, 0xfeeffffdffd5fcd2bfffffffff2fd9fff098fff,
  0xffffff8dffff4bffffffffff6f26bffcd318fff, 0xffffe68ffffffcc2ffff3fff6fffd9491fd8fff, 0xfffffffdfffffff2fffcffff6f24ff48d318fff, 0xfeefe6ffffff47f2ff0b3ffffff6bf57ffd8fff, 0xffffe6ffffff47f2ffff3ffffff6bf57f098fff, 0xfeefe4fff67f47ffffff3fff0ff77ffffff1fff,
  0xfeea64fff67f48e2bf0f3ffffff77ffffff1fff, 0xfeca65fff67f47ffffff3ffffff77f2bfff1fff, 0xfecfe5fff67ffce2ffff3ffffff4ff4bf731fff, 0xfecffffff67fffffffff32dffff4ff291731fff, 0xfffafffff6fffffffffcffdffff4ce4bfff1fff, 0xfffae4fffffffcdfffff3fdf6fffd9fff718fff,
  0xfedfe4fff67ffce2bfff38ff0ffffffe00b1fff, 0xfeda64fff67f48c2bf0b3fff8bfffffffff1fff, 0xffffe6fff67f4cefffff3fff8bffff2a0ff1fff, 0xfffabffff695fff2bffff8ff8a1fcefffff1fff, 0xfffffffff6bffffffffff2ff8a1fce28d331fff, 0xfecfe6fff67fffffff0b3fff8bf4fffffff1fff,
  0xfecabfffffff48c2bfff38ffffffd9fe0fd8fff, 0xfecffffffffffccfffff38ff6e14d9491fd8fff, 0xffffff81d656fff2ffffffe60f2fff93f0b1fff, 0xfffa7f8dc6564ff2ff0bffff972ffffffff1fff, 0xfffa7f81d67ffffffffff2e6972ffffffff1fff, 0xffffff8dc67fffffff0bffff9724fffffff1fff,
  0xfffffffff6bfffffffffffe60d7fd657f0b1fff, 0xfffffffffffffcc2fffe7fe6ff24d9491fd8fff, 0xfecffffff67f47f2ffffffff97f77f93fff1fff, 0xfecffffff67ffffffffe7fff97f4fffd1731fff, 0xfecffffdc67fffffff0bf8e68bf4fffffff1fff, 0xfedfe489c695fcc2bfffffffff2fe9fffff1fff,
  0xfecfe5fdd6bffcdfffff32eaffffe92bfff1fff, 0xffffff89d695fff2bffffaeaff2fcefff331fff, 0xfffffffff6bffffffffcf2eaff2fce28d331fff, 0xfecfe481cfffffffffff3aea6fffffffffd8fff, 0xfecffffff6fffcd2bffffafffff769fff731fff, 0xfffffffff6fffcdfffff3fdffff7692bf731fff,
  0xfffffffff6ff4bfffffffafffde74efcdff1fff, 0xfecffffffffffcd2bfff3adf6ffffffff718fff, 0xffffe4fff6bffccfff0b3fff8bffe9fffff1fff, 0xfffffffff6bfffffffffffea8a1fcefcd331fff, 0xfffffffdcfffffffffff38eafe1699fe0fd8fff, 0xffffff83f6bfffffff0bfaff972fe9fffff1fff,
  0xfecffffdcfff47fffffffae6ff26bf93ffd8fff, 0xfffffffff6bffccfff0a78ff8bffe9920ff1fff, 0xffffff81f67f47f2bfffffff0ffb7ffff0b1fff, 0xfffa7f89c67f4bf2bf0bffffff2b7ffffff1fff, 0xfffffffdf65647ffff0fffffff2b7f2bfff1fff, 0xfffffffff67f47ffffffffff0f2b7f2bfff1b3f,
  0xffffff89c656fffffffffbbfff24ff491ff1b3f, 0xfffffffff6fffccffffffbbffd74d6fd1ff1fff, 0xfffabf83ffd5ffffff0bffff6f2fd9ffffd8b3f, 0xfffffffffffffcd2bffffbbf0f2fd9fff098b3f, 0xfffffffff67f47fffffffb9f0ff77ffff0b1b3f, 0xfffffffff67f4bfffffeffff0ffb7ffe00b1fff,
  0xfffffffff67fffffff0bffff8a14ff4bfff1b3f, 0xfffffffdc6d5fccfffffffffff2b69fffff1fff, 0xfffffffdc6ff44cfffffffeafffb5657fff1fff, 0xffffff83ffd5fffffffffaea6f2fd9ffffd8b3f, 0xfffffffff6fffcd2bffffafffff769fff731b3f]


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
end PEqualNP.Research.Plane975Mask

open PEqualNP.Research.Plane975Mask PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget in
theorem PEqualNP.Research.Plane975Mask : ∀ (ors : List (Nat × Nat)) (left right : Nat)
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
