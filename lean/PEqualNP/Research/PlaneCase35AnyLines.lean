import PEqualNP.Research.PlaneCase35EightFlags

namespace PEqualNP.Research.PlaneCase35AnyLines
open PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35EightFlags
-- Each triple selects part of a word and shifts it to its new coordinates.
private def permute : List (Nat × Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (mask,l,r)::tail, x => (((x &&& mask) <<< l) >>> r) ||| permute tail x
private def segments : Array (List (Nat × Nat × Nat)) := #[[(0x1ffefff,1,0), (0x2001000,0,12)], [(0x2001,0,0), (0x4002,2,0), (0x8004,4,0), (0x10008,6,0), (0x20010,8,0), (0x40020,0,3), (0x80040,0,1), (0x100080,1,0), (0x200100,3,0), (0x400200,0,8), (0x800400,0,6), (0x1000800,0,4), (0x2001000,0,2)], [(0x68220b,0,0), (0x8024,5,0), (0x10,7,0), (0x140140,0,4), (0x10080,0,1), (0x800400,2,0), (0x800,0,3), (0x1000,0,7), (0x4000,10,0), (0x20000,6,0), (0x1000000,0,6), (0x2000000,0,8)]]
private def act (g : Fin 3) (x : Nat) := extend (permute segments[g.val]! x)
private theorem permJoin (s : List (Nat × Nat × Nat)) (x y : Nat) :
    permute s (x ||| y) = permute s x ||| permute s y := by
  induction s with
  | nil => simp [permute]
  | cons h t ih =>
    rcases h with ⟨m,l,r⟩
    simp only [permute,Nat.and_or_distrib_right,Nat.shiftLeft_or_distrib,Nat.shiftRight_or_distrib,ih]
    ac_rfl
private def Hom (f : Nat → Nat) := ∀ x y, f (x ||| y) = f x ||| f y
private theorem glue {f g : Nat → Nat} (hf : Hom f) (hg : Hom g) : Hom (fun v => f v ||| g v) := by
  intro x y
  change f _ ||| g _ = (f x ||| g x) ||| (f y ||| g y)
  rw [hf,hg]
  ac_rfl
private theorem pushed {f : Nat → Nat} (h : Hom f) (k : Nat) : Hom (fun v => f v <<< k) := by
  intro x y
  exact (congrArg (fun z => z <<< k) (h x y)).trans Nat.shiftLeft_or_distrib
private theorem bitHom (k : Nat) : Hom (fun x => (x >>> k) &&& 1) := by
  intro x y
  simp only [Nat.shiftRight_or_distrib,Nat.and_or_distrib_right]
private theorem extendJoin : Hom extend :=
  glue (glue (fun _ _ => rfl) (pushed (glue (bitHom 0) (bitHom 1)) 26))
    (pushed (glue (bitHom 3) (bitHom 9)) 27)
private theorem join (g : Fin 3) (x y : Nat) : act g (x ||| y) = act g x ||| act g y := by
  exact (congrArg extend (permJoin _ x y)).trans (extendJoin _ _)

private def pm : Array Nat := #[0x3081c33cb1beeb6ca2baa99e69648e28607de75c6da6585d65544134913ce34c2ca2481c6144, 0xaaba687dd79c4d14901c6105b6cbaf8238625175562ca209cb1cf09a49e56986d934f38c043080, 0x4914d0557594cb3c709279668628233cd38c6d961a1851c4a6aae82882c979f71dbeeb6c0c2040]
private def nm : Array Nat := #[0xe5f1f89bcdce6f2b91c7e370d84c1602fd75b9dc6db6bb2d8ec15aac55ead52a752e87409c4c25b2a93c7a39198842e13067fbf1f2f579badcce471379aed4693419cca61afd7abb5bad158aa54a9d4c9348231007d3e1e8f075399c8e06f34990c4572a1449c4d259249046229087a3b1c0c45a2b1409848210f87436190b85428130903c160903818080300803a7d2e8f439fcee6f3395c9e471b8bc3e170781bfdf6f777badc6df6db5da6cf65b1d86bf5dadd66af55a9d469f4da5d268f45a1d067f3d9dce66b3398cbe5b2993c96431d8cc5e2b1388c3e170781bfdf6f97bbd5e6f177bb5d2e570b7dbad96ab4da2cf66b258ac35faf576b95bacd56a953a8d429f4da652a9348a3d1a8b44a15067f3e9ecf2773a9ccde6d359a4ce653197cba592b94ca24d259248e45219047e3b1b8d4622f168ac52271288c3e1d0d8642a110782c12070280c01fcfd7dbe9f0f77b3d1e4f1783bddced763a9d2e873b95c6e17037dbadc6db69b2d86b355a6d167b3598cb64b218ec662b1184c1602f978ba5cae16cb559ac962b057ab95aab5429548a351285409f4f275389b4d26530974b255289248a3d1c8d45a29128843a190a8441a09027f3f1ecf2773b1d0e26e369b0d66a3419ccc6531984c05f2f174b85b2d164b0562a94ca4502793094472210c82401f8f8783a1c8dc6c351a0cc6430178b8582a1489c4a23110803c1c0d0602c11080381a0c050200a02, 0x703318ec863543a74fa7535c2df6f37596ca64eb59ec4d7ebb58ce66b1587465d2c582afa4d4e8f456cbc5b8d55cb0966b0773a5d0c0597429944a0b6362db6934571a95aab952a8d368d7abc562ad4dd1aa523a5cfaad4aa34ba550e85407935dadb8d9ecb60f077b69a8d3686a96eb6db6a1d6ea5a6d74fa476b9dc8e35faf95aa7dbed357a576399cae25daa8722fbd0b4586a529a4d03a1c0def62ecedf2f2914823c602b9444f911588998d864318d08636190a6f175ba1007a3c150a27f2993c9a2f3a8c45b93398971f8d389bc5220a33699548a2371acce62220cd309449a4884411a8c739764b2347d9ecde6aff7ebeddee6974aa39183f1dbf77d317d5a44e1003017275c441e8f21b0d00e43cd9ec7a3bc282c137f007e3ef7b3097bfdfcf93095cad892e93499a2c66213c5c25dcad56813094241107d7eba200e8701004cc64adf6eaf2250e7c3d9e03e1e0c81f993c91c6a5cf87a6ea692b8641dec525017c9e9b2411f4182c0a64b0450702b2d66b0a2d027e11030ee7238808018fc756ab35642a08ea743785c2c1300cfa4b208ff3b97ca9dc92451c8dc67830f81c078bc09b4ca1d02de6ee6b2d9643613087bbcf89c3dccce550b85419ea602a944a0a14f978a853276870f84c1a75345b2c9288d9fc5e2b0d85c0270b449b3d8ec424118341399cae52e370b2d92c08a401fcfa2105e47215baba190676380602997c6db6d96bac210e615, 0xb55cad3c2b4185b3212b9587505090444e2612ae872106652572381bc101fa2cc64f3b92c66279b88b7d7ef95eb75eb7d5cbdefebb79debc54b3d4f225d2913e1ed10ee43cc4f479a9ba1208f984bcf0dc2e971c0d53513498693447a3a4b1007c3cb36451d6500040c1fefe03b04361a613003a1c0cac68caf17bf40c05168b1f40363ac18d45173f1f60415be73396db6572966b3d96c9c5b8dc35361d574751c1b1d8b816050a81e53e4fa0528803fa2d3136451faa8eb754e92692991f4ab202a14cbe6092979b05227b5dac512847c9c0e1b032060d8c0d6040b21888890f1208c84418708570b51a02864cb5badaa0ca64d21691719c04131618e8371a1cfedf3d97c7e3b6bb4ce647219bcd63717b2c3e1b0bb3e762b63ccc16076184c1f2f9580bfdb6d9a6bc56ab3a7d7696b777ac6bfa5abbf5f789c3b5f4347c8badd37556d6e93a7ace7f26edbcddd5f8fc6b9ee5e09d52271373c4cbbd469a9fa8a76854325d08773a9d1cee6729d91c739a209db557625a6a834acce5c7238cacdee471d4aa2e29ca365b2c384e26e8c9516cdd242d37da8d3254a4cf1c8d925b66c91961c2da36964d72269344cc4823ca0c8638d115bcdd681948d279318a32408605c2d0d0c0fe170a0aaba88ac55be00515153d802ada7b168742553de28f5a62f5783d1e41c26cf5faf99ccda5d29763e84c20283b832a551415344c52f40044450c453d3a9ac3a0449e710]
private def lm : Array Nat := #[0xcba987654321, 0xa741b852c9630, 0x45c98361a27b0]
private def imageP (g : Fin 3) (p : Fin 52) : Fin 52 :=
  Fin.ofNat 52 (((pm[g.val]! >>> (6*p.val)) &&& 63))
private def imageN (g : Fin 3) (n : Fin 468) : Fin 468 :=
  Fin.ofNat 468 (((nm[g.val]! >>> (9*n.val)) &&& 511))
private def line (g : Fin 3) (a : Nat) := (lm[g.val]! >>> (4*a)) &&& 15
set_option maxRecDepth 16000 in
private theorem posOK : ∀ (g : Fin 3) (p : Fin 52), pos (imageP g p).val = act g (pos p.val) ∧
    (imageP g p).val / 4 = line g (p.val/4) := by decide +kernel
private def nw (i : Fin 468) := (0xb900230b880038b840218b804228b800238b280428b220448b2040683202460b200468b108250b1042603102070b100270b0c04183082430b080438b060608b048610b040618b028640b024248b020648300a450b008650b0042683002470ee0008aec8001aac400986c08092ec0009aea8002a6a100a2aa040a8ea000aa6980032e910222e908212e900232e88003aa848290a844288a840298e818282a8142a0e8102a2e808292a8042a8e62004a66080c2a6040c8e6000ca65808126520842650805225028506500852a4c0818e4a080ae48081aa4448882442890a440898a424848e42084a240a0d064080d224068c0a4048c824028d0e2a040a6290422e28042a6228442e22044a621848222124a062104a2220a4c062084c222060e0a2040e822024e0619082221828306180832e130a02e128242a124a40e120a42a114a20e110a22e1082522106860a104a602102870a0e0c0820c2c10a0c0c1860b0c02e0a0c0a2092c206090c222082c30a070e00a064a08a060e08a058680a054a802052c80a050e80204a490a048690a044a882042c90e038602e030e02e028642a024a48e01868220168a0a014aa02012ca0200a4d020068e09c801189c4001c9c2010c1c021149c0011c9940214991022419020349900234988412818821309880138986020c984021c98303049824308982030c981432018121249810324980432818021345700045d64000d962004cd604049d60004d5540015550805115020545500055d4c00195488111d484109d480119d44001d94241481422144942014c540c141140a1505408151d40414914021545310025530406113020645300065d2c04095290421d284029d280429926040c5250405d24040d1222444922044c12124245210425d2040691202464d150205d148211d140215d114221d110225d10c241d108251d104261110207450c8411d0c04195098501509412110925205090521108a5105088511d08412910825309070604906060cd058601d050605d048611903870010325049030704902c340102a540902874090243481022544d01c301d018701d0143211012524d00c341100a5508e4008cce2000e4e10086ce0008ecca010a4c88112cc8011a0c420948c4009c4c30106cc2010e4c181820c121844c101860c0a1904c081920c021944b810224b210064b100260b030244b01026caa100a8a85028ca8102a8a6100c8a450880a430848a4108cca2100e0a120a44a100a60a070a08a050a80a030a44989012098303049810328961204894921009430148941214c930206c929202c921206c910226c909212090303448a910288a5108c8a110a088b11048891120887120888512808831308865208886120c884d280084b090884929088452880843094c838302c830306882d300c8293028825308881c380c81838208161a088143a008121a4080f180880d380080b19008071a047200464710007470804347000474650085c644089c64008dc62004e46180834610087460c0c146080c3c6040c945c0811459080345880134580813455080505428144540815453080605228444520846451080745080530502854c4c4809c4c081944b090284a4908c4a090a4498103449490144909034488113c484909445488104528844450885c444889044289404329044430906042694084249480422944441c1814418183041698044149810412984040e1c0440c1c1040a1d004069c043900234389003438502143810234329042032304443210464310027430d041430904303070604305061030306482e140842c9401c2c5009c2c140942a9402c2a140a429840342904234289403c2850290263404826140c425848102524844250485424d081024b4804249481c2450890243484022b44042294420223444421848302124a4020f0c0420d0c1020b4c002070e041c901141c580101c381041c18114194821419082341890130187820418582101838308170a048165a0001638048161a04c154a01c150a05c14d201c149211c145a010143814c130a06812d240c12924201278408125a400123844c114a21c10d241010786080e580800e3c0080e1c0800cb41040c9411c0c580900c3c1040b850200b2d0040b0d0200ab50040a950200a790080a590800a3d004098503009692040949210092d20008b51000879200072c048070e048065a080063c04c05c281c058681c054a810052c84c04d281004b490c0387020032d04002f140802d340002b5400027940c01c38100169a0000f1c0 >>> (28*i.val)) &&& 0xfffffff
set_option maxRecDepth 8192 in
private theorem original : ∀ i : Fin 468, nw i = neg i.val := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n0b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 0 n) = act 0 (nw n) := by decide +kernel
private theorem n0 (n : Fin 468) : nw (imageN 0 n) = act 0 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n0b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n1b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n1b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 1 n) = act 1 (nw n) := by decide +kernel
private theorem n1 (n : Fin 468) : nw (imageN 1 n) = act 1 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n1b442 j
  omega
set_option maxRecDepth 8192 in
private theorem n2b0 : ∀ j : Fin 26, let n := Fin.ofNat 468 (0+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b26 : ∀ j : Fin 26, let n := Fin.ofNat 468 (26+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b52 : ∀ j : Fin 26, let n := Fin.ofNat 468 (52+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b78 : ∀ j : Fin 26, let n := Fin.ofNat 468 (78+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b104 : ∀ j : Fin 26, let n := Fin.ofNat 468 (104+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b130 : ∀ j : Fin 26, let n := Fin.ofNat 468 (130+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b156 : ∀ j : Fin 26, let n := Fin.ofNat 468 (156+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b182 : ∀ j : Fin 26, let n := Fin.ofNat 468 (182+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b208 : ∀ j : Fin 26, let n := Fin.ofNat 468 (208+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b234 : ∀ j : Fin 26, let n := Fin.ofNat 468 (234+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b260 : ∀ j : Fin 26, let n := Fin.ofNat 468 (260+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b286 : ∀ j : Fin 26, let n := Fin.ofNat 468 (286+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b312 : ∀ j : Fin 26, let n := Fin.ofNat 468 (312+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b338 : ∀ j : Fin 26, let n := Fin.ofNat 468 (338+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b364 : ∀ j : Fin 26, let n := Fin.ofNat 468 (364+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b390 : ∀ j : Fin 26, let n := Fin.ofNat 468 (390+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b416 : ∀ j : Fin 26, let n := Fin.ofNat 468 (416+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
set_option maxRecDepth 8192 in
private theorem n2b442 : ∀ j : Fin 26, let n := Fin.ofNat 468 (442+j.val); nw (imageN 2 n) = act 2 (nw n) := by decide +kernel
private theorem n2 (n : Fin 468) : nw (imageN 2 n) = act 2 (nw n) := by
  by_cases h0 : n.val < 26
  · let j : Fin 26 := ⟨n.val-0,by omega⟩
    have e : Fin.ofNat 468 (0+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b0 j
  by_cases h26 : n.val < 52
  · let j : Fin 26 := ⟨n.val-26,by omega⟩
    have e : Fin.ofNat 468 (26+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b26 j
  by_cases h52 : n.val < 78
  · let j : Fin 26 := ⟨n.val-52,by omega⟩
    have e : Fin.ofNat 468 (52+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b52 j
  by_cases h78 : n.val < 104
  · let j : Fin 26 := ⟨n.val-78,by omega⟩
    have e : Fin.ofNat 468 (78+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b78 j
  by_cases h104 : n.val < 130
  · let j : Fin 26 := ⟨n.val-104,by omega⟩
    have e : Fin.ofNat 468 (104+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b104 j
  by_cases h130 : n.val < 156
  · let j : Fin 26 := ⟨n.val-130,by omega⟩
    have e : Fin.ofNat 468 (130+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b130 j
  by_cases h156 : n.val < 182
  · let j : Fin 26 := ⟨n.val-156,by omega⟩
    have e : Fin.ofNat 468 (156+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b156 j
  by_cases h182 : n.val < 208
  · let j : Fin 26 := ⟨n.val-182,by omega⟩
    have e : Fin.ofNat 468 (182+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b182 j
  by_cases h208 : n.val < 234
  · let j : Fin 26 := ⟨n.val-208,by omega⟩
    have e : Fin.ofNat 468 (208+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b208 j
  by_cases h234 : n.val < 260
  · let j : Fin 26 := ⟨n.val-234,by omega⟩
    have e : Fin.ofNat 468 (234+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b234 j
  by_cases h260 : n.val < 286
  · let j : Fin 26 := ⟨n.val-260,by omega⟩
    have e : Fin.ofNat 468 (260+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b260 j
  by_cases h286 : n.val < 312
  · let j : Fin 26 := ⟨n.val-286,by omega⟩
    have e : Fin.ofNat 468 (286+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b286 j
  by_cases h312 : n.val < 338
  · let j : Fin 26 := ⟨n.val-312,by omega⟩
    have e : Fin.ofNat 468 (312+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b312 j
  by_cases h338 : n.val < 364
  · let j : Fin 26 := ⟨n.val-338,by omega⟩
    have e : Fin.ofNat 468 (338+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b338 j
  by_cases h364 : n.val < 390
  · let j : Fin 26 := ⟨n.val-364,by omega⟩
    have e : Fin.ofNat 468 (364+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b364 j
  by_cases h390 : n.val < 416
  · let j : Fin 26 := ⟨n.val-390,by omega⟩
    have e : Fin.ofNat 468 (390+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b390 j
  by_cases h416 : n.val < 442
  · let j : Fin 26 := ⟨n.val-416,by omega⟩
    have e : Fin.ofNat 468 (416+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b416 j
  by_cases h442 : n.val < 468
  · let j : Fin 26 := ⟨n.val-442,by omega⟩
    have e : Fin.ofNat 468 (442+j.val) = n := by apply Fin.ext; simp only [Fin.ofNat, Fin.val_mk]; dsimp [j]; omega
    simpa only [e] using n2b442 j
  omega
private theorem negOK (g : Fin 3) (n : Fin 468) : neg (imageN g n).val = act g (neg n.val) := by
  rw [←original,←original n]
  match g with
  | ⟨0,_⟩ => exact n0 n
  | ⟨1,_⟩ => exact n1 n
  | ⟨2,_⟩ => exact n2 n
  | ⟨m+3,hm⟩ => omega
private theorem inj : ∀ (g : Fin 3) (a b : Fin 13), line g a.val = line g b.val → a=b := by decide +kernel
theorem cover (x y : Nat) : x &&& y = x ↔ x ||| y = y := by
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
    have e := congrArg (fun v : Nat => v.testBit k) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and] at e ⊢ <;>
    cases ex : x.testBit k <;> cases ey : y.testBit k <;> simp_all

private def W (a b : Nat) := ∃ f : Fin 257 → Fin 468, ∀ i j, i < j →
    ∃ p : Fin 52, p.val/4 ≠ a ∧ p.val/4 ≠ b ∧
      pos p.val ||| (neg (f i).val ||| neg (f j).val) = neg (f i).val ||| neg (f j).val
private theorem start : W 0 1 := by
  refine ⟨fun i => ⟨ix i,neg_match i⟩,?_⟩
  intro i j h
  obtain ⟨p,lo,ok⟩ := pairCertificate i j h
  exact ⟨p,by omega,by omega,(cover _ _).mp ok⟩
private theorem hop {a b : Fin 13} (g : Fin 3) (old : W a.val b.val) : W (line g a.val) (line g b.val) := by
  obtain ⟨f,h⟩ := old
  refine ⟨fun i => imageN g (f i),?_⟩
  intro i j lt
  obtain ⟨p,ha,hb,ok⟩ := h i j lt
  let t : Fin 13 := ⟨p.val/4,by omega⟩
  have distinct (k : Fin 13) (off : p.val / 4 ≠ k.val) : (imageP g p).val / 4 ≠ line g k.val := by
    rw [(posOK g p).2]
    exact fun eq => off (congrArg Fin.val (inj g t k eq))
  refine ⟨imageP g p,distinct a ha,distinct b hb,?_⟩
  simpa only [(posOK g p).1,negOK,join] using congrArg (act g) ok

private theorem within : ∀ (g : Fin 3) (a : Fin 13), line g a.val < 13 := by decide +kernel
private def shift (g : Fin 3) (a : Fin 13) : Fin 13 := ⟨_,within g a⟩
private def walk : Nat → Nat → Fin 13 × Fin 13 → Fin 13 × Fin 13
  | 0,_,x => x
  | k+1,z,(a,b) => if z%4 = 0 then (a,b) else
    let g := Fin.ofNat 3 (z%4-1)
    walk k (z/4) (shift g a,shift g b)
private theorem follow (k z : Nat) (x : Fin 13 × Fin 13) (h : W x.1.val x.2.val) :
    W (walk k z x).1.val (walk k z x).2.val := by
  induction k generalizing z x with
  | zero => exact h
  | succ k ih =>
    rcases x with ⟨a,b⟩
    simp only [walk]
    split
    · exact h
    · exact ih _ _ (hop _ h)
private def target (a b : Fin 13) := walk 7 ((0x1d8675076c01d099c36901dc99e07782552b64266036800000d8275036c00d037c2b500dc36e037826d2b5c7e902740001bd43dd09d80690d9c65703641e90d5419502543e902980000bd41b51be4029029c2570a7c0e91ad82b602b42b701b400007e40b50be426501d4375075c2d702dc2db01943bd00b400003e417d02d819600d40d6035c2e607dc37d009425f0e5800002e407d1ae40960ee409703d8e6d03dc1dd01643de05540000f6803d0ae40a50a5c19b019c19e0b640dd006419f01540002d541570ddc066009809b009c09e03b40f5002409f005400036580570f5c0e701680d502f43ed017c03900580e600140000e7c017001c3a5006806b006c06e007e6f9001801e000400015d8176000c976002802b002c02e003cd76000800e0000000 >>> (14*(13*a.val+b.val))) &&& (2^14-1)) (0,1)
set_option maxRecDepth 12000 in
private theorem found : ∀ a b : Fin 13, a ≠ b → target a b = (a,b) ∨ target a b = (b,a) := by decide +kernel
theorem allPairs (a b : Fin 13) (ne : a ≠ b) : W a.val b.val := by
  have h : W (target a b).1.val (target a b).2.val := follow _ _ (0,1) start
  rcases found a b ne with eq | eq <;> rw [eq] at h
  · exact h
  · obtain ⟨f,hf⟩ := h
    refine ⟨f,?_⟩
    intro i j lt
    obtain ⟨p,hb,ha,ok⟩ := hf i j lt
    exact ⟨p,ha,hb,ok⟩
end PEqualNP.Research.PlaneCase35AnyLines

open PEqualNP.Research.PlaneFirstAndSeparation PEqualNP.Research.PlaneFirstAndBudget
  PEqualNP.Research.PlaneCase35FourthOrBudget PEqualNP.Research.PlaneCase35EightFlags in
theorem PEqualNP.Research.PlaneCase35AnyLines : ∀ (A B : Fin 13), A ≠ B → ∀ (extra : List Column) (gs : List Gate) (o : Nat),
    (∀ w ∈ extra, ∀ p : Fin 52, p.val / 4 ≠ A.val → p.val / 4 ≠ B.val → w p.val = true →
      ∃ v ∈ initial, v p.val = true ∧ ∀ n : Fin 468, v (52+n.val) = true → w (52+n.val) = true) →
    (∀ p : Fin 52, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o p.val = true) →
    (∀ n : Fin 468, wire (gs.foldl step (initial ++ extra ++ [fun _ => false, fun _ => true])) o (52+n.val) = false) →
    9 ≤ gs.countP Prod.fst := by
  intro A B ne extra gs o h hp hn
  obtain ⟨f,hf⟩ := PEqualNP.Research.PlaneCase35AnyLines.allPairs A B ne
  apply separated_bound _ gs o _ hp hn
  refine ⟨f,?_⟩
  intro i j lt
  obtain ⟨p,ha,hb,hp'⟩ := hf i j lt
  refine ⟨p,?_⟩
  have good0 := initial_good p (f i) (f j) ((PEqualNP.Research.PlaneCase35AnyLines.cover _ _).mpr hp')
  intro w mem
  rcases List.mem_append.mp mem with prev | const
  · rcases List.mem_append.mp prev with raw | ext
    · exact good0 w raw
    · intro on
      obtain ⟨v,hv,hit,down⟩ := h w ext p ha hb on
      rcases good0 v hv hit with x | y
      · exact Or.inl (down (f i) x)
      · exact Or.inr (down (f j) y)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at const
    rcases const with rfl | rfl <;> simp [good]
