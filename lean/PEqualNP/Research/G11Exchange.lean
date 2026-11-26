import PEqualNP.Research.G11Rare
namespace PEqualNP.Research.G11Exchange
open PEqualNP.Research.G11Rare
set_option maxHeartbeats 0
set_option maxRecDepth 10000
-- One 22-bit word per input mask, first the replacement, then its full cover.
private def words : Array Nat := #[0x4fe07dae91c6ba075ae81c6ba4673d01a6ba065ae8183ee05cfa9143ea054fa8143ea4473d0123ea044fa8104fe03fa700e6ba035ae80cb5602ed580a6ba025ae8083ee01fa70063ea014fa804b5600ed58023ea004fa800,
  0x4fe0fdaeb1cb730e6dcc38b724e73d03ab720e6dc8383ee0dcfa9343ea0d4fa8343ea4c73d0323ea0c4fa8304fe0bed5c2ab570a6d5c28b560aed582ab560a6d58283ee09ed5c223ea094fa824b5608ed58223ea084fa820,
  0x4fe17dae95c6ba175ae85c6ba5673d05a6ba165ae8583ee15cfa9543ea154fa8543ea5473d0523ea144fa8504fe13fa704e6ba135ae84cbc630f3d04a6ba125ae8483ee11fa70463ea114fa844bc610ef18423ea104fa840,
  0x4fe1fcfa9f43ea3d4fa8f43ea7c73d07a3ea3c73d0783ee1dcfa9743ea1d4fa8743ea5c73d0723ea1c4fa8704fe1bf3d46a3ea394fa8e4bc638f3d06a3ea3873d0683ee19ef1c623ea194fa864bc618ef18623ea184fa860,
  0x3ee35fce19c3ea357ce09cb726675d09ab72266dc8983ee25cfa9943ea254fa8943ea6475d0923ea244fa890b5e23fc708e3ea317c708cb5622ed588ab56226d58883ee21fc70863ea214fa884b5620ed58823ea204fa880,
  0x3ee3dcfa9f43ea3d4fa8f4b726e75d0bab722e6dc8b83ee2dcfa9b43ea2d4fa8b43ea6c75d0b23ea2c4fa8b0b5e2bed5caa3ea394fa8e4b562aed58aab562a6d58a83ee29ed5ca23ea294fa8a4b5628ed58a23ea284fa8a0,
  0x3ee35cfa9d43ea354fa8d43ea747790d23ea344fa8d03ee35cfa9d43ea354fa8d43ea747790d23ea344fa8d03ee31fe30c63ea314fa8c4bc630ef18c23ea304fa8c03ee31fe30c63ea314fa8c4bc630ef18c23ea304fa8c0,
  0x3ee3dcfa9f43ea3d4fa8f43ea7c7790f23ea3c4fa8f03ee3dcfa9f43ea3d4fa8f43ea7c7790f23ea3c4fa8f03ee39cfa9f43ea394fa8e4bc638ef18e23ea384fa8e03ee39ed5caa3ea394fa8e4bc638ef18e23ea384fa8e0,
  0x6be47dae91c6ba475ae91c6ba465ae9186ba465ae9183ee45cfa9143ea454fa9143ea444fa9103ea444fa9106be43fa710e6ba435ae90cb5642ed590a6ba425ae9083ee41fa71063ea414fa904b5640ed59023ea404fa900,
  0x3fa4f4fa9f46bac75aeb1cb724e6dc938b724e6dc9383ee4dcfa9343ea4d4fa9343ea4c4fa9303ea4c4fa930b5e4bfa730e6bac35aeb0cb564aed592ab564a6d59283ee49cfa9343ea494fa924b5648ed59223ea484fa920,
  0x6be57dae95c6ba575ae95c6ba565ae9586ba565ae9583ee55cfa9543ea554fa9543ea544fa9503ea544fa9506be53fa714e6ba535ae94c6ba567a714a6ba525ae9483ee51fa71463ea514fa944bc650ef19423ea504fa940,
  0x3fa5f4fa9f43ea7d4fa9f43ea7c7bc1783ea7c7bc1783ee5dcfa9743ea5d4fa9743ea5c4fa9703ea5c4fa9703fa5f4fa9f43ea794fa9e4bc678fb516a3ea787b51683ee59cfa9743ea594fa964bc658ef19623ea584fa960,
  0x3fa677ce19c3ea757ce19cb72666dc998b72666dc9983ee65cfa9943ea654fa9943ea644fa9903ea644fa990b5e63fc718e3ea717c718cb5662ed598ab56626d59883ee61fc71863ea614fa984b5660ed59823ea604fa980,
  0x3fa6f4fa9f43ea7d4fa9f4b726e6dc9b8b726e6dc9b83ee6dcfa9b43ea6d4fa9b43ea6c4fa9b03ea6c4fa9b0b5e6bcfa9f43ea794fa9e4b566aed59aab566a6d59a83ee69cfa9b43ea694fa9a4b5668ed59a23ea684fa9a0,
  0x3ea754fa9d43ea754fa9d43ea744fa9d03ea744fa9d03ee75cfa9d43ea754fa9d43ea744fa9d03ea744fa9d03ee71fe31c63ea714fa9c4bc670ef19c23ea704fa9c03ee71fe31c63ea714fa9c4bc670ef19c23ea704fa9c0,
  0x3ea7d4fa9f43ea7d4fa9f43ea7c4fa9f03ea7c4fa9f03ee7dcfa9f43ea7d4fa9f43ea7c4fa9f03ea7c4fa9f03ee79cfa9f43ea794fa9e4bc678ef19e23ea784fa9e03ee79cfa9f43ea794fa9e4bc678ef19e23ea784fa9e0,
  0x4fe87daeb1c6ba875aea1c6bac673d21a6ba865aea184fe85daeb146ba855aea146bac473d2126ba845aea104fe83fa720e6ba835aea0ccf582b3d20a6ba825aea084fe81fa72066ba815aea04cf580b3d2026ba805aea00,
  0x4fe8fdaeb1c6bac75aeb1cb726e73d23acf58e33d2384fe8ddaeb146bac55aeb143ea6c73d232cf58c33d2304fe8bfa730e6bac35aeb0ccf58ab3d22acf58a33d2284fe89fa73066bac15aeb04cf588b3d222cf58833d220,
  0x4fe97daeb5c6ba975aea5c3ea7c73d25a6ba965aea584fe95daeb546ba955aea546bad473d2526ba945aea504fe93fa724e6ba935aea4ccf592b3d24a6ba925aea484fe91fa72466ba915aea44cf590b3d2426ba905aea40,
  0x4fe9fcfa9f53ea7d5aeb5c3ea7c73d27a3ea7c73d2784fe9ddaeb546bad55aeb543ea7c73d272cf59c33d2704fe9bfa734e3ea795aeb4cbc678f3d26a3ea7873d2684fe99fa73466bad15aeb44cf598b3d262cf59833d260,
  0x3fa6f5aeb5c6ba977ce29cb726e75d29a6ba9675d2985eea5deab947aaa55eaa943ea6c75d2927aaa45eaa90f1ea3fc728e6ba937c728ccf592b5d28a6ba9275d2885eea1fc72867aaa15eaa84d75a0b5d2827aaa05eaa80,
  0x3fa6f4fa9f53ea7d5aeb5cb726e75d2bab726e75d2b85eeadcfa9b53ea6d5eab943ea6c75d2b23ea6c75d2b0b5e6bfa734e3ea795aeb4cb566af5d2aab566a75d2a85eea9fc73863ea695eab84b5668f5d2a23ea6875d2a0,
  0x3ea7d4fa9f53ea7d5aea5c3ea7c4fa9f13ea7c5aea585eeb5daeb5c7aab55eaad43ea7c7792d27aab45eaad03ee79fa724e3ea795aea4cbc678f3d24a3ea785aea485eeb1fe32c67aab15eaac4cf592b792c27aab05eaac0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7c4fa9f13ea7c4fa9f15eebdcfa9f53ea7d5aeb5c3ea7c7792f23ea7c7792f03ee79cfa9f53ea794fa9e5bc678ef19e33ea784fa9e15eeb9fa734e3ea795aeb4cbc678f792e23ea787792e0,
  0x6bec7daeb1c6bac75aeb1cb726e73d23a6bac65aeb186bec5daeb146bac55aeb143ea6c73d2326bac45aeb106bec3fa730e6bac35aeb0c6bac67a730a6bac25aeb086bec1fa73066bac15aeb046bac47a73026bac05aeb00,
  0x3fa6f4fa9f53ea7d5aeb1cb726e6dc9b9b726e7bc3383ea6d4fa9b53ea6d5aeb143ea6c4fa9b13ea6c7bc330b5e6bfa730e3ea795aeb0cb566afb532ab566a7b53283ee69fa73063ea695aeb04b5668fb53223ea687b5320,
  0x6bed7cfa9f56bad75aeb5c3ea7c4fa9f16bad65aeb586bed5daeb546bad55aeb543ea7c73d2726bad45aeb506bed3fa734e6bad35aeb4cbc678fa734a6bad25aeb486bed1fa73466bad15aeb446bad47a73426bad05aeb40,
  0x3ea7d4fa9f53ea7d4fa9f53ea7c4fa9f13ea7c7bc3783ea7d4fa9f53ea7d5aeb543ea7c4fa9f13ea7c7bc3703ee79cfa9f53ea794fa9e5bc678fb536a3ea787b53683ee79fa73463ea795aeb44bc678fb53623ea787b5360,
  0x3fa6f4fa9f53ea7d7ce39cb726e6dc9b9b726e7ce3987aee5cfa9b57aae55eab943ea6c4fa9b17aae45eab90f1ee3fc738e3ea797c738cb566afc738ab566a7c73887aee1fc73867aae15eab84b5668fc73827aae05eab80,
  0x3fa6f4fa9f53ea7d4fa9f5b726e6dc9b9b726e7dc3b83ea6d4fa9b53ea6d4fa9b53ea6c4fa9b13ea6c7dc3b0b5e6bcfa9f53ea794fa9e5b566afd53aab566a7d53a83ee69cfa9b53ea694fa9a5b5668fd53a23ea687d53a0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7c4fa9f13ea7c4fa9f17aef5cfa9f57aaf55eabd43ea7c4fa9f17aaf45eabd03ee79cfa9f53ea794fa9e5bc678ef19e33ea784fa9e17aef1fe33c67aaf15eabc4bc678fe33c27aaf05eabc0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7c4fa9f13ea7c4fa9f13ea7d4fa9f53ea7d4fa9f53ea7c4fa9f13ea7c7f83f03ee79cfa9f53ea794fa9e5bc678ef19e33ea784fa9e13ee79cfa9f53ea794fa9e5bc678ff13e23ea787f13e0,
  0x4fe17f3d43a6ba177ae41cb5742f3d41ab73066dcc183ee15f3d4323ea157ae414b5740f3d412b73046dcc10b5f03fa740eb570a7a740cb5702ed5c0ab57026d5c08b5f01fa7406b57087a7404b5700ed5c02b57006d5c00,
  0x4fe1ff3d43a3ea3d6dcc38b574af3d43ab730e6dcc383ee1df3d4323ea1d6dcc30b5748f3d432b730c6dcc30b5f0bed5c2ab570a6d5c28b570aed5c2ab570a6d5c28b5f09ed5c22b57086d5c20b5708ed5c22b57086d5c20,
  0x4fe17dae95d6ba177ae45c6ba5773d45a6ba1773d4583ee15cfa9553ea157ae4543ea5573d452be3146f8c50e9f13fa744e6ba177a744cb5722f3d44ab572273d448bcf11fa74463ea157a7444bc710ef1c42bc7106f1c40,
  0x4fe1fcfa9f53ea3d4fa8f53ea7d73d47a3ea3d73d4783ee1dcfa9753ea1d4fa8753ea5d73d472be31c6f8c704fe1ff3d46a3ea3d73d468b572af3d46ab572a73d468bcf19ef1c623ea1d6f1c60bc718ef1c62bc7186f1c60,
  0x3ee35cfa9d53ea357ce49c3ea7575d49ab73266dcc983ee35f5d4b23ea357ce494b5760f5d492b73246dcc90b5f23fc748e3ea357c748cb5722ed5c8ab57226d5c88b5f21fc7486b57287c7484b5720ed5c82b57206d5c80,
  0x3ee3dcfa9f53ea3d4fa8f53ea7d75d4bab732e6dccb83ee3df5d4b23ea3d6dccb0b5768f5d4b2b732c6dccb0b5f2bed5caa3ea3d6d5ca8b572aed5caab572a6d5ca8b5f29ed5ca2b57286d5ca0b5728ed5ca2b57286d5ca0,
  0x3ee35cfa9d53ea354fa8d53ea754fa9d53ea354fa8d53ee35cfa9d53ea357ea4d43ea757794d2be3346f8cd03ee35cfa9d53ea354fa8d53ea756d5c8a3ea356d5c88bcf31fe34c63ea357e34c4bc730ef1cc2bc7306f1cc0,
  0x3ee3dcfa9f53ea3d4fa8f53ea7d4fa9f53ea3d4fa8f53ee3dcfa9f53ea3d4fa8f53ea7d7794f2be33c6f8cf03ee3dcfa9f53ea3d4fa8f53ea7d6d5caa3ea3d6d5ca8bcf39ed5caa3ea3d6d5ca8bc738ef1ce2bc7386f1ce0,
  0x3fa575ae95d6ba577ae51c6ba576d5d0ab73466dcd183ea554fa9553ea557ae5143ea556d5d02b73446dcd10b5f43fa750eb574a7a750cb5742ed5d0ab57426d5d08b5f41fa7506b57487a7504b5740ed5d02b57406d5d00,
  0x3fa5f4fa9f53ea7d6d5d2a3ea7d6d5d2ab734e6dcd383ea5d4fa9753ea5d6d5d223ea5d6d5d22b734c6dcd30b5f4bed5d2ab574a6d5d28b574aed5d2ab574a6d5d28b5f49ed5d22b57486d5d20b5748ed5d22b57486d5d20,
  0x3fa575ae95d6ba577ae55c6ba575ae95d6ba577ae5583ea554fa9553ea557ae5543ea554fa955be3546f8d50e9f53fa754e6ba577a754c6ba577a754ab57627a7548bcf51fa75463ea557a7544bc750ef1d42bc7506f1d40,
  0x3fa5f4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7bc5783ea5d4fa9753ea5d4fa9753ea5d4fa975be35c6f8d703fa5f4fa9f53ea7d7b55683ea7d7b556ab576a7b5568bcf59cfa9753ea5d6f1d60bc758ef1d62bc7586f1d60,
  0x3ea754fa9d53ea757ce59c3ea754fa9d5b73666dcd983ea754fa9d53ea757ce5943ea756d5d82b73646dcd90b5f63fc758e3ea757c758cb5762ed5d8ab57626d5d88b5f61fc7586b57687c7584b5760ed5d82b57606d5d80,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f5b736e6dcdb83ea7d4fa9f53ea7d6d5da23ea7d6d5da2b736c6dcdb0b5f6bcfa9f53ea7d6d5da8b576aed5daab576a6d5da8b5f69ed5da2b57686d5da0b5768ed5da2b57686d5da0,
  0x3ea754fa9d53ea754fa9d53ea754fa9d53ea754fa9d53ea754fa9d53ea757ea5d43ea754fa9d5be3746f8dd03ea754fa9d53ea754fa9d53ea754fa9d53ea756d5d88bcf71fe35c63ea757e35c4bc770ef1dc2bc7706f1dc0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f5be37c6f8df03ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d6d5da8bcf79cfa9f53ea7d6d5da8bc778ef1de2bc7786f1de0,
  0x3ea7d73d63a6ba977ae61ccf586b3d61acf58633d6184fe95f3d6326ba957ae614cf584b3d612cf58433d610e9f83fa760ee9d833a760ccf582b3d60acf58233d608e9f81fa7606e9d813a7604cf580b3d602cf58033d600,
  0x3ea7d4fa9f53ea7d73d6383ea7d73d63acf58e33d6383ea7d5aeb556bad573d6306bad573d632cf58c33d6303ea7d73d62ab576a73d628cf58ab3d62acf58a33d6286bad573d622b576873d620cf588b3d622cf58833d620,
  0x3ea7d4fa9f53ea7d7ae65c3ea7d73d65a6ba9773d6583ea7d5aeb556ba957ae6546bad573d6526ba9573d650e9f93fa764e6ba977a764ccf592b3d64acf59233d648e9f91fa76466ba957a7644cf590b3d642cf59033d640,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d73d67a3ea7d73d6783ea7d4fa9f53ea7d5aeb553ea7d73d6726bad573d6703ea7d4fa9f53ea7d6d5da93ea7d73d66ab576a73d6683ea7d5aeb556bad573d6606bad573d662cf59833d660,
  0x3ea7d4fa9f53ea7d7ce69c3ea7d75d69a6ba9775d6983ea7d6d5da36ba977ce694b5768f5d692cf59635d690f1fa3fc768e6ba977c768ccf592b5d68acf59235d688f1fa1fc7686b57687c7684cf592b5d682cf59235d680,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d75d6ba3ea7d75d6b83ea7d4fa9f53ea7d6d5da33ea7d75d6b2b5768f5d6b03ea7d4fa9f53ea7d6d5da93ea7d75d6aab576a75d6a83ea7d6d5da3b57686d5da1b5768f5d6a2b576875d6a0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d5aea5d3ea7d4fa9f53ea7d7ea6d43ea7d7796d26ba977796d03ea7d4fa9f53ea7d5aea5d3ea7d73d64a6ba9773d648f8fb1fe36c66ba977e36c4cf592b796c2cf5923796c0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7796f23ea7d7796f03ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d6d5da93ea7d4fa9f53ea7d6d5da93ea7d7796e2b576a7796e0,
  0x3ea7d4fa9f53ea7d7ae71c3ea7d73d63acf58ebae7183ea7d5aeb556bad57ae7146bad573d632cf58cbae710e9fc3fa770eb576a7a770ccf58eba770ae9dc23a7708e9fc1fa7706b57687a7704cf58cba7702e9dc03a7700,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7bc7383ea7d4fa9f53ea7d5aeb553ea7d5aeb556bad57bc7303ea7d4fa9f53ea7d6d5da93ea7d7b572ab576a7b57283ea7d5aeb556bad56d5da16bad57b5722b57687b5720,
  0x3ea7d4fa9f53ea7d7ae75c3ea7d4fa9f53ea7d7ae7583ea7d4fa9f53ea7d7ae7543ea7d5aeb556bad57ae750e9fd3fa774e3ea7d7a774c3ea7d7a774ab576a7a7748e9fd1fa77466bad57a77446bad57a7742e9dd03a7740,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7bc7783ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7bc7703ea7d4fa9f53ea7d4fa9f53ea7d7b576a3ea7d7b57683ea7d4fa9f53ea7d5aeb553ea7d7b57626bad57b5760,
  0x3ea7d4fa9f53ea7d7ce79c3ea7d4fa9f53ea7d7ce7983ea7d4fa9f53ea7d7ce7943ea7d6d5da3b5768fce790f1fe3fc778e3ea7d7c778c3ea7d7c778ab576a7c7788f1fe1fc7786b57687c7784b5768fc7782b57687c7780,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7dc7b83ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7dc7b03ea7d4fa9f53ea7d4fa9f53ea7d7d57aa3ea7d7d57a83ea7d4fa9f53ea7d6d5da13ea7d7d57a2b57687d57a0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7ea7d43ea7d4fa9f53ea7d7ea7d03ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d6d5da9f8ff1fe37c63ea7d7e37c43ea7d7e37c2b576a7e37c0,
  0x3ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7f87f03ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d4fa9f53ea7d7f17e23ea7d7f17e0]
private def word (m : M) := words[m.toNat / 32]! >>> (22*(m.toNat%32))
def repl (m : M) : M := BitVec.ofNat 11 (word m)
def cover (m : M) : M := BitVec.ofNat 11 (word m >>> 11)
def onEdge (m : M) (e : V × V) := m.getLsbD e.1.val || m.getLsbD e.2.val
def correct (m : M) : Bool :=
  decide (count (repl m) ≤ count m) &&
  edges.all (fun e => !onEdge m e || onEdge (repl m) e) &&
  decide (repl m &&& cover m = repl m) && covers 0 (cover m) &&
  decide (count (cover m) ≤ (if m &&& 7 = 7 then 8 else 7 : BitVec 4))
theorem certify (m : M) : correct m = true := by
  suffices h : ∀ a : Fin 64, ∀ b : Fin 32, correct (BitVec.ofNat 11 (32*a.val+b.val)) = true by
    have eq : BitVec.ofNat 11 (32 * (m.toNat/32) + m.toNat%32) = m := by rw [Nat.div_add_mod]; simp
    rw [←eq]
    exact h ⟨_,by have := m.isLt; omega⟩ ⟨_,Nat.mod_lt _ (by decide)⟩
  intro a
  fin_cases a <;> as_aux_lemma => decide +kernel
end PEqualNP.Research.G11Exchange

open PEqualNP.Research.G11Rare PEqualNP.Research.G11Exchange in
theorem PEqualNP.Research.G11Exchange :
    let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ K : Finset (Fin 11), ∃ J T : Finset (Fin 11), J.card ≤ K.card ∧
      (∀ a b, G.Adj a b → (a ∈ K ∨ b ∈ K) → a ∈ J ∨ b ∈ J) ∧
      J ⊆ T ∧ G.IsVertexCover (↑T) ∧ T.card ≤ (if ({0,1,2} : Finset (Fin 11)) ⊆ K then 8 else 7) := by
  intro G K
  obtain ⟨m,rfl⟩ := represents K
  have cert := certify m
  simp only [correct,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at cert
  obtain ⟨⟨⟨⟨size,preserve⟩,inside⟩,valid⟩,limit⟩ := cert
  refine ⟨vertices (repl m),vertices (cover m),?_,?_,?_,(corr 0 _).mpr valid,?_⟩
  · change (count (repl m)).toNat ≤ (count m).toNat at size
    simpa only [count_eq] using size
  · intro a b hab hit
    have keep (a b : V) (edge : (a,b) ∈ edges) (hit : a ∈ vertices m ∨ b ∈ vertices m) :
        a ∈ vertices (repl m) ∨ b ∈ vertices (repl m) := by
      have h := preserve (a,b) edge
      have yes : onEdge m (a,b) = true := by simpa [onEdge,vertices] using hit
      rw [yes] at h
      simpa [onEdge,vertices] using h
    have ed : ∀ a b : V, G.Adj a b → (a,b) ∈ edges ∨ (b,a) ∈ edges := by decide +kernel
    rcases ed a b hab with ab|ba
    · exact keep a b ab hit
    · exact (keep b a ba hit.symm).symm
  · intro v hv
    have h := congrArg (fun a : M => a.getLsbD v.val) inside
    have on : (repl m).getLsbD v.val = true := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [BitVec.getLsbD_and,on,Bool.true_and] using h⟩
  · by_cases h : ({0,1,2} : Finset V) ⊆ vertices m
    · have raw (a : V) (ha : a ∈ ({0,1,2} : Finset V)) := (Finset.mem_filter.mp (h ha)).2
      have a := raw 0 (by simp)
      have b := raw 1 (by simp)
      have c := raw 2 (by simp)
      change m.getLsbD 0 = true at a
      change m.getLsbD 1 = true at b
      change m.getLsbD 2 = true at c
      have hc : m &&& 7 = 7 := by rw [BitVec.and_comm]; exact (coreEq m).mpr ⟨a,b,c⟩
      rw [if_pos hc] at limit
      change (count (cover m)).toNat ≤ 8 at limit
      rw [if_pos h]
      simpa only [count_eq] using limit
    · have hc : ¬m &&& 7 = 7 := by
        intro yes
        apply h
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rw [BitVec.and_comm] at yes
        obtain ⟨b0,b1,b2⟩ := (coreEq m).mp yes
        rcases ha with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b0⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b2⟩
      rw [if_neg hc] at limit
      change (count (cover m)).toNat ≤ 7 at limit
      rw [if_neg h]
      simpa only [count_eq] using limit
