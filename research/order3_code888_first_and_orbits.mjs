import {readFileSync} from "node:fs";

// Reproduce the complete first-AND finite test on the repository's 520 inputs.
function certify(leanSource) {
  function readRows(name) {
    const match = leanSource.match(new RegExp("def " + name + " : Array Nat := #\\[([^\\]]+)"));
    if (!match) throw Error("missing row table " + name);
    return match[1].split(",").map(Number);
  }
  function check(ok, message) { if (!ok) throw Error(message); }
  function pop32(x) {
    x -= (x >>> 1) & 0x55555555;
    x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
    return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
  }
  function count(x) {
    let result = 0;
    while (x) { result += pop32(Number(x & 0xffffffffn)); x >>= 32n; }
    return result;
  }
  function extend(x) {
    const bit = i => (x >>> i) & 1;
    return x | ((bit(0) & bit(13)) << 26) | ((bit(0) | bit(14)) << 27) |
      ((bit(1) & bit(13)) << 28) | ((bit(1) & bit(18)) << 29);
  }
  const rawP = readRows("positive"), rawN = readRows("negative");
  const pos = rawP.map(extend), neg = rawN.map(extend);
  check(pos.length === 52 && neg.length === 468, "test count");
  const bits = neg.map((_, i) => 1n << BigInt(i));
  const flags = pos.map((_, i) => 1n << BigInt(i));
  const full = (1n << 468n) - 1n;
  const setters = [...neg, ...pos];
  const cols = Array.from({length: 30}, (_, k) => setters.reduce(
    (z, row, i) => row & (1 << k) ? z | (1n << BigInt(i)) : z, 0n));
  const ideal = cols[26] | cols[28] | cols[29];
  check(!(ideal & full) && count(ideal) === 3 && cols[27] === (cols[0] | cols[14]), "prefix");
  const witness = neg.map((right, j) => neg.slice(0, j).map(left =>
    pos.reduce((mask, p, i) => p & ~(left | right) ? mask : mask | flags[i], 0n)));
  const edges = [], partner = neg.map(() => 468);
  for (let j = 0; j < 468; j++) for (let i = 0; i < j; i++) {
    if (witness[j][i]) continue;
    check(partner[i] === 468 && partner[j] === 468, "conflicts are not a matching");
    partner[i] = j; partner[j] = i; edges.push(bits[i] | bits[j]);
  }
  function alpha(mask) {
    return count(mask) - edges.reduce((n, e) => n + Number((mask & e) === e), 0);
  }
  const wires = Array.from({length:26}, (_, i) => i);
  const sets = [new Set(rawP), new Set(rawN)];
  const adj = wires.map(i => wires.map(j => i !== j && sets[0].has((1 << i) | (1 << j))));
  function extendMap(m) {
    if (m.size === 26) return [wires.map(i => m.get(i))];
    const used = new Set(m.values());
    let best = null, key = 0;
    for (const i of wires) if (!m.has(i)) {
      const options = wires.filter(j => !used.has(j) &&
        [...m].every(([a,b]) => adj[i][a] === adj[j][b]));
      if (best === null || options.length < best.length) { best = options; key = i; }
    }
    const result = [];
    for (const v of best) { m.set(key,v); result.push(...extendMap(m)); m.delete(key); }
    return result;
  }
  // The three ideal flags are the edges of the path 0--13--1--18.
  const path = [0,13,1,18], reversal = path.slice().reverse();
  const group = [path, reversal].flatMap(image =>
    extendMap(new Map(path.map((v,i) => [v,image[i]]))));
  function move(mask, g) {
    return wires.reduce((z, i) => mask & (1 << i) ? z | (1 << g[i]) : z, 0);
  }
  check(new Set(group.map(g => g.join(","))).size === 24, "group order");
  for (const g of group) {
    check(new Set(g).size === 26, "map not bijective");
    for (const [rows, s] of [[rawP,sets[0]], [rawN,sets[1]]])
      check(rows.every(r => s.has(move(r,g))), "row family not invariant");
  }
  const known = new Set(group.map(g => g.join(",")));
  for (const g of group) for (const h of group)
    check(known.has(g.map(v => h[v]).join(",")), "group not closed");
  const options = [], bySize = [0,0,0,0,0], quads = new Set();
  let minQuartet = 468, minSingleton = 468;
  function visit(next, used, mask, column) {
    const n = column & full;
    const t = alpha(n), f = alpha(full & ~n);
    if (used === 1) minSingleton = Math.min(minSingleton, f);
    if (used === 4) {
      minQuartet = Math.min(minQuartet,t);
      quads.add(Math.min(...group.map(g => move(mask,g))));
    }
    if (Math.max(t,f) < 257) {
      options.push({mask,column}); bySize[used]++;
    }
    if (used < 4) for (let k = next; k < 26; k++)
      visit(k+1,used+1,mask | (1 << k),column | cols[k]);
  }
  visit(0,0,0,0n);
  check(minQuartet >= 257, "large disjunctions not covered");
  check(minSingleton >= 257, "singletons not covered");
  const index = new Map(options.map((a,i) => [a.mask,i]));
  const action = group.map(g => options.map(a => {
    const id = index.get(move(a.mask,g));
    check(id !== undefined, "balanced set not invariant");
    return id;
  }));
  const singles = new Set(options.map((_,i) => Math.min(...action.map(a => a[i]))));
  const length = options.length, seen = new Uint8Array(length * length);
  const key = (i,j) => Math.max(i,j) * length + Math.min(i,j);
  let pairs = 0, orbits = 0;
  const hard = [];
  for (let j = 0; j < length; j++) for (let i = 0; i < j; i++) {
    if (seen[key(i,j)]) continue;
    const orbit = new Set(action.map(a => key(a[i],a[j])));
    for (const k of orbit) { check(!seen[k], "overlapping orbits"); seen[k] = 1; }
    pairs += orbit.size; orbits++;
    const a = options[i], b = options[j];
    const av = a.column & ~b.column, bv = b.column & ~a.column;
    if (Math.max(alpha(full & ~av),alpha(full & ~bv)) < 257) {
      hard.push({a:a.mask, b:b.mask, orbit:orbit.size});
    }
  }
  check(pairs === length*(length-1)/2, "incomplete orbit cover");

  const reps = [
    [[2,4,10], [1,14]],
    [[14,17], [4,16]],
    [[15,17], [4,5]]
  ];
  const pack = keys => keys.reduce((m,k) => m | (1 << k), 0);
  const disj = keys => keys.reduce((m,k) => m | cols[k], 0n);
  const positiveMask = reps.reduce((m,[a,b]) => m | ((disj(a) & disj(b)) | ideal), 0n) >> 468n;
  check(positiveMask === 0x1604e3n, "unexpected positive mask");
  const avoid = neg.map(() => 0n);
  for (let j = 0; j < 468; j++) for (let i = 0; i < j; i++) {
    if (witness[j][i] & ~positiveMask) continue;
    avoid[i] |= bits[j]; avoid[j] |= bits[i];
  }
  const independent = [];
  let active = full;
  while (active) {
    let best = -1, degree = 469;
    for (let i = 0; i < 468; i++) if (active & bits[i]) {
      const d = count(avoid[i] & active);
      if (d < degree) { degree = d; best = i; if (!d) break; }
    }
    independent.push(best);
    active &= ~(avoid[best] | bits[best]);
  }
  independent.sort((a,b) => a-b);
  const sample = independent.slice(0,257);
  check(sample.length === 257, "no common certificate");
  // This scalar replay uses neither the graph nor its witness bit masks.
  const retained = pos.filter((_,i) => !(positiveMask & flags[i]));
  for (let j = 0; j < sample.length; j++) for (let i = 0; i < j; i++)
    check(retained.some(p => !(p & ~(neg[sample[i]] | neg[sample[j]]))), "invalid common family");

  const syntaxKey = (a,b) => [Math.min(a,b),Math.max(a,b)].join(",");
  const hardOrbits = new Map();
  for (const {a,b} of hard) for (const g of group)
    hardOrbits.set(syntaxKey(move(a,g),move(b,g)), 0);
  const rawIndex = new Map(rawN.map((v,i) => [v,i]));
  const hardCases = [];
  for (const [a,b] of reps) {
    const aMask=pack(a), bMask=pack(b), orbit = new Set();
    for (const g of group) {
      const left = a.map(k => g[k]), right = b.map(k => g[k]);
      const token = syntaxKey(move(aMask,g),move(bMask,g));
      if (orbit.has(token)) continue;
      orbit.add(token);
      check(hardOrbits.has(token) && !hardOrbits.get(token), "wrong or duplicate residual orbit");
      hardOrbits.set(token,1);
      // Check the transported certificate on the actual rows; even the
      // pessimistic AND, granting all ideal positives, must retain a witness.
      const column = (disj(left) & disj(right)) | ideal;
      const ns = sample.map(i => rawIndex.get(move(rawN[i],g)));
      check(new Set(ns).size === 257 && !ns.includes(undefined), "transport dropped a row");
      const lifted = (row,k) => row | (Number((column >> BigInt(k)) & 1n) << 30);
      const pp = pos.map((p,k) => lifted(p,468+k));
      const nn = ns.map(i => lifted(neg[i],i));
      for (let j = 0; j < 257; j++) for (let i = 0; i < j; i++)
        check(pp.some(p => !(p & ~(nn[i] | nn[j]))), "transport failed direct scalar check");
    }
    hardCases.push({left:a,right:b,orbit:orbit.size});
  }
  check([...hardOrbits.values()].every(v => v === 1), "uncovered residual orbit");
  return {conflicts:edges.length,baseIndependent:alpha(full),minSingletonFalse:minSingleton,
    minQuartetTrue:minQuartet,quartetOrbits:quads.size,groupSize:group.length,balancedBySize:bySize,
    balanced:length,operandOrbits:singles.size,syntaxPairs:pairs,pairOrbits:orbits,hardCases,
    positiveOmissionMask:positiveMask.toString(16),independent:independent.length,
    residualSyntaxes:hardOrbits.size,transportedPairs:hardOrbits.size*257*256/2,
    negativeIndices:sample};
}

const path = new URL("../lean/PEqualNP/Research/OrderThreePlanePrefixData.lean", import.meta.url);
const result = certify(readFileSync(path, "utf8"));
console.log(JSON.stringify(result, null, 2));
