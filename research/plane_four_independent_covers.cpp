// Build with c++ -std=c++20 -O3. All masks use point bits 0..20, line bits 21..41.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

int main() {
    constexpr unsigned side = (1u << 21) - 1;
    std::array<unsigned, 21> neighbors{};
    for (int p = 0; p < 21; ++p)
        for (int d : {0, 5, 7, 17, 20}) neighbors[p] |= 1u << ((p + d) % 21);

    std::array<unsigned, 43> histogram{};
    std::vector<std::uint64_t> eight;
    // Maximality forces the line half once the point half is chosen.
    for (unsigned points = 0; points <= side; ++points) {
        unsigned lines = side;
        for (unsigned t = points; t; t &= t - 1)
            lines &= ~neighbors[std::countr_zero(t)];
        bool maximal = true;
        for (int p = 0; p < 21; ++p)
            if (!(points & (1u << p)) && !(lines & neighbors[p])) {
                maximal = false;
                break;
            }
        if (!maximal) continue;
        int size = std::popcount(points) + std::popcount(lines);
        ++histogram[size];
        if (size == 8) eight.push_back(points | (std::uint64_t(lines) << 21));
    }
    for (int size = 0; size <= 42; ++size)
        if (histogram[size]) std::cout << size << " vertices: " << histogram[size] << '\n';

    if (eight.size() != 105) throw std::runtime_error("unexpected witness count");
    using Choices = std::bitset<105>;
    std::array<Choices, 42> on;
    for (std::size_t t = 0; t < eight.size(); ++t)
        for (int i = 0; i < 42; ++i) on[i][t] = (eight[t] >> i) & 1;
    std::vector<Choices> pairs;
    for (int i = 0; i < 42; ++i)
        for (int j = i + 1; j < 42; ++j) pairs.push_back(on[i] | on[j]);
    std::size_t minimum = eight.size();
    for (const auto &a : pairs)
        for (const auto &b : pairs) minimum = std::min(minimum, (a & b).count());
    std::cout << pairs.size() * pairs.size() << " ordered pairs of raw OR gates: minimum "
              << minimum << " common accepting baselines\n";
    std::cout << "Triple (0,1), (0,2), (21,28): "
              << ((on[0] | on[1]) & (on[0] | on[2]) & (on[21] | on[28])).count()
              << " common accepting baselines\n";

    // Reconstruct the seven translated private-edge samples used in Lean.
    // A base center chooses its lexicographically first incident edge whose
    // other endpoint is in the independent set.
    using VertexSet = std::bitset<42>;
    using EdgeSet = std::bitset<21 * 21>;
    const VertexSet baseline{0x185ULL | (0x50c00ULL << 21)};
    std::vector<std::pair<int, int>> privateEdges;
    for (int center = 0; center < 42; ++center) {
        if (baseline[center]) continue;
        bool found = false;
        for (int point = 0; point < 21 && !found; ++point) {
            for (int line = 0; line < 21 && !found; ++line) {
                if (!(neighbors[point] & (1u << line))) continue;
                if (!((center == point && baseline[21 + line]) ||
                      (center == 21 + line && baseline[point]))) continue;
                privateEdges.emplace_back(point, line);
                found = true;
            }
        }
        if (!found) throw std::runtime_error("missing private incidence");
    }
    if (privateEdges.size() != 34) throw std::runtime_error("wrong sample size");

    VertexSet omitted;
    EdgeSet commonSamples;
    commonSamples.set();
    for (int offset = 0; offset < 21; offset += 3) {
        VertexSet independent;
        for (int v = 0; v < 42; ++v)
            if (baseline[v]) independent.set(21 * (v / 21) + (v % 21 + offset) % 21);
        for (int p = 0; p < 21; ++p) {
            if (!independent[p]) continue;
            for (int l = 0; l < 21; ++l)
                if ((neighbors[p] & (1u << l)) && independent[21 + l])
                    throw std::runtime_error("rotation lost independence");
        }
        EdgeSet current;
        VertexSet centers;
        for (const auto &[point, line] : privateEdges) {
            int p = (point + offset) % 21;
            int l = (line + offset) % 21;
            if (!(neighbors[p] & (1u << l)) || independent[p] == independent[21 + l])
                throw std::runtime_error("invalid translated sample");
            int center = independent[p] ? 21 + l : p;
            if (centers[center]) throw std::runtime_error("repeated sample center");
            centers.set(center);
            current.set(21 * p + l);
        }
        if (centers != ~independent || current.count() != 34)
            throw std::runtime_error("incomplete private-edge family");
        omitted |= independent;
        commonSamples &= current;
    }
    if (!omitted.all() || commonSamples.any())
        throw std::runtime_error("seven rotations do not certify a neutral first union");
    std::cout << "Seven translated 34-edge samples: all 42 vertices omitted somewhere, "
                 "zero edges sampled everywhere\n";
}
