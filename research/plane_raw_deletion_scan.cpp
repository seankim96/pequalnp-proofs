// Enumerate every k-flag deletion. The input is (exact witness mask, pair count).
// Output includes the exceptional masks that need an endpoint-cover check.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

using Mask = std::uint64_t;
constexpr int flags = 52;
constexpr int max_deleted = 7;
constexpr int budget = 211;
int deleted;
int choose[flags + 1][max_deleted + 1];
int singleton[flags], pair_weight[flags][flags];
std::array<int, max_deleted> selected;
std::vector<unsigned char> higher;
std::uint64_t subsets, total_bad, expected_total, over_budget;
int maximum;
Mask worst;

// Add the frequency of a witness mask to every k-set containing that mask.
void distribute(Mask mask, int next, int left, int weight) {
    if (left == 0) {
        int rank = 0, k = 1;
        while (mask) {
            rank += choose[std::countr_zero(mask)][k++];
            mask &= mask - 1;
        }
        if (higher[rank] + weight > 255) std::abort();
        higher[rank] += weight;
        return;
    }
    for (int i = next; i <= flags - left; ++i) {
        Mask bit = Mask{1} << i;
        if (!(mask & bit)) distribute(mask | bit, i + 1, left - 1, weight);
    }
}

// Colexicographic rank indexes higher-order weights. Accumulate singleton and
// pair weights as new flags enter the selected tuple.
void scan(int depth, int next, int partial, int rank, Mask mask) {
    if (depth == deleted) {
        const int bad = partial + higher[rank];
        ++subsets;
        total_bad += bad;
        if (bad > maximum) {
            maximum = bad;
            worst = mask;
        }
        if (bad > budget) {
            ++over_budget;
            std::printf("%llx %d\n", static_cast<unsigned long long>(mask), bad);
        }
        return;
    }
    for (int i = next; i <= flags - deleted + depth; ++i) {
        int add = singleton[i];
        for (int j = 0; j < depth; ++j) add += pair_weight[selected[j]][i];
        selected[depth] = i;
        scan(depth + 1, i + 1, partial + add, rank + choose[i][depth + 1], mask | (Mask{1} << i));
    }
}

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    deleted = std::atoi(argv[1]);
    if (deleted < 1 || deleted > max_deleted) return 2;
    for (int i = 0; i <= flags; ++i) {
        choose[i][0] = 1;
        for (int j = 1; j <= deleted && j <= i; ++j)
            choose[i][j] = choose[i-1][j] + choose[i-1][j-1];
    }
    higher.resize(choose[flags][deleted]);
    unsigned long long raw;
    int weight;
    while (std::scanf("%llu%d", &raw, &weight) == 2) {
        Mask mask = raw;
        int size = std::popcount(mask);
        if ((mask >> flags) || weight <= 0) return 2;
        if (size > deleted) continue;
        expected_total += std::uint64_t(weight) * choose[flags-size][deleted-size];
        if (size == 1) singleton[std::countr_zero(mask)] = weight;
        else if (size == 2)
            pair_weight[std::countr_zero(mask)][std::countr_zero(mask & (mask-1))] = weight;
        else distribute(mask, 0, deleted-size, weight);
    }
    scan(0, 0, 0, 0, 0);
    if (total_bad != expected_total || subsets != unsigned(choose[flags][deleted])) return 1;
    std::fprintf(stderr, "%d %llu %d %llx %llu %llu\n", deleted,
        static_cast<unsigned long long>(subsets), maximum, static_cast<unsigned long long>(worst),
        static_cast<unsigned long long>(over_budget), static_cast<unsigned long long>(total_bad));
}
