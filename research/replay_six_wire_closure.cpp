// Independent numerical replay of a six-input closure from live_wire_search.py.
// Usage: replay CAP TABLE < states.txt   (decimal or 0x-prefixed target).
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Wires = std::vector<Word>;

class Replay {
    Word target;
    std::vector<std::set<Wires>> closed;
    std::vector<unsigned> negatives;

    bool impossible(unsigned remaining, const Wires& wires) const {
        if (wires.size() > remaining + 1) return true;
        if (remaining == 0) return wires != Wires{target};
        for (unsigned row : negatives) {
            Word indistinguishable = target;
            Word below = target;
            for (Word w : wires) {
                if ((w >> row) & 1) {
                    indistinguishable &= w;
                } else {
                    indistinguishable &= ~w;
                    below &= ~w;
                }
            }
            if (indistinguishable || (wires.size() == remaining + 1 && below)) return true;
        }
        return false;
    }

    void require_closed(unsigned remaining, Wires wires) const {
        if (impossible(remaining, wires)) return;
        std::sort(wires.begin(), wires.end());
        if (remaining == 0 || !closed.at(remaining).count(wires))
            throw std::runtime_error("reachable terminal or missing state at " +
                                     std::to_string(remaining) + " remaining gates");
    }

    void check_step(unsigned remaining, const Wires& state) const {
        if (impossible(remaining, state)) return;
        if (remaining == 0) throw std::runtime_error("target in closure");
        for (unsigned i = 0; i < state.size(); ++i) {
            // Enumerate all masks of retained operands. The cardinality test
            // in require_closed handles branches with too many live wires.
            for (unsigned j = i; j < state.size(); ++j) {
                Wires rest;
                for (unsigned k = 0; k < state.size(); ++k)
                    if (k != i && k != j) rest.push_back(state[k]);
                const Word a = state[i], b = state[j];
                const auto outputs = i == j ? std::array<Word, 2>{a, ~a}
                                            : std::array<Word, 2>{a & b, a | b};
                for (Word output : outputs) {
                    for (unsigned keep = 0; keep < (i == j ? 2u : 4u); ++keep) {
                        Wires next = rest;
                        next.push_back(output);
                        if (keep & 1) next.push_back(a);
                        if (keep & 2) next.push_back(b);
                        require_closed(remaining - 1, next);
                    }
                }
            }
        }
    }

public:
    Replay(unsigned cap, Word y) : target(y), closed(cap + 1) {
        if (y == 0 || ~y == 0) throw std::runtime_error("constant target");
        for (unsigned row = 0; row < 64; ++row)
            if (!((target >> row) & 1)) negatives.push_back(row);
    }

    std::size_t verify(std::istream& in) {
        std::size_t count = 0;
        std::string line;
        while (std::getline(in, line)) {
            std::istringstream fields(line);
            unsigned t;
            if (!(fields >> t) || t >= closed.size()) throw std::runtime_error("bad budget");
            Wires wires;
            Word w;
            while (fields >> w) wires.push_back(w);
            if (!fields.eof() || !std::is_sorted(wires.begin(), wires.end()))
                throw std::runtime_error("bad state");
            if (!closed[t].insert(wires).second) throw std::runtime_error("duplicate state");
            ++count;
        }
        Word inputs[6] = {};
        for (unsigned i = 0; i < 6; ++i)
            for (unsigned row = 0; row < 64; ++row)
                if ((row >> i) & 1) inputs[i] |= Word{1} << row;
        for (unsigned subset = 0; subset < 64; ++subset) {
            Wires wires;
            for (unsigned i = 0; i < 6; ++i)
                if ((subset >> i) & 1) wires.push_back(inputs[i]);
            require_closed(closed.size() - 1, wires);
        }
        for (unsigned t = 0; t < closed.size(); ++t)
            for (const Wires& state : closed[t]) check_step(t, state);
        return count;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::runtime_error("expected CAP TABLE and states on stdin");
        const unsigned cap = std::stoul(argv[1]);
        if (cap > 63) throw std::runtime_error("unsupported budget");
        Replay checker(cap, std::stoull(argv[2], nullptr, 0));
        const auto count = checker.verify(std::cin);
        std::cout << "CLOSED states=" << count << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
