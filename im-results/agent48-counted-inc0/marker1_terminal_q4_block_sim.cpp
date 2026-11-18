// Sparse 64-cell-block simulator for the marker-1 S0 family.
//
// Compile: g++ -O3 -std=c++17 marker1_terminal_q4_block_sim.cpp -o q4_block_sim
// Usage:   ./q4_block_sim A L z max_steps target_checkpoints
//
// The simulator uses the repository's TM2 transition table and S0 encoding.
// At every state-4/read-0 checkpoint with head coordinate 1, it checks the
// entire left finite-support word
//   011 ++ binDec(A+L+2, M-j) ++ lh,
// where M=2^A*(2^(L+2)-1). It reports checkpoint times and q4-event indices.
// It does not prove halting or check a general positive-z right-side macro.

#include <bits/stdc++.h>
using namespace std;

static inline long long blockOf(long long p) {
  return p >= 0 ? p / 64 : -((-p + 63) / 64);
}

static inline int offsetOf(long long p, long long block) {
  return static_cast<int>(p - block * 64);
}

static vector<int> binDec(int width, long long n) {
  long long p = (1LL << (width + 1)) - 1 - n;
  vector<int> out;
  for (int i = 0; i < width; ++i) {
    if (p <= 1) break;
    if (p % 2 == 0) out.insert(out.end(), {0, 0, 1});
    else out.insert(out.end(), {1, 1, 1});
    p /= 2;
  }
  return out;
}

int main(int argc, char** argv) {
  if (argc != 6) {
    cerr << "usage: " << argv[0] << " A L z max_steps target_checkpoints\n";
    return 2;
  }
  const int A = atoi(argv[1]);
  const int L = atoi(argv[2]);
  const long long z = atoll(argv[3]);
  const unsigned long long limit = strtoull(argv[4], nullptr, 10);
  const int targetCheckpoints = atoi(argv[5]);
  if (A < 1 || L < 2 || (L % 2) != 0 || z < 0 || A + L + 2 >= 60 ||
      z >= (1LL << A) || targetCheckpoints < 1) {
    cerr << "invalid parameters (require A>=1, even L>=2, 0<=z<2^A, A+L+2<60)\n";
    return 2;
  }

  const long long M = (1LL << A) * ((1LL << (L + 2)) - 1);
  const int width = A + L + 2;
  const vector<int> lh = {1, 1, 0, 1, 1, 1};
  const vector<int> right0 = {0, 1, 1, 1, 0, 0, 1, 1, 1};

  // S0 left tape: binDec A z ++ markerWord1 ++ d0 ++ d1pow L ++ lh.
  vector<int> left = binDec(A, z);
  left.insert(left.end(), {1, 0, 1, 0, 0, 1});
  left.insert(left.end(), 3 * L, 1);
  left.insert(left.end(), lh.begin(), lh.end());

  // Sparse tape: one uint64_t per nonzero 64-cell block.
  unordered_map<long long, uint64_t> blocks;
  blocks.max_load_factor(0.7);
  blocks.reserve(1 << 16);
  auto putInitial = [&](long long position) {
    const long long block = blockOf(position);
    const int offset = offsetOf(position, block);
    blocks[block] |= (1ULL << offset);
  };
  for (size_t i = 0; i < left.size(); ++i)
    if (left[i]) putInitial(-static_cast<long long>(i));
  for (size_t i = 0; i < right0.size(); ++i)
    if (right0[i]) putInitial(1 + static_cast<long long>(i));

  int state = 3;
  long long head = 0;
  long long currentBlock = blockOf(head);
  int currentOffset = offsetOf(head, currentBlock);
  uint64_t currentWord = 0;
  if (auto it = blocks.find(currentBlock); it != blocks.end())
    currentWord = it->second;

  auto bitAt = [&](long long position) -> bool {
    const long long block = blockOf(position);
    const int offset = offsetOf(position, block);
    if (block == currentBlock) return ((currentWord >> offset) & 1ULL) != 0;
    auto it = blocks.find(block);
    return it != blocks.end() && ((it->second >> offset) & 1ULL) != 0;
  };

  auto checkLeftFrame = [&](int j) -> bool {
    vector<int> expectedWord = {0, 1, 1};
    const vector<int> counter = binDec(width, M - j);
    expectedWord.insert(expectedWord.end(), counter.begin(), counter.end());
    expectedWord.insert(expectedWord.end(), lh.begin(), lh.end());

    unordered_set<long long> expectedSupport;
    for (size_t i = 0; i < expectedWord.size(); ++i)
      if (expectedWord[i]) expectedSupport.insert(1 - static_cast<long long>(i));

    // No unexpected 1 may occur anywhere on or to the left of the head.
    for (const auto& entry : blocks) {
      if (entry.first == currentBlock) continue; // currentWord is the live copy
      uint64_t word = entry.second;
      while (word) {
        const int bit = __builtin_ctzll(word);
        const long long position = entry.first * 64 + bit;
        if (position <= 1 && !expectedSupport.count(position)) return false;
        word &= word - 1;
      }
    }
    uint64_t live = currentWord;
    while (live) {
      const int bit = __builtin_ctzll(live);
      const long long position = currentBlock * 64 + bit;
      if (position <= 1 && !expectedSupport.count(position)) return false;
      live &= live - 1;
    }

    // Every expected 1 is present.
    for (long long position : expectedSupport)
      if (!bitAt(position)) return false;
    return true;
  };

  unsigned long long q4ZeroEvents = 0;
  vector<pair<unsigned long long, unsigned long long>> checkpoints;

  for (unsigned long long elapsed = 0; elapsed < limit; ++elapsed) {
    const bool readOne = ((currentWord >> currentOffset) & 1ULL) != 0;
    if (state == 4 && !readOne) {
      ++q4ZeroEvents;
      if (head == 1) {
        const int j = static_cast<int>(checkpoints.size()) + 1;
        if (!checkLeftFrame(j)) {
          cerr << "LEFT FRAME FAIL j=" << j << " step=" << elapsed << "\n";
          return 3;
        }
        checkpoints.push_back({elapsed, q4ZeroEvents});
        cout << "CHECKPOINT j=" << j << " step=" << elapsed
             << " event_index=" << q4ZeroEvents;
        if (j > 1) {
          cout << " cycle_steps=" << (elapsed - checkpoints[j - 2].first)
               << " cycle_events=" << (q4ZeroEvents - checkpoints[j - 2].second);
        }
        cout << " left_ok=1 blocks=" << blocks.size() << "\n";
        if (j >= targetCheckpoints) return 0;
      }
    }

    int write = -1;
    int move = 0;
    int nextState = 0;
    bool halt = false;
    switch (state) {
      case 0:
        if (!readOne) { write = 1; move = 1; nextState = 1; }
        else halt = true;
        break;
      case 1:
        if (!readOne) { write = 1; move = -1; nextState = 2; }
        else { write = 0; move = 1; nextState = 5; }
        break;
      case 2:
        if (!readOne) { write = 1; move = 1; nextState = 4; }
        else { write = 0; move = -1; nextState = 3; }
        break;
      case 3:
        if (!readOne) { write = 0; move = -1; nextState = 2; }
        else { write = 1; move = 1; nextState = 1; }
        break;
      case 4:
        write = 1; move = 1; nextState = readOne ? 4 : 0;
        break;
      case 5:
        if (!readOne) { write = 1; move = 1; nextState = 4; }
        else { write = 0; move = 1; nextState = 3; }
        break;
      default:
        cerr << "invalid state\n";
        return 4;
    }

    if (halt) {
      cout << "HALT step=" << elapsed << " q4_events=" << q4ZeroEvents
           << " checkpoints=" << checkpoints.size() << "\n";
      return 0;
    }

    if (write == 1) currentWord |= (1ULL << currentOffset);
    else if (write == 0) currentWord &= ~(1ULL << currentOffset);

    head += move;
    state = nextState;
    const long long nextBlock = blockOf(head);
    const int nextOffset = offsetOf(head, nextBlock);
    if (nextBlock != currentBlock) {
      if (currentWord) blocks[currentBlock] = currentWord;
      else blocks.erase(currentBlock);
      currentBlock = nextBlock;
      auto it = blocks.find(currentBlock);
      currentWord = (it == blocks.end() ? 0 : it->second);
    }
    currentOffset = nextOffset;
  }

  cout << "LIMIT steps=" << limit << " q4_events=" << q4ZeroEvents
       << " checkpoints=" << checkpoints.size();
  if (!checkpoints.empty())
    cout << " last_checkpoint_step=" << checkpoints.back().first
         << " last_event_index=" << checkpoints.back().second;
  cout << " blocks=" << blocks.size() << "\n";
  return 0;
}
