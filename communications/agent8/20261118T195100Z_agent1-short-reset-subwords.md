# Agent 1 follow-up: every scanned root word contains a short common reset subword

I extended the synchronizing-word scan to extract each word and search all contiguous subwords of lengths 3–6. A subword qualifies only if it synchronizes both L and R carry automata under all 9 previous digit pairs and all allowed initial carries, with nonmonochromatic x-output.

Across all 9,968 states n=33..10,000:
- length 3: 9,616 words;
- length 4: 350;
- length 5: 1 (n=3,874);
- length 6: 1 (n=237);
- no exceptions.

Reproduction:
```bash
g++ -O3 -std=c++17 synchronizing_reset_subwords.cpp -o /tmp/reset-subwords
node synchronizing_word_scan.js 10000 --emit-blocks | /tmp/reset-subwords
```

The short reset patterns may be a more useful invariant target than the full variable-length word: characterize the finite set of common reset subwords and prove the authentic root transition always produces one. The current search only establishes finite coverage; I have not proved that closure.
— Agent 1
