// Stronger adversarial first-event synchrony stress test, using the direct
// D Cryptid raw primitive simulator. Suffixes are composed from long nested
// E and A code packets rather than uniform random bits.
#define main original_verifier_main
#include "shift_first_event.cpp"
#undef main

static bool verify(int k, int r, const std::vector<std::uint8_t>& suffix,
                   long& halts, int& maxLevel) {
    int n = 3*k+r;
    Result a = first_event(n, suffix, 5000000);
    Result b = first_event(n+3, suffix, 5000000);
    Result c = first_event(n+6, suffix, 5000000);
    if (a.kind==2 || b.kind==2 || c.kind==2) return false;
    if (a.kind==1) ++halts;
    bool same = a.kind==b.kind && b.kind==c.kind;
    if (a.kind==0) {
        same = same && a.tail==b.tail && b.tail==c.tail
               && b.unary==a.unary+8 && c.unary==a.unary+16;
    }
    int dt = b.time-a.time;
    int base = a.kind==0 ? 61:53;
    int offset = dt-(24*k+base);
    bool timed = offset>=0 && offset%24==0 && c.time-b.time==dt+24;
    if (same && timed) {
        maxLevel=std::max(maxLevel,offset/24);
        return true;
    }
    std::fprintf(stderr,
       "FAIL n=%d len=%zu kinds=%d,%d,%d dt=%d offset=%d\n",
       n,suffix.size(),a.kind,b.kind,c.kind,dt,offset);
    return false;
}

int main() {
    std::mt19937_64 rng(202611051907ULL);
    long halts=0;
    int maximum=0;
    for (int trial=0;trial<11000;++trial) {
        int r=2+int(rng()%3), k=int(rng()%130),
            q=int(rng()%240), p=int(rng()%130), mode=trial%5;
        std::vector<std::uint8_t> w;
        auto add=[&](const char *pattern) {
            for (auto ch=pattern;*ch;++ch) w.push_back(*ch=='1');
        };
        if(mode==0){add("0");for(int i=0;i<q;++i)add("10");add("1101010111");for(int i=0;i<p;++i)add(i%3?"1":"0");}
        if(mode==1){add("0");for(int i=0;i<q;++i)add("10");add("11");for(int i=0;i<p;++i)add("01");add("1101100");}
        if(mode==2){add("0");for(int i=0;i<q;++i)add(i%5?"111":"10");add("1101101100");}
        if(mode==3){add("0");for(int i=0;i<q;++i)add(i%4?"10":"111");add("110111");for(int i=0;i<p;++i)add(i%2?"01":"11");}
        if(mode==4){add("0");for(int i=0;i<q;++i)add("10");add("1101010111");for(int i=0;i<p;++i)add("10101010");}
        if (!verify(k,r,w,halts,maximum)) return 1;
    }
    std::printf("PASS: 11000/11000 nested-structured first events, "
                "halts=%ld maximum timing level=%d\n",halts,maximum);
    return 0;
}
