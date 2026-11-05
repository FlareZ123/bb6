#include <gmpxx.h>
#include <openssl/sha.h>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

// Independent GMP implementation of the published genuine Sheep section map,
// complementary to the Python verifier and the Lean-certified E semantics.
int main() {
    constexpr long target_index = 441323;
    constexpr unsigned long modulus = 1000000007UL;
    const std::string expected = "94e089549afb02dcc8098cde8e1a1ac0ca241a1ac7bf595d76b4f7492c488e29";

    mpz_class x(10), z, w, u, power;
    for (long index = 0; index <= target_index; ++index) {
        assert(mpz_even_p(x.get_mpz_t()));
        unsigned long a = mpz_scan1(x.get_mpz_t(), 0);
        mpz_tdiv_q_2exp(u.get_mpz_t(), x.get_mpz_t(), a);
        assert(u >= 3 && mpz_odd_p(u.get_mpz_t()));
        z = x + a;
        if (u == 3) {
            z += 3;
        } else {
            assert(u >= 5);
            w = u - 1;
            mpz_tdiv_q_2exp(w.get_mpz_t(), w.get_mpz_t(), 1);
            z += w;
        }
        assert(z > x);
        w = z - 1;
        unsigned long h = mpz_scan1(w.get_mpz_t(), 0);
        if (index == target_index) {
            assert(a == 19 && h == 7);
            assert(mpz_sizeinbase(x.get_mpz_t(), 2) == 354071);
            assert(mpz_fdiv_ui(x.get_mpz_t(), modulus) == 882768040UL);
            std::vector<unsigned char> bytes((mpz_sizeinbase(x.get_mpz_t(), 2) + 7) / 8);
            size_t count = 0;
            mpz_export(bytes.data(), &count, 1, 1, 1, 0, x.get_mpz_t());
            assert(count == bytes.size());
            unsigned char digest[SHA256_DIGEST_LENGTH];
            SHA256(bytes.data(), count, digest);
            std::ostringstream out;
            for (unsigned char octet : digest)
                out << std::hex << std::setw(2) << std::setfill('0') << static_cast<unsigned>(octet);
            assert(out.str() == expected);
            std::cout << "PASS: index=" << index << " a=" << a << " h=" << h
                      << " capacity=" << (a + h + 1) << " bits="
                      << mpz_sizeinbase(x.get_mpz_t(), 2) << " SHA256=" << out.str() << '\n';
            return 0;
        }
        mpz_tdiv_q_2exp(w.get_mpz_t(), w.get_mpz_t(), h);
        mpz_ui_pow_ui(power.get_mpz_t(), 3UL, h);
        x = 1 + power * w;
        assert(mpz_even_p(x.get_mpz_t()));
    }
    return 1;
}
