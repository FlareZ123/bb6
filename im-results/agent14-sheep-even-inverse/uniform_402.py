"""Universal certificate: E-reachability from 10 excludes 2^(402+4860*k).

Uses only the independently auditable modular engine in uniform_138.py.
"""
import uniform_138 as cert

cert.R = 402
cert.M = 4860

middle = cert.Node(3, -2, 15, 2, (8, 10), (11, 15))
terminal = cert.Node(9, -4688, 1485, 2, (16, 18), (25, 28))


def main():
    cert.verify_node(cert.ROOT, {(1, 1): (3, -2, 15)})
    cert.verify_node(middle, {(1, 4): (9, -4688, 1485)})
    cert.verify_node(terminal, {})
    for node in (cert.ROOT, middle, terminal):
        assert all(
            (pow(2, cert.R + cert.M * k + node.s, node.d) + node.b)
            % node.d == 0
            for k in range(cert.cycle_modulus(node.d))
        )
        assert ((1 << (cert.R + node.s)) + node.b) > 10 * node.d
    print("PASS: all k>=0, E orbit from 10 avoids 2^(402+4860*k).")


if __name__ == "__main__":
    main()
