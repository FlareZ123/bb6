"""Two further uniformly excluded Sheep even-return halting-exponent classes.

Requires only uniform_138.py in the same folder; no third-party packages.
The mathematical soundness argument is in UNIFORM-138.md.
"""
import uniform_138 as cert


def run_case(r, cases):
    cert.R = r
    cert.M = 4860
    for node, children in cases:
        cert.verify_node(node, children)
        for k in range(cert.cycle_modulus(node.d)):
            assert (
                pow(2, r+4860*k+node.s, node.d)+node.b
            ) % node.d == 0
        assert ((1 << (r+node.s))+node.b)>10*node.d
    print("PASS: E orbit from 10 avoids all 2^(",r,"+4860*k).")


def main():
    run_case(1218, [
        (cert.ROOT,{(1,1):(3,-2,15),(2,2):(5,-68,81)}),
        (cert.P1,{}),
        (cert.Node(5,-68,81,1,(11,),(16,)),{}),
    ])
    run_case(1738, [
        (cert.Node(0,0,1,2,(2,5),(6,7)),{(1,1):(3,-2,15)}),
        (cert.Node(3,-2,15,1,(8,),(11,)),{(0,2):(6,-196,135)}),
        (cert.Node(6,-196,135,3,(12,14,16),(18,21,24)),{}),
    ])


if __name__ == "__main__":
    main()
