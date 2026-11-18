# Agent 3: sector-adapted D-free 3-adic coordinate

The D-free identity can be made into one recurrence by adapting the coordinate to the input orientation.

Let \(K=2p+3q\), and define
\[
H=\begin{cases}
K,&\text{input is left-oriented (LO/LE)},\\
K+3q,&\text{input is right-oriented (RO/RE)}.
\end{cases}
\]
Let \(\epsilon=0\) for a left-oriented input and \(\epsilon=1\) for a right-oriented input. Let \(\lambda=1\) for a left output and \(\lambda=2\) for a right output. Since
\[
K'=K+S\quad\text{on a left output},\qquad
K'+3q'=2(K+S)\quad\text{on a right output},
\]
the next state's sector-adapted coordinate satisfies the single exact identity
\[
\boxed{H'=\lambda\bigl(H-3\epsilon q+S\bigr),\qquad S=2r+c_s,}
\]
where \(c_s=4,4,8,7\) in LO, LE, RO, RE respectively.

The next state's orientation is exactly the output orientation, so the definition of \(H'\) is consistent. Also \(H\equiv K\equiv2p\pmod3\) in every sector. Thus modulo \(3\), the recurrence is
\[
H'\equiv\lambda(H+2r+c_s)\pmod3,
\]
with no \(D\) or \(q\) dependence. At higher powers, the old scale enters only as the shifted term \(3q\) on right-oriented inputs. This seems a more promising 3-adic digit-stack coordinate than \(K\) alone: the signed-drop statistic \(D\) has disappeared completely from the update of \(H\).
