# 7. Witt decomposition and \(\mathbb F_2\) Gauss sums for the \(m = 7\) trace

This section documents the closed-form Gauss-sum evaluator
`TraceOnOmega0Gauss` that powers the K-4a Phase 2 pipeline at \(m = 7\).
The implementation lives in
`extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g` and was
shipped in PR #247 (issue #236, parent #220 / #187). The section is
self-contained: a strong mathematician acquainted with finite group
cohomology and \(\mathbb F_2\)-linear algebra should be able to follow
it without consulting the KRR construction in detail. Numerical
benchmarks anchor the asymptotic claims; the cross-validation at
\(m = 5\) (1025/1025 conjugacy-class traces) gives the empirical
ground-truth.

The thread of the argument is: §7.1 frames the computational problem;
§7.2 reduces the trace of \(T_h\) on \(\Omega_0\) to a Gauss sum over an
affine subspace of \(\mathbb F_2^k\); §7.3 recalls the \(\mathbb F_2\)
quadratic-form background; §7.4–§7.5 carry out the Witt decomposition
and prove the closed-form Gauss-sum identity via the Arf invariant; §7.6
assembles these into a single evaluation formula; §7.7 spells out the
fast \(O(d^3)\) symplectic-basis algorithm that replaces the textbook
\(O(2^d)\) construction and is what makes the procedure feasible at
\(m = 7\); §7.8 derives the specific quadratic form
\(\varphi_h\) from KRR's closed-form intertwiner-entry formula; §7.9
states the algorithm in pseudocode; §7.10 records the per-trace cost
and the \(m = 5\) cross-validation; §7.11 lists extensions.

---

## 7.1 The problem

Fix \(m \ge 3\) and let \(G = E_+(m)\) be the real-type extraspecial
2-group. Write \(z = -I \in G\) for the central involution and
\(C := C_G(z) = G\) for its centraliser. The KRR \(z\)-twisted lattice
module is the Bakalov–Kac defect representation \(\Omega_0\) of the
finite Heisenberg group \(N = L / 2L\), and for each
\(h \in C\) the intertwiner \(T_h \in \mathrm{GL}(\Omega_0)\)
is the Schur-averaged operator (KRR eq. 4.1.5; §5.1 of the methodology
paper).

With \(d = 2^{m-1}\) the dimension of the symplectic complement of
\(N\), the space \(\Omega_0\) has a natural basis
\(\{e_{\check c} : \check c \in \mathbb F_2^d\}\) indexed by
\(\mathbb F_2\)-vectors of length \(d\). Throughout this section we
write \(k := d = 2^{m-1}\) and let \(c \in \mathbb F_2^k\) index the
basis. The dimension grows as

\[
  \dim \Omega_0 \;=\; 2^k
  \;=\;
  \begin{cases}
    16 & (m = 3,\; k = 4) \\
    65\,536 & (m = 5,\; k = 16) \\
    2^{64} \approx 1.8 \times 10^{19} & (m = 7,\; k = 64).
  \end{cases}
\]

The character-orthogonality reformulation of `trace_on_W` (issue #220,
§5.5 of the methodology paper) reduces the K-4a Phase 2 inner loop to
*one trace* \(\mathrm{Tr}(T_h \mid \Omega_0)\) per conjugacy-class
representative \(h \in C\). There are \(2^{2m} + 1\) such
representatives in \(E_+(m)\): two singletons \(\{1\}\) and \(\{z\}\)
plus \(2^{2m} - 1\) size-2 classes. So we need

\[
  N_{\mathrm{traces}}
  \;=\;
  2^{2m} + 1
  \;=\;
  \begin{cases}
    33 & (m = 3) \\
    1\,025 & (m = 5) \\
    16\,385 & (m = 7).
  \end{cases}
\]

The entry-summing formula

\[
  \mathrm{Tr}(T_h \mid \Omega_0)
  \;=\;
  \sum_{c \in \mathbb F_2^k} (T_h)_{c,\,c}
\]

is feasible at \(m = 5\): \(2^{16} = 65\,536\) diagonal entries per
trace at the optim-pipeline cost of \(\sim 20\) µs per closed-form
entry (PR #235's sparse path) is \(\sim 1.3\) s/trace, and 1025 traces
finish in \(\sim 22\) minutes. At \(m = 7\) the same calculation is
hopeless: \(2^{64}\) entries per trace at the same cost is on the
order of \(10^9\)–\(10^{10}\) seconds per trace, i.e. \(\sim 150\)
days/trace and \(\sim 13\,000\) years for the full 16-K sweep. This
section's goal is to replace the entry-sum by a closed-form
evaluation in \(\mathrm{poly}(k)\) time per trace; PR #247 lands at
\(O(k^3)\) per trace, with the full \(m = 7\) sweep completing
on the order of minutes.

---

## 7.2 Structure of the diagonal entry

Inspection of the closed-form intertwiner-entry formula
`HardCodeShortComputeInterTwineref(h, e, f, c, d, s, ...)` in
`extraspecial_orbifolds/scripts/defect_rep_minus_id_optim.g` shows
that, restricting to the diagonal case \(e = f = 0\), \(d = c\),
\(s = 0\) (the trace summand), the value of \((T_h)_{c, c}\) splits as

\[
  (T_h)_{c,\, c}
  \;=\;
  \begin{cases}
    (-1)^{\varphi_h(c)} \cdot \mathrm{base\_val}(h) & c \in M_h, \\
    0 & c \notin M_h.
  \end{cases}
  \tag{7.1}
\]

Here:

- \(M_h \subseteq \mathbb F_2^k\) is the **support**, an affine
  subspace cut out by *linear* constraints in \(c\):
  \begin{itemize}
    \item the *feasibility* constraint
      \(F_{\mathrm{mat}} \cdot c^\top \;=\; 0\) where
      \(F_{\mathrm{mat}}\) is derived from the row-reduction of the
      KRR matrix \(\Pi(h)\) (this encodes "the system
      \(x \cdot \Pi(h) = (c, c)\) has a solution \(x\)");
    \item the *radical-match* constraint
      \(\mathrm{BT}_{\mathrm{rad}} \cdot c^\top \;=\; t_{\mathrm{rad}}\)
      where \(\mathrm{BT}_{\mathrm{rad}}\) and the inhomogeneous target
      \(t_{\mathrm{rad}}\) come from the \(\sigma_2\)-radical of the
      shift-and-target structure of KRR §4.2.
  \end{itemize}
  Concretely, \(M_h\) is the solution set of the joint linear system
  \([F_{\mathrm{mat}};\, \mathrm{BT}_{\mathrm{rad}}] \cdot c^\top
  = [0;\, t_{\mathrm{rad}}]\); if the system is inconsistent, then
  \(M_h = \emptyset\) and \(\mathrm{Tr}(T_h \mid \Omega_0) = 0\).

- \(\varphi_h : \mathbb F_2^k \to \mathbb F_2\) is a *purely
  quadratic* function in \(c\): no linear part, no constant. This is
  verified by direct inspection — the formulae for
  \(\gamma_{\mathrm{const}}(c)\) and \(\mathrm{hpair}(c)\) in the
  optim-pipeline diagonal-entry routine evaluate to \(0\) at \(c = 0\),
  and each summand is bilinear or quadratic in \(c\) with no
  free linear term once \(e, f, s\) are zero. The form \(\varphi_h\)
  has a specific decomposition \(\varphi_h = \gamma + \mathrm{hpair}\)
  whose two pieces have separate provenances (the
  Mhh-quadratic + cross-pair part of \(\gamma\) and the
  symplectic-pair quadratic of \(\mathrm{hpair}\)). The matrix
  representation of \(\varphi_h\) is the \(k \times k\) form
  \(Q \in M_{k \times k}(\mathbb F_2)\) built by `_BuildGaussCtx`
  (see §7.8).

- \(\mathrm{base\_val}(h) = 2^{\mathrm{kerLen} - \mathrm{dimND}}\) is a
  positive power of 2 depending on \(h\), with \(\mathrm{kerLen}\) the
  rank of the kernel block and \(\mathrm{dimND}\) the non-degenerate
  part of the symplectic-shift datum (§7.8). Crucially,
  \(\mathrm{base\_val}\) does not depend on \(c\).

With (7.1) in hand the trace reduces to a Gauss sum:

\[
  \mathrm{Tr}(T_h \mid \Omega_0)
  \;=\;
  \mathrm{base\_val}(h) \cdot
  \sum_{c \in M_h} (-1)^{\varphi_h(c)}.
  \tag{7.2}
\]

The right-hand sum is an *affine quadratic Gauss sum over
\(\mathbb F_2\)*, of a kind that admits a closed form. The next four
subsections establish the closed form.

---

## 7.3 \(\mathbb F_2\) quadratic forms

We collect the standard background; see [AM04, §III.5] or
[O'Meara, Ch. VI] for a full development.

A **quadratic form** on \(V = \mathbb F_2^n\) is a function
\(Q : V \to \mathbb F_2\) satisfying
\(Q(0) = 0\) and such that the polarisation
\[
  B(u, v) \;:=\; Q(u + v) + Q(u) + Q(v)
\]
is \(\mathbb F_2\)-bilinear. \(B\) is *alternating*: \(B(v, v) = Q(2v) +
2 Q(v) = 0\) since characteristic 2. The pair \((V, Q)\) determines
both \(Q\) and \(B\). Note the asymmetry from odd characteristic:
\(Q\) is *not* recoverable from \(B\) alone — over \(\mathbb F_2\) the
linear-in-each-variable part of \(Q\) lifts off the symmetric
bilinear part \(B\).

In matrix form, \(Q\) is encoded by a \(k \times k\) matrix
\(M_Q \in M_{k \times k}(\mathbb F_2)\) with
\[
  Q(c) \;=\; c\, M_Q\, c^\top \pmod 2,
\]
where \(c\) is a row vector. The on-diagonal entries
\((M_Q)_{i,i}\) carry the linear coefficient of \(c_i\) (because
\(c_i^2 = c_i\) in \(\mathbb F_2\)). The associated bilinear form is
\(B = M_Q + M_Q^\top\) with the diagonal zeroed; this convention is
what `_F2_QuadGaussSum` implements.

The **radical** of \(B\) is
\[
  \mathrm{Rad}(B) \;:=\;
  \{v \in V \,:\, B(v, w) = 0 \;\forall\, w \in V\}.
\]
On \(\mathrm{Rad}(B)\), the polarisation identity gives
\(Q(u + v) = Q(u) + Q(v)\) for \(u \in \mathrm{Rad}(B)\), \(v \in V\),
so the restriction \(Q|_{\mathrm{Rad}(B)}\) is
\(\mathbb F_2\)-**linear** — a functional, equivalently an element of
\(\mathrm{Rad}(B)^*\). The quotient \(V / \mathrm{Rad}(B)\) carries a
non-degenerate alternating bilinear form induced by \(B\); since the
form is non-degenerate alternating in characteristic 2, the dimension
of \(V / \mathrm{Rad}(B)\) is *even*, say \(2 n_{\mathrm{nd}}\).

A **symplectic basis** of \(V / \mathrm{Rad}(B)\) is a basis
\((\alpha_1, \dots, \alpha_{n_{\mathrm{nd}}}, \beta_1, \dots,
\beta_{n_{\mathrm{nd}}})\) such that
\[
  B(\alpha_i,\, \beta_j) = \delta_{ij},
  \qquad
  B(\alpha_i,\, \alpha_j) = B(\beta_i,\, \beta_j) = 0.
\]
Existence is standard (Witt's theorem / Gram–Schmidt over
\(\mathbb F_2\)).

---

## 7.4 Witt decomposition

The decomposition \(Q = Q_{\mathrm{rad}} \oplus Q_{\mathrm{nd}}\), with
\(Q_{\mathrm{rad}}\) on \(\mathrm{Rad}(B)\) and \(Q_{\mathrm{nd}}\) on
the non-degenerate quotient, drives the Gauss-sum factorisation. Pick
any complementary subspace \(W \subset V\) of \(\mathrm{Rad}(B)\), so
\(V = \mathrm{Rad}(B) \oplus W\) (as \(\mathbb F_2\)-spaces). For
\(r + w \in V\) with \(r \in \mathrm{Rad}(B)\) and \(w \in W\),
\[
  Q(r + w)
  \;=\;
  Q(r) + Q(w) + B(r, w)
  \;=\;
  Q(r) + Q(w),
\]
because \(B(r, w) = 0\) for \(r \in \mathrm{Rad}(B)\). So \(Q\)
*splits* as a sum of \(Q|_{\mathrm{Rad}(B)}\) (linear) and \(Q|_W\)
(non-degenerate quadratic):

\[
  \sum_{v \in V} (-1)^{Q(v)}
  \;=\;
  \Bigl( \sum_{r \in \mathrm{Rad}(B)} (-1)^{Q_{\mathrm{rad}}(r)} \Bigr)
  \;\cdot\;
  \Bigl( \sum_{w \in W} (-1)^{Q_{\mathrm{nd}}(w)} \Bigr).
  \tag{7.3}
\]

The first factor is a Gauss sum of a *linear* form on
\(\mathrm{Rad}(B)\). For any non-zero linear functional
\(\ell : \mathbb F_2^r \to \mathbb F_2\), the sum
\(\sum_{x} (-1)^{\ell(x)}\) is \(0\) (half the inputs go to each
sign). For the zero functional the sum is \(2^r\). So

\[
  \sum_{r \in \mathrm{Rad}(B)} (-1)^{Q_{\mathrm{rad}}(r)}
  \;=\;
  \begin{cases}
    2^{|\mathrm{Rad}(B)|} & Q_{\mathrm{rad}} \equiv 0, \\
    0 & Q_{\mathrm{rad}} \not\equiv 0.
  \end{cases}
\]

The first case is detected operationally by evaluating \(Q\) on each
basis vector of \(\mathrm{Rad}(B)\); if any \(Q(b_i) = 1\), the entire
sum vanishes.

The second factor — the Gauss sum of the non-degenerate part — is
controlled by the Arf invariant.

---

## 7.5 The Arf invariant and the non-degenerate Gauss sum

For a non-degenerate \(\mathbb F_2\) quadratic form \(Q_{\mathrm{nd}}\)
on a space of dimension \(2 n_{\mathrm{nd}}\), pick a symplectic basis
\((\alpha_1, \dots, \alpha_{n_{\mathrm{nd}}}, \beta_1, \dots,
\beta_{n_{\mathrm{nd}}})\) and define
\[
  \mathrm{Arf}(Q_{\mathrm{nd}})
  \;:=\;
  \sum_{i=1}^{n_{\mathrm{nd}}} Q_{\mathrm{nd}}(\alpha_i) \cdot Q_{\mathrm{nd}}(\beta_i)
  \pmod 2.
\]
The content of Arf's theorem is that this invariant is *independent of
the choice of symplectic basis* and is the *complete* invariant of
\(Q_{\mathrm{nd}}\) up to isometry [AM04, Thm III.5.4; O'Meara, §94].
Two non-degenerate \(\mathbb F_2\) quadratic forms of the same
dimension are isometric iff they have the same Arf invariant.

The Gauss sum closed form follows from a hyperbolic decomposition. A
non-degenerate \(\mathbb F_2\) quadratic form of dimension 2 is one of
two isometry classes:

- \(\mathbb H_0\): \(Q(\alpha, \beta) = \alpha \beta\), with
  \(\mathrm{Arf} = 0\). The four values \((Q(0), Q(\alpha), Q(\beta),
  Q(\alpha + \beta)) = (0, 0, 0, 1)\); Gauss sum
  \(3 - 1 = 2\).
- \(\mathbb H_1\): \(Q(\alpha, \beta) = \alpha^2 + \alpha\beta + \beta^2
  = \alpha + \alpha\beta + \beta\) (over \(\mathbb F_2\)),
  with \(\mathrm{Arf} = 1\). Values \((0, 1, 1, 1)\); Gauss sum
  \(1 - 3 = -2\).

In both cases the Gauss sum is \((-1)^{\mathrm{Arf}} \cdot 2\). The
general non-degenerate form decomposes as an orthogonal sum of
\(n_{\mathrm{nd}}\) two-dimensional pieces (this is the symplectic-basis
construction), and Arf is additive over orthogonal sums. The Gauss sum
multiplies likewise:

\[
  \sum_{w \in W} (-1)^{Q_{\mathrm{nd}}(w)}
  \;=\;
  (-1)^{\mathrm{Arf}(Q_{\mathrm{nd}})}
  \cdot 2^{n_{\mathrm{nd}}}.
  \tag{7.4}
\]

This is the foundational identity. The Arf invariant gives the sign;
the dimension gives the magnitude.

A clean self-contained derivation of (7.4) using only Gauss sums and
the symplectic structure: pick any symplectic basis. Each hyperbolic
plane contributes a factor of \(\pm 2\), with the sign determined by
the Arf bit \(Q(\alpha_i) Q(\beta_i)\) of that plane (by the rank-2
case). Multiplying \(n_{\mathrm{nd}}\) factors gives \((-1)^{\sum_i
Q(\alpha_i) Q(\beta_i)} \cdot 2^{n_{\mathrm{nd}}} = (-1)^{\mathrm{Arf}}
\cdot 2^{n_{\mathrm{nd}}}\). Arf's basis-independence guarantees this
does not depend on the specific symplectic basis chosen.

---

## 7.6 The closed-form Gauss sum on an affine quadratic form

Combining (7.3) and (7.4) yields the general formula. Let \(M\) be an
affine subspace of \(\mathbb F_2^n\), say \(M = c_0 + W\) where
\(W \subseteq \mathbb F_2^n\) is a linear subspace and \(c_0 \in M\) is
any particular solution. Let \(\Phi : \mathbb F_2^n \to \mathbb F_2\)
be a quadratic form (no linear or constant component required —
\(c \mapsto c\, Q\, c^\top\) for some \(Q\)). Then

\[
  \sum_{c \in M} (-1)^{\Phi(c)}
  \;=\;
  (-1)^{\Phi(c_0)}
  \cdot
  \sum_{y \in \mathbb F_2^{\dim W}} (-1)^{\Phi_\psi(y)},
\]

where \(\Phi_\psi : \mathbb F_2^{\dim W} \to \mathbb F_2\) is the
*pullback form* of \(\Phi\) along the affine substitution
\(c = c_0 + y \cdot B_W\), with \(B_W\) a \(\dim W \times n\) matrix
whose rows form a basis of \(W\). Concretely

\[
  \Phi(c_0 + y B_W)
  \;=\;
  \Phi(c_0) + B_\Phi(c_0,\, y B_W) + \Phi(y B_W)
  \quad \text{(over } \mathbb F_2),
\]

where \(B_\Phi(u, v) = u (Q + Q^\top) v^\top\) is the bilinear form
associated to \(\Phi\). The cross term is *linear* in \(y\), of the
form \(L_y \cdot y^\top\) with \(L_y = c_0 (Q + Q^\top) B_W^\top\);
the quadratic part is \(y \cdot B_W Q B_W^\top \cdot y^\top\). Over
\(\mathbb F_2\), a linear-in-\(y_i\) term \(L_y[i] \cdot y_i\) is
equal to \(L_y[i] \cdot y_i^2\), which is the same as adding \(L_y[i]\)
to the \((i, i)\)-diagonal of the quadratic matrix. So
\[
  \Phi_\psi(y)
  \;=\;
  y \cdot Q_\psi \cdot y^\top
  \quad
  \text{with}
  \quad
  Q_\psi
  \;=\;
  B_W Q B_W^\top + \mathrm{diag}(L_y),
\]
where \(\mathrm{diag}(L_y)\) adds the linear-in-\(y\) coefficients to
the diagonal of the matrix.

After this reduction, applying (7.3) + (7.4) to \(Q_\psi\) gives the
closed-form trace. Writing \(\mathrm{Rad}_\psi := \mathrm{Rad}(B_\psi)\)
for the radical of the polarisation of \(Q_\psi\) and
\(n_{\mathrm{nd}, \psi} := \dim W / 2 - |\mathrm{Rad}_\psi| / 2\)
for the half-dimension of its non-degenerate part:

\[
  \boxed{
  \sum_{c \in M} (-1)^{\Phi(c)}
  \;=\;
  \begin{cases}
    0
    & Q_\psi|_{\mathrm{Rad}_\psi} \neq 0, \\[4pt]
    (-1)^{\Phi(c_0)} \cdot (-1)^{\mathrm{Arf}(Q_{\psi,\mathrm{nd}})}
    \cdot 2^{|\mathrm{Rad}_\psi| + n_{\mathrm{nd}, \psi}}
    & Q_\psi|_{\mathrm{Rad}_\psi} = 0.
  \end{cases}
  }
\]

For the empty case \(M = \emptyset\), the sum is zero by convention.
The signed-magnitude is fully determined by the three integers
\(\Phi(c_0)\), \(\mathrm{Arf}(Q_{\psi, \mathrm{nd}})\),
\(|\mathrm{Rad}_\psi|\), and the parity check
\(Q_\psi|_{\mathrm{Rad}_\psi} \stackrel{?}{=} 0\) — none of which
requires summing over \(\mathbb F_2^{\dim W}\).

---

## 7.7 The fast symplectic basis algorithm

The standard textbook construction of a symplectic basis is via the
recursion: pick any non-zero \(\alpha \in V\); find \(\beta\) with
\(B(\alpha, \beta) = 1\); let \(V' = \langle \alpha, \beta
\rangle^\perp\); recurse on \(V'\). The bottleneck is "find \(\beta\)
with \(B(\alpha, \beta) = 1\)". The textbook routine
`SymplecticBasisF2` (and similarly `FindHyperBolicPair`) in
`qforms_f2.g` enumerates over \(\mathbb F_2^{\dim V}\) to find such a
\(\beta\); the inner enumeration is \(O(2^{\dim V})\). At \(m = 5\)
(\(k = 16\)), the enumeration is \(2^{16} = 65\,536\) — fast. At
\(m = 7\) (\(k = 64\)), it is \(2^{64} \approx 10^{19}\) — wholly
infeasible.

PR #247 replaces this with a Gauss-Jordan-style algorithm
`_F2_FastSymplecticBasis` (file
`krr_spectral_characters_sparse.g`, lines 715–798) that runs in
\(O(d^3)\) for \(d \times d\) inputs:

1. Maintain a "current basis" \(b_1, \dots, b_d\) of the ambient
   \(\mathbb F_2^d\) along with the bilinear-form matrix \(B'\) in this
   basis. Initially the basis is the standard basis and \(B' = B_0\).
2. Find any pair \((i, j)\) of *active* indices (slots not yet paired
   off) with \(B'[i][j] = 1\). This is a linear scan over the \(d^2\)
   matrix entries — \(O(d^2)\). Non-degeneracy of \(B_0\) restricted to
   the non-radical part guarantees such a pair exists at each step.
3. Take \(b_i\) and \(b_j\) as the next symplectic pair
   \((\alpha, \beta)\); mark slots \(i, j\) as done.
4. For every other index \(l \neq i, j\), update \(b_l \to b_l +
   B'[l][j] \cdot b_i + B'[l][i] \cdot b_j\). This makes \(b_l\)
   orthogonal to both \(\alpha\) and \(\beta\) under \(B_0\), so the
   remaining symplectic structure decouples on the orthogonal
   complement. The update is \(O(d)\) per index, \(O(d^2)\) total.
5. Update \(B'[l][m]\) accordingly. \(O(d^2)\) total.
6. Recurse on the remaining active indices (now \(d - 2\) of them).

Each iteration is \(O(d^2)\); there are \(d/2\) iterations; total
cost \(O(d^3)\).

At \(d = 64\) (the \(m = 7\) case), \(d^3 \approx 2.6 \times 10^5\) —
microseconds. The same operation under the textbook \(O(2^d)\) routine
would be \(\approx 10^{19}\) ops — wholly infeasible.

This is the single substantive algorithmic improvement that makes the
\(m = 7\) trace tractable; everything else in the pipeline is
polynomial in \(k\) by construction.

---

## 7.8 The KRR application: building \(Q_h\) from \(h\)

The per-\(h\) context built by `_BuildGaussCtx(h, m)` (file
`krr_spectral_characters_sparse.g`, lines 587–685) extracts the four
ingredients of (7.1) from KRR's optim-pipeline data structures. We
trace through the derivation; the reader following along will benefit
from cross-referencing `HardCodeShortComputeInterTwineref` in
`defect_rep_minus_id_optim.g`.

### 7.8.1 The feasibility matrix \(F_{\mathrm{mat}}\)

The closed-form entry routine first solves
\(x \cdot \Pi(h) = (c, c)\) for \(x \in \mathbb F_2^n\), where
\(\Pi(h) := \mathrm{BigPi}(h)\) is a fixed \(n \times n\)
\(\mathbb F_2\) matrix associated to \(h\). For diagonal entries
\((d, c) = (c, c)\), the target vector is the *symmetrised* row
\((c, c) \in \mathbb F_2^{2k} = \mathbb F_2^n\). The system has a
solution iff the target lies in the image of the (left)
multiplication by \(\Pi(h)^\top\), i.e. iff
\(\Pi(h)^\top\) row-reduction leaves a *feasibility witness*
\(F'_{\mathrm{mat}}\) with \(F'_{\mathrm{mat}} \cdot (c, c)^\top = 0\).

`_BuildTraceCtx` row-reduces \(\Pi(h)^\top\) once at context-build
time and stores both the pivot map (`solveMap`) for the particular
solution \(x\) and the feasibility constraint
(`feasMat`). At the Gauss-sum context level we collapse
the redundancy in the symmetric target: since
\(\mathrm{feasMat}[r] \cdot (c, c)^\top = \sum_i (\mathrm{feasMat}[r][i]
+ \mathrm{feasMat}[r][k + i]) \cdot c[i]\),
we define \(F_{\mathrm{mat}}\) as the \((n - \mathrm{rank}) \times k\)
matrix obtained by adding the two halves of \(\mathrm{feasMat}\)
columnwise.

### 7.8.2 The radical-match constraint \(\mathrm{BT}_{\mathrm{rad}}\)

After the linear solve, the closed-form entry routine then evaluates a
secondary linear functional \(\beta : \mathbb F_2^k \to
\mathbb F_2^{\mathrm{kerLen}}\) and checks whether
\(\tilde\beta := \beta \cdot \mathrm{Sh}^\top\) matches a target
\(t \in \mathbb F_2^{\mathrm{kerLen}}\) on the *radical block*
(the first \(\mathrm{radLen} = \dim_{\mathrm{An}} + \dim_{\mathrm{Sp}}\)
coordinates).

In Gauss-sum coordinates, \(\beta(c) = c \cdot L_{\mathrm{mat}}\) where
\(L_{\mathrm{mat}}\) is computed from \(X_{\mathrm{mat}} \cdot
M_{hh,\mathrm{sym}} \cdot A^\top + \mathrm{ic}_{\mathrm{mat}}
\cdot R^\top \cdot H^\top \cdot A^\top\) (line 638 ff.). Composing with
\(\mathrm{Sh}^\top\) gives \(\mathrm{BT}_{\mathrm{mat}} :=
L_{\mathrm{mat}} \cdot \mathrm{Sh}^\top\). The radical-match condition
is the requirement that the first \(\mathrm{radLen}\) coordinates of
\(\tilde\beta(c)\) equal the corresponding entries of \(t\):
\[
  \mathrm{BT}_{\mathrm{rad}} \cdot c^\top
  \;=\; t_{\mathrm{rad}}
  \quad
  \text{with}
  \quad
  \mathrm{BT}_{\mathrm{rad}}[r][\,\cdot\,] = \mathrm{BT}_{\mathrm{mat}}[\,\cdot\,][r],
  \;\;
  t_{\mathrm{rad}} = t[1..\mathrm{radLen}].
\]

### 7.8.3 The quadratic form \(Q\)

The exponent in the sign \((-1)^{\varphi_h(c)}\) decomposes as

\[
  \varphi_h(c)
  \;=\;
  \gamma_{\mathrm{const}}(c) + \mathrm{hpair}(c)
  \pmod 2.
\]

The first piece \(\gamma_{\mathrm{const}}\) has two further parts:
\(x(c) \cdot M_{hh} \cdot x(c)^\top\) (a quadratic in the lifted
solution \(x(c)\)) and \(x(c) \cdot H \cdot R \cdot \mathrm{ic}(c)^\top\)
(a bilinear cross term). Since \(x(c)\) is linear in \(c\) — it is the
particular solution of \(x \cdot \Pi(h) = (c, c)\), which is
\(x(c) = c \cdot X_{\mathrm{mat}}\) for an explicit
\(k \times n\) matrix \(X_{\mathrm{mat}}\) — and \(\mathrm{ic}(c) = (0,
c) = c \cdot \mathrm{ic}_{\mathrm{mat}}\) is also linear in \(c\), both
parts are *quadratic* in \(c\). Concretely
\[
  Q_1 \;:=\; X_{\mathrm{mat}} \cdot M_{hh} \cdot X_{\mathrm{mat}}^\top
  \quad (k \times k),
  \qquad
  Q_2 \;:=\; X_{\mathrm{mat}} \cdot H \cdot R \cdot \mathrm{ic}_{\mathrm{mat}}^\top
  \quad (k \times k).
\]

The second piece \(\mathrm{hpair}(c)\) is a sum
\(\sum_{i=1}^{\dim \mathrm{ND}/2} \tilde\beta(c)[r + 2i - 1] \cdot
\tilde\beta(c)[r + 2i]\) of products of pairs of entries of the
linear form \(\tilde\beta\), with \(r = \mathrm{radLen}\). Each entry
of \(\tilde\beta\) is linear in \(c\); each product is therefore
quadratic; summing gives
\[
  Q_3 \;:=\;
  \sum_{i=1}^{\dim \mathrm{ND}/2}
  \mathrm{BT}_{\mathrm{odd}, i}\, \mathrm{BT}_{\mathrm{even}, i}^\top
  \quad (k \times k),
\]
where \(\mathrm{BT}_{\mathrm{odd}, i}\) and
\(\mathrm{BT}_{\mathrm{even}, i}\) are length-\(k\) vectors picked off
from the appropriate columns of \(\mathrm{BT}_{\mathrm{mat}}\).

The total quadratic form is
\[
  Q \;:=\; Q_1 + Q_2 + Q_3 \pmod 2 \quad (k \times k).
\]

This \(Q\) is the matrix `ctx.Q` stored by `_BuildGaussCtx`. The form
is in general neither symmetric nor purely off-diagonal — both kinds
of contribution arise from `_BuildTraceCtx`'s linear/cross structure.
The polarisation
\(Q + Q^\top\) (with diagonal zeroed) is the associated alternating
bilinear form on \(\mathbb F_2^k\).

### 7.8.4 The base value

The factor \(\mathrm{base\_val} = 2^{\mathrm{kerLen} - \mathrm{dimND}}\)
is read off from the dimensions of the kernel block
(\(\mathrm{kerLen} = \dim A\)) and the non-degenerate part of the
shift datum (\(\mathrm{dimND}\)), both fixed by \(h\) and independent
of \(c\).

---

## 7.9 Algorithm summary

The complete `TraceOnOmega0Gauss(h, m)` is six steps. The first three
are the per-\(h\) context build, cached so subsequent traces against
the same \(h\) are free; the last three are the per-call evaluation.

```text
TraceOnOmega0Gauss(h, m):

  # ---- Per-h context (cached) ----
  1. Build _BuildTraceCtx(h, m): F_2 row-reduce Pi(h), produce
     feasMat (n - rank) x n and solveMap (rank x n).
     Cost: O(n^3) with n = 2^m.

  2. Build _BuildGaussCtx(h, m):
     a. Collapse symmetric halves: F_mat (rows x k).
     b. Build L_mat = X_mat * Mhh_sym * A^T
                    + ic_mat * R^T * H^T * A^T  (k x kerLen).
     c. Build BT_mat = L_mat * Sh^T  (k x kerLen).
     d. Build BT_radmat = BT_mat[:, 1..radLen]^T  (radLen x k),
              t_rad     = t[1..radLen].
     e. Build Q = Q1 + Q2 + Q3 (k x k).
     f. base_val = 2^(kerLen - dimND).
     Cost: O(k^2 n).

  # ---- Per-call evaluation ----
  3. Affine solve: [F_mat; BT_radmat] * c^T = [0; t_rad].
     Returns (c_0, B_W) with B_W spanning the kernel.
     If infeasible: return 0.
     Cost: O(k^3) F_2 row reduction.

  4. Substitute c = c_0 + y * B_W in phi:
     Q_psi = B_W * Q * B_W^T + diag(L_y),
     L_y   = c_0 * (Q + Q^T) * B_W^T.
     Compute phi(c_0) = c_0 * Q * c_0^T mod 2.
     Cost: O(k^2 * dim W).

  5. Witt-decompose Q_psi via _F2_QuadGaussSum:
     a. Bilinear form B_psi = Q_psi + Q_psi^T with zero diagonal.
     b. Radical Rad = nullspace(B_psi); dimRad = |Rad|.
     c. Check Q_psi|Rad = 0; else return 0.
     d. Complement Bn of Rad; B|<Bn> non-deg.
     e. Symplectic basis (alpha_i, beta_i) of B|<Bn> via
        _F2_FastSymplecticBasis (O(d^3)).
     f. Arf = sum_i Q_psi(alpha_i) Q_psi(beta_i) mod 2.
     g. Gauss sum: (-1)^Arf * 2^(dimRad + dim Bn / 2).
     Cost: O((dim W)^3).

  6. Return base_val * (-1)^{phi(c_0)} * Gauss sum.
```

Per-trace asymptotic cost is dominated by step 1 (the
\(O(n^3) = O(8^m)\) F_2 row reduction). At \(m = 7\), \(n = 128\),
\(n^3 \approx 2 \times 10^6\) ops — \(\sim 10\) ms per trace. For
16\,385 traces, the total is on the order of minutes.

---

## 7.10 Cost and validation

### 7.10.1 Cost summary

| \(m\) | \(k = 2^{m-1}\) | \(n = 2^m\) | \(\dim \Omega_0\) | Entry-sum per trace | Gauss-sum per trace | Total Gauss sweep |
| ---: | ---: | ---: | ---: | --- | --- | --- |
| 3 | 4 | 8 | 16 | \(< 1\) ms | \(< 1\) ms | \(\sim\) 30 ms |
| 5 | 16 | 32 | 65\,536 | \(\sim 1.3\) s | \(\sim 1\) ms | \(\sim 1\) s |
| 7 | 64 | 128 | \(2^{64}\) | \(\sim 150\) days | \(\sim 10\) ms | \(\sim 1\)–10 min |

The dispatcher `TraceOnOmega0(h, m)` (lines 970–987 of
`krr_spectral_characters_sparse.g`) selects the path:
\(m \le 5 \to\) entry-sum (`TraceOnOmega0Batch`);
\(m \ge 7 \to\) Gauss-sum (`TraceOnOmega0Gauss`). At \(m = 5\) the
entry-sum is fast enough that the closed-form Gauss sum buys no
asymptotic advantage in production; we still use the Gauss-sum path
for *cross-validation* (see §7.10.2).

### 7.10.2 \(m = 5\) cross-validation

The acceptance test for PR #247 (file
`extraspecial_orbifolds/scripts/tests/test_krr_gauss_sum.g`, Test 1)
runs `TraceOnOmega0Gauss(h, 5)` and `TraceOnOmega0Batch(h, 5)` on every
conjugacy-class representative \(h\) of \(C_G(z) = E_+(5)\) and verifies
exact integer equality. The test confirms **1025/1025 PASS** on the
\(m = 5\) centraliser class set. Wall time is several minutes for the
batch baseline (the Gauss-sum path is sub-second). Test 0 runs the
same cross-check at \(m = 3\) (33 classes, instant) and Test 2 sanity-
checks the \(m = 7\) build:

- Sum of \(\mathrm{mult}_\chi\) over irreps \(\chi\) of
  \(C_G(z) = E_+(7)\) equals \(\dim \Omega_0 = 2^{64}\) on the central
  conjugacy class (verifying the orthogonality formula is self-
  consistent and that the trace data integrates correctly).
- All \(\mathrm{mult}_\chi\) are non-negative integers (a necessary
  condition for an actual representation).
- `trace_on_W(central, 1, identity) = mult * chi.dim` (smoke-test of
  the integration with the rest of the spectral-characters pipeline).

At \(m = 5\), the agreement is exact for *every* class. This is a
strong validation: the Gauss-sum machinery and the entry-sum
implementation share no critical-path code (`_BuildGaussCtx` and
`_BuildTraceCtx` share the row reduction of \(\Pi(h)\), but the
quadratic-form construction and the trace evaluation are completely
independent). Any bug in the Witt decomposition, the Arf-invariant
computation, the affine reduction, or the symplectic-basis routine
would manifest as a per-class disagreement.

### 7.10.3 What the cross-validation does *not* check

A residual concern is that the entry-sum and Gauss-sum paths both
inherit the algebraic content of `HardCodeShortComputeInterTwineref`
(the closed-form expression for \((T_h)_{c, c}\)). A bug in *that*
expression — i.e. in the underlying KRR optim-pipeline derivation —
would not be caught by 1025/1025 agreement, since both paths would be
wrong in the same way. The cross-validation against the dense
materialised \(T_h\) at \(m = 3\) (K-3 anchor of §8.1; full
\(S\,+\,T\) anchor of issue #211 / PR #222) is the relevant check
upstream: at \(m = 3\) the dense \(2^4 \times 2^4 = 16 \times 16\)
matrix is built directly and the central-row + diagonal entries
match byte-for-byte. This anchors the optim-pipeline closed form at
\(m = 3\); the present Gauss-sum machinery propagates that
correctness to \(m = 5, 7\) under the assumption that the optim
formula extends without modification to higher \(m\), which is the
content of KRR's §4.4.

---

## 7.11 Open questions and extensions

### 7.11.1 Generalising to other 2-groups

The Witt-decomposition framework of §7.4–§7.6 applies to *any*
\(\mathbb F_2\) quadratic Gauss sum on an affine subspace of
\(\mathbb F_2^n\), regardless of how \(Q\), \(M\), and the
base-value factor arise. The K-4a application uses it on a quadratic
form derived from KRR's lattice intertwiner formula, but the same
machinery would apply to any 2-group orbifold whose diagonal-entry
formula reduces to the structure of (7.1). Examples plausibly within
reach: BRW-twisted modules for the wider class of Clifford-collineation
groups (NRS01); other extraspecial-2 lattice orbifolds (e.g. real-type
vs. complex-type signatures).

### 7.11.2 Scaling to \(m \ge 9\)

The per-trace cost is \(O(k^3) = O(8^{m-1})\); the number of traces is
\(O(4^m)\). Total cost scales as \(O(32^m / m)\) (after accounting for
class structure). At \(m = 9\) this is \(\sim 10^4\)–\(10^5\) times the
\(m = 7\) cost, i.e. hours-to-days; at \(m = 11\) it is millions of
times more, i.e. infeasible without further reductions. The
asymptotic ceiling for the present framework is \(m = 9\) or so on
contemporary hardware; \(m = 11\) and beyond would require a
substantially different approach (e.g. exploiting the BRW-orbit
structure of conjugacy classes to reduce the trace sweep itself, not
just the per-trace cost).

### 7.11.3 Cyclotomic generalisations

The CT case of KRR's setup makes every diagonal entry \(\pm\) (a power
of 2). For a hypothetical non-CT lattice orbifold — or for an analogous
construction with twisted modules at an odd prime — the diagonal
entries would involve roots of unity, e.g. \(p\)-th roots of unity at
\(p \neq 2\). The Witt decomposition extends to non-degenerate
quadratic forms over \(\mathbb F_p\) for odd \(p\) with the same
overall structure (radical + non-degenerate quotient + symplectic
basis); the Gauss sum on the non-degenerate part picks up a phase
depending on the Legendre symbol of the form's discriminant
(see [Sta12, §1.10] for the classical statement). Closed-form
evaluation remains \(\mathrm{poly}(k)\), with somewhat heavier
cyclotomic arithmetic on each step.

### 7.11.4 The \(M_h = \emptyset\) case

A subtle observation: even at \(m = 7\) it remains an *empirical*
question how often the affine system
\([F_{\mathrm{mat}}; \mathrm{BT}_{\mathrm{rad}}] \cdot c^\top
= [0;\, t_{\mathrm{rad}}]\) is inconsistent. On the \(m = 5\) sweep, a
significant fraction of \(h\) had \(M_h = \emptyset\), giving
\(\mathrm{Tr}(T_h \mid \Omega_0) = 0\) for structural reasons. The
fraction at \(m = 7\) has not been measured; if it is dominant, the
per-trace cost is reduced further (we exit at the affine-solve step,
saving the Witt-decomposition pass). This is a minor optimisation
opportunity that has not been pursued.

### 7.11.5 Joint diagonalisation as an alternative

An orthogonal approach to the spectral-character problem is to
*joint-diagonalise* the family \(\{T_h : h \in C\}\) (commuting
projective operators on \(\Omega_0\)) and read off the irrep content
directly from the eigenvalue support. This is what the *dense* path
of `BuildKRRSpectralCharacters` does at \(m = 3\) (PR #218). At
\(m = 5, 7\) the matrix \(T_h\) is too large to materialise; the
trace-only path of PR #235 + the present Gauss-sum machinery sidesteps
this by extracting the same information from a class function.
However, the trace-only path *cannot* directly produce the
eigenvectors — only the multiplicities. For applications that need
the actual projections (rather than just the spectral character),
some form of distillation from the traces back to an
eigenvector-level data structure would be required. This is presently
out of scope for K-4a Phase 2 (which only consumes the
spectral characters), but it may matter for downstream analyses of
the modular data.

### 7.11.6 Reproducibility note

The implementation has no external dependencies beyond GAP and HAP.
The fast symplectic-basis algorithm of §7.7 is folklore (it is the
\(\mathbb F_2\) version of standard Gauss-elimination-style
symplectic-form reduction); we are not aware of a specific reference
that states it in the form above with the explicit complexity
bound. The Arf-invariant theorem dates to Arf 1941 (cited via
[AM04, Thm III.5.4]); the Gauss-sum closed form (7.4) is standard
([O'Meara, Ch. VI]; cf. [Sta12, §1.10] for the classical case). The
specific reduction in §7.2 of KRR's diagonal-entry formula to (7.1)
is, to our knowledge, original to PR #247.

---

### References for this section

- [AM04] Adem, Milgram, *Cohomology of Finite Groups* (2nd ed.,
  Springer 2004), §III.5 (\(\mathbb F_2\) quadratic forms; Arf
  invariant) and §IV.2 (extraspecial 2-groups).
- [O'Meara] O'Meara, *Introduction to Quadratic Forms* (Springer
  1973), Ch. VI (Witt decomposition over general fields including
  characteristic 2).
- [Sta12] Stanley, *Enumerative Combinatorics, Vol. 1* (2nd ed.,
  Cambridge 2012), §1.10 (Gauss sums and \(q\)-binomial identities).
- [TY80] Tezuka, Yagita, on the mod-2 cohomology of extraspecial
  2-groups (cited via [AM04, §IV.4–§IV.5]).
- [NRS01] Nebe, Rains, Sloane, "The invariants of the Clifford
  groups" (cited as [NRS01] in the methodology paper for the BRW
  group structure).
- [KRR24] Keller, Roberts, Roberts (2024), arXiv:2411.13646.
  §4.1–§4.4 is the source of the intertwiner construction and the CT
  case.
- [PR #247] Implementation of `TraceOnOmega0Gauss`,
  `_F2_FastSymplecticBasis`, `_F2_QuadGaussSum`, `_BuildGaussCtx`,
  `_F2_AffineSolveCols`; cross-validation at \(m = 5\).
- [issue #236] Specification of the \(m = 7\) Gauss-sum requirement;
  closed by PR #247.
- [issue #220] Parent issue: sparse `trace_on_W` reformulation.
- [PR #235] Sparse \(m = 5\) entry-summing path; provides the
  ground-truth `TraceOnOmega0Batch` against which the Gauss-sum
  variant is cross-validated.
- [PR #222] Full \(S + T\) anchor at \(m = 3\); anchors the optim-
  pipeline closed-form expression for \((T_h)_{c, c}\) upstream of
  this section.
