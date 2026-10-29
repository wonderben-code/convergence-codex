#!/usr/bin/env python3
"""R5 — the Born circle: Tree GNS -> a qudit's Hilbert space -> Chain Theory's wash -> the Born readout.

Pre-registered (The Refined Gaps v1, §6.3): the chain closes with nothing used twice and nothing cited.
Kill-condition: a second import in Chain Theory's premises ("the pair as a ray", or the twirl's invariance) that the
Tree's inner-product lineage does not already provide.
Chain Theory 35.1: "the twirl over the identifications is a linear channel, and the inner product of the span is the
Born readout"; "the twirl of the whole identification group has exactly one pure fixed state, the maximally entangled
pair on the common support, its amplitude the root of the Born readout."

The chain, step by step, for d = 2 and d = 3:
  (1) R8 (Lean): every matching fixes only the trace, so the state is tau = tr/d.
  (2) GNS of tau: H = L^2(M_d), <x, y> = tr(x* y)/d, cyclic vector Omega = 1. Under L^2(M_d) = C^d (x) C^d (vec),
      Omega is the maximally entangled pair; vectors are rays (x and e^{i t} x give one state): "the pair as a ray".
  (3) The matchings (unitary conjugations, the Tree's Aut lineage) act on L^2(M_d) as x -> U x U* = (U (x) conj U) vec x.
      The twirl is the average over them, i.e. the projection onto their commutant.
  (4) Twirling a vector state |x><x| leaves weight p = |<Omega, x>|^2 on the pair: the Born square.
Run: python3 -I scripts/chain_theory/r5_born_circle.py
"""
import numpy as np

rng = np.random.default_rng(5)


def run(d):
    vec = lambda X: X.reshape(-1)
    Omega = vec(np.eye(d)) / np.sqrt(d)                       # normalised GNS vector of the trace state
    # (2) Omega is maximally entangled: its reduced state is flat
    red = Omega.reshape(d, d) @ Omega.reshape(d, d).conj().T
    flat = np.allclose(red, np.eye(d) / d)
    # (3) the matchings' generators: X -> i[h, X] for Hermitian h, i.e. on vec: (h (x) 1 - 1 (x) h^T)
    gens = []
    for a in range(d):
        for b in range(d):
            for ph in (1, 1j):
                h = np.zeros((d, d), complex); h[a, b] += ph; h[b, a] += np.conj(ph)
                gens.append(np.kron(h, np.eye(d)) - np.kron(np.eye(d), h.T))
    # commutant on B(C^{d^2}): operators commuting with every generator
    N = d * d
    rows = [np.kron(g, np.eye(N)) - np.kron(np.eye(N), g.T) for g in gens]
    A = np.vstack(rows)
    _, s, vh = np.linalg.svd(A)
    null = vh[np.sum(s > 1e-9):].conj()
    comm_dim = null.shape[0]
    P_Om = np.outer(Omega, Omega.conj())
    in_comm = np.linalg.matrix_rank(np.vstack([null, P_Om.reshape(1, -1), np.eye(N).reshape(1, -1)]), tol=1e-8) == comm_dim
    # the twirl = Hilbert-Schmidt projection onto the commutant span{1, P_Om}
    B = [np.eye(N) - P_Om, P_Om]
    def twirl(rho):
        return sum(np.trace(b.conj().T @ rho) / np.trace(b.conj().T @ b) * b for b in B)
    # pure fixed states: a pure state |v><v| in the commutant must be P_Om (rank-1 elements of span{1, P_Om})
    # an element c1 (1 - P_Om) + c2 P_Om has rank 1 only if c1 = 0, because 1 - P_Om has rank d^2 - 1 > 1
    unique_pure = np.linalg.matrix_rank(np.eye(N) - P_Om, tol=1e-9) > 1
    # (4) Born square
    ok = True
    for _ in range(20):
        x = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); x = vec(x); x /= np.linalg.norm(x)
        T = twirl(np.outer(x, x.conj()))
        p = abs(np.vdot(Omega, x)) ** 2
        ok &= np.isclose(np.trace(P_Om @ T).real, p)
        ok &= np.allclose(T, p * P_Om + (1 - p) * (np.eye(N) - P_Om) / (N - 1))
        # and a phase leaves it unchanged: the state depends on the ray
        x2 = np.exp(0.7j) * x
        ok &= np.allclose(twirl(np.outer(x2, x2.conj())), T)
    return flat, comm_dim, in_comm, unique_pure, ok


print("R5 — THE BORN CIRCLE")
for d in (2, 3):
    flat, cd, inc, up, ok = run(d)
    print(f"  d = {d}: GNS vector Omega maximally entangled (flat reduced state): {flat};  commutant of the matchings has "
          f"dimension {cd}, spanned by 1 and |Omega><Omega|: {inc};")
    print(f"         unique pure fixed state = Omega: {up};  twirl(|x><x|) = p|Omega><Omega| + (1-p)(flat), p = |<Omega,x>|^2,"
          f" ray-dependent only: {ok}")
print()
print("VERDICT: the circle closes. GNS on the trace state (forced by R8) supplies the Hilbert space, the rays, and the pair")
print("itself: Chain Theory's maximally entangled pair IS the Tree's GNS vector Omega. The Tree's Aut lineage supplies the")
print("matchings, whose twirl is the projection onto span{1, |Omega><Omega|}; twirling leaves weight |<Omega, x>|^2 on the")
print("pair: the Born square. No second import is needed. The one step left is interpretive and shared with Gleason's")
print("route: reading that weight as a probability.")
