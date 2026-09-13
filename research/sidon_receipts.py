"""Erdos #39 campaign -- computational receipts.

Every number this campaign quotes comes from this script.  Nothing here proves
anything about #39; it (a) cross-checks the Lean theorems numerically, and
(b) measures the greedy exponent that #39 asks to beat.

Arms
----
A. Sidon checker, two independent criteria (distinct sums with diagonal allowed,
   and distinct differences).  Agreement of the two IS the convention check
   demanded by the campaign contract's "Sidon convention drift" trap.
B. Greedy / Mian-Chowla infinite Sidon set (OEIS A005282), computed to a budget.
   - verified Sidon at every prefix
   - cross-check of the Lean FLOOR theorem  N <= k + k^3 + k^2  at every prefix
     (a greedy prefix A_k is by construction maximal in [1, a_k])
   - measured growth exponent  a_k ~ k^theta  =>  A(N) ~ N^(1/theta)
C. Erdos-Turan construction: for prime p, {2pk + (k^2 mod p) : 0<=k<p} is Sidon,
   size p inside [0, 2p^2].  Shows exponent 1/2 IS attained for each fixed N,
   i.e. #39's difficulty is entirely the uniform-in-N requirement.
   - cross-check of the Lean CEILING theorem  k^2 <= k + 2N + 1.

Output: receipts.json  (sha256 over the canonical serialisation of each witness)
"""

import hashlib
import json
import math
import sys
import time

# ---------------------------------------------------------------- arm A


def is_sidon_by_sums(A):
    """Sidon with diagonal summands ALLOWED: all a+b (a<=b) distinct.
    This is exactly `Erdos39.SidonF` of E39.lean."""
    seen = set()
    L = sorted(A)
    for i, a in enumerate(L):
        for b in L[i:]:
            s = a + b
            if s in seen:
                return False
            seen.add(s)
    return True


def is_sidon_by_diffs(A):
    """All differences a-b (a != b) distinct."""
    seen = set()
    L = sorted(A)
    for i, a in enumerate(L):
        for b in L[i + 1:]:
            d = b - a
            if d in seen:
                return False
            seen.add(d)
    return True


def convention_agreement_check(trials=4000, seed=20260905):
    """The two criteria must agree on every input.  Randomised + exhaustive-small."""
    import random
    rng = random.Random(seed)
    disagreements = []
    tested = 0
    # exhaustive over all subsets of [1,9]
    for mask in range(1, 1 << 9):
        S = [i + 1 for i in range(9) if mask >> i & 1]
        tested += 1
        if is_sidon_by_sums(S) != is_sidon_by_diffs(S):
            disagreements.append(S)
    # random larger sets
    for _ in range(trials):
        n = rng.randint(2, 12)
        S = rng.sample(range(1, 200), n)
        tested += 1
        if is_sidon_by_sums(S) != is_sidon_by_diffs(S):
            disagreements.append(sorted(S))
    return {"tested": tested, "disagreements": disagreements,
            "agree": len(disagreements) == 0}


# ---------------------------------------------------------------- arm B


def greedy_sidon(k_target, time_budget_s):
    """Mian-Chowla: greedily take the least integer keeping the set Sidon.
    Rejection uses the difference criterion with largest-element-first scan
    (small differences are the dense ones, so this exits early)."""
    A = []
    used = set()          # differences already realised
    x = 1
    t0 = time.time()
    while len(A) < k_target:
        if time.time() - t0 > time_budget_s:
            break
        ok = True
        new = []
        for a in reversed(A):          # largest first => smallest difference first
            d = x - a
            if d in used:
                ok = False
                break
            new.append(d)
        if ok:
            # also forbid the "2x = a+b" coincidence; under the difference
            # criterion that is exactly a repeat inside `new` itself.
            if len(set(new)) == len(new):
                A.append(x)
                used.update(new)
            else:
                ok = False
        x += 1
    return A, time.time() - t0


def blocked_set_lean(A):
    """EXACT transcription of `Erdos39.Blocked` from E39.lean:
        ((A x A x A).image fun t => t.1 + t.2.1 - t.2.2)   -- NAT truncated subtraction
      U ((A x A).image   fun t => (t.1 + t.2) / 2)         -- NAT floor division
    Note the second image uses FLOOR halving, so it also throws in (a+b)//2 for
    ODD a+b.  `Blocked` is therefore an OVER-approximation of the true set of
    non-extendable values -- which is sound for every theorem in E39.lean (they
    only ever use "not blocked => extendable"), but means the Lean `Greedy` set
    need not coincide with A005282.  This function exists to measure that gap."""
    out = set()
    for a in A:
        for b in A:
            for c in A:
                out.add(max(0, a + b - c))
            out.add((a + b) // 2)
    return out


def greedy_lean_predicate(k_target, time_budget_s):
    """The sequence `Erdos39.G` of E39.lean: least x > max(A) with x not in Blocked A."""
    A = []
    m = 0
    t0 = time.time()
    while len(A) < k_target:
        if time.time() - t0 > time_budget_s:
            break
        B = blocked_set_lean(A)
        x = m + 1
        while x in B:
            x += 1
        A.append(x)
        m = x
    return A


def fit_exponent(xs, ys):
    """least-squares slope of log y against log x"""
    lx = [math.log(v) for v in xs]
    ly = [math.log(v) for v in ys]
    n = len(lx)
    mx = sum(lx) / n
    my = sum(ly) / n
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) ** 2 for a in lx)
    return num / den


# ---------------------------------------------------------------- arm C


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def erdos_turan(p):
    """{2pk + (k^2 mod p) : 0 <= k < p}: a Sidon set of size p in [0, 2p^2]."""
    return [2 * p * k + (k * k) % p for k in range(p)]


# ---------------------------------------------------------------- driver


def sha(obj):
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def main():
    out = {"campaign": "erdos39-close-2026-09-05",
           "python": sys.version.split()[0]}

    # ---- A
    out["arm_A_convention"] = convention_agreement_check()

    # ---- B
    k_target = int(sys.argv[1]) if len(sys.argv) > 1 else 900
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 90.0
    A, secs = greedy_sidon(k_target, budget)
    k = len(A)
    prefix_sidon_ok = True
    for m in (2, 3, 5, 10, 25, 60, 120, 250, 500, k):
        if m <= k and not is_sidon_by_sums(A[:m]):
            prefix_sidon_ok = False
    full_diff_ok = is_sidon_by_diffs(A)

    # Lean FLOOR cross-check: A[:m] is maximal-Sidon in [1, A[m-1]],
    # so the theorem `maximal_sidon_dense` predicts  N <= m + m^3 + m^2.
    floor_violations = []
    worst = None
    for m in range(1, k + 1):
        N = A[m - 1]
        bound = m + m ** 3 + m ** 2
        if N > bound:
            floor_violations.append({"k": m, "a_k": N, "bound": bound})
        r = N / (m ** 3)
        if worst is None or r > worst[1]:
            worst = (m, r)

    # measured growth exponent (tail half, to shed the transient)
    lo = max(20, k // 2)
    theta = fit_exponent(list(range(lo, k + 1)), A[lo - 1:k])
    # External cross-check: A005282 listing retrieved 2026-09-05 via web search.
    # This is a CROSS-CHECK REFERENCE (untrusted external text), not an authority;
    # the authority for Sidon-ness is `is_sidon_by_sums` above, run on our own output.
    A005282_ref = [1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182, 204, 252,
                   290, 361, 401, 475, 565, 593, 662, 775, 822, 916, 970, 1016, 1159,
                   1312, 1395, 1523, 1572, 1821, 1896, 2029, 2254, 2379, 2510, 2780,
                   2925, 3155, 3354, 3591, 3797, 3998, 4297, 4433, 4779, 4851]
    n_ref = min(len(A005282_ref), k)
    out["arm_B_external_crosscheck"] = {
        "reference": "OEIS A005282 (Mian-Chowla), first 50 terms, retrieved 2026-09-05",
        "terms_compared": n_ref,
        "matches": A[:n_ref] == A005282_ref[:n_ref],
        "first_mismatch_index": next((i for i in range(n_ref)
                                      if A[i] != A005282_ref[i]), None),
    }

    # Formal <-> computational: does the EXACT Lean `Blocked` predicate generate
    # the same sequence?  (See blocked_set_lean docstring: it over-approximates.)
    k_lean = min(k, 60)
    A_lean = greedy_lean_predicate(k_lean, 60.0)
    out["arm_B_lean_predicate"] = {
        "definition": "Erdos39.G / Erdos39.Greedy of E39.lean (least x > max A, x not in Blocked A)",
        "k": len(A_lean),
        "first_25": A_lean[:25],
        "sidon_verified_by_sums": is_sidon_by_sums(A_lean),
        "agrees_with_A005282_greedy": A_lean == A[:len(A_lean)],
        "first_divergence_index": next((i for i in range(len(A_lean))
                                        if A_lean[i] != A[i]), None),
        "lean_floor_bound_holds": all(
            A_lean[m - 1] <= m + m ** 3 + m ** 2 for m in range(1, len(A_lean) + 1)),
        "note": ("Blocked over-approximates (it floor-halves ODD sums too). Every "
                 "E39.lean theorem only uses 'not blocked => extendable', so all "
                 "proved statements hold for whichever sequence this is."),
        "sha256_witness": sha(A_lean),
    }

    out["arm_B_greedy"] = {
        "source": "greedy Sidon set, diagonal-allowed convention (= Erdos39.SidonF)",
        "k_reached": k,
        "a_k": A[-1] if A else None,
        "seconds": round(secs, 2),
        "first_25": A[:25],
        "prefix_sidon_verified_by_sums": prefix_sidon_ok,
        "full_set_sidon_by_differences": full_diff_ok,
        "lean_floor_theorem": "N <= k + k^3 + k^2  (Erdos39.maximal_sidon_dense)",
        "lean_floor_violations": floor_violations,
        "max_ratio_a_k_over_k_cubed": {"k": worst[0], "ratio": worst[1]} if worst else None,
        "measured_exponent_theta_a_k_~_k^theta": round(theta, 4),
        "implied_counting_exponent_1_over_theta": round(1.0 / theta, 4),
        "erdos39_target_exponent": 0.5,
        "published_record_ruzsa": round(math.sqrt(2) - 1, 6),
        "proved_greedy_floor_exponent": round(1.0 / 3.0, 6),
        "sha256_witness": sha(A),
    }

    # ---- C
    et = []
    for p in [7, 11, 13, 17, 19, 23, 31, 61, 127, 251, 509]:
        if not is_prime(p):
            continue
        S = erdos_turan(p)
        N = max(S)
        ok_s = is_sidon_by_sums(S)
        ok_d = is_sidon_by_diffs(S)
        kk = len(S)
        et.append({
            "p": p, "card": kk, "N": N,
            "sidon_by_sums": ok_s, "sidon_by_diffs": ok_d,
            "density_card_over_sqrtN": round(kk / math.sqrt(N), 4),
            "lean_ceiling_k2_le_k_plus_2N_plus_1": kk * kk <= kk + 2 * N + 1,
            "sha256_witness": sha(S),
        })
    out["arm_C_erdos_turan"] = {
        "construction": "{2pk + (k^2 mod p) : 0 <= k < p}",
        "lean_ceiling_theorem": "k^2 <= k + 2N + 1  (Erdos39.sidon_card_sq_le)",
        "instances": et,
        "all_sidon": all(e["sidon_by_sums"] and e["sidon_by_diffs"] for e in et),
        "all_respect_ceiling": all(e["lean_ceiling_k2_le_k_plus_2N_plus_1"] for e in et),
    }

    # ---- D : is the counting obstruction ever active against the #39 target?
    # E39.lean `sidon_card_sq_le` proves k^2 <= k + 2N + 1 for every Sidon set in
    # [1,N].  That pigeonhole bound is the ONLY cheap obstruction available for a
    # NEGATIVE close of #39.  Test whether the #39 target density k = ceil(c*N^(1/2-eps))
    # ever violates it -- if it never does, no negative close can come from counting.
    # `>>_eps` permits a threshold N0(eps), so a violation only matters if it
    # PERSISTS as N grows.  For each (eps, c) record the largest violating N and
    # check the ceiling then holds for every larger N in the grid.
    # For k = c*N^(1/2-eps) the ceiling k^2 <= 2N reads c^2 * N^(1-2eps) <= 2N,
    # i.e. N^(2 eps) >= c^2/2, i.e. N >= (c^2/2)^(1/(2 eps)) =: N0(eps,c).
    # N0 is FINITE for every eps>0, so the obstruction always dies out; it is
    # never asymptotically active.  Verify that closed form numerically.
    eps_list = [0.25, 0.1, 0.05, 0.01, 0.001, 1e-6]
    c_list = [1.0, 2.0, 10.0, 100.0]
    rows = []
    bad = []
    for eps in eps_list:
        for c in c_list:
            log10_N0 = max(0.0, math.log10(c * c / 2.0) / (2.0 * eps))
            # check the ceiling holds at N0*10 and at N0*10^6 (in log space, k^2 <= 2N)
            checks = []
            for pad in (1.0, 6.0):
                lg = log10_N0 + pad
                log10_k = math.log10(c) + (0.5 - eps) * lg
                checks.append(2 * log10_k <= math.log10(2.0) + lg)
            # and check a violation really does occur below N0 when N0 > 1
            below = None
            if log10_N0 > 1.0:
                lg = log10_N0 - 1.0
                log10_k = math.log10(c) + (0.5 - eps) * lg
                below = 2 * log10_k > math.log10(2.0) + lg
            rows.append({"eps": eps, "c": c,
                         "log10_N0": round(log10_N0, 3),
                         "ceiling_holds_above_N0": all(checks),
                         "violated_just_below_N0": below})
            if not all(checks):
                bad.append({"eps": eps, "c": c})
    out["arm_D_counting_obstruction"] = {
        "question": ("does the #39 target density k = ceil(c*N^(1/2-eps)) ever violate the "
                     "machine-checked ceiling k^2 <= k + 2N + 1 (Erdos39.sidon_card_sq_le) "
                     "for LARGE N?"),
        "closed_form_threshold": "N0(eps,c) = (c^2/2)^(1/(2*eps)), finite for every eps>0",
        "eps_values": eps_list,
        "implied_constants_tested": c_list,
        "per_pair": rows,
        "pairs_where_ceiling_fails_above_N0": bad,
        "obstruction_active_asymptotically": len(bad) > 0,
        "reading": ("For every eps>0 and every implied constant c, the ceiling is violated "
                    "only for N below the finite threshold N0(eps,c) -- exactly what the "
                    "threshold N0(eps) in `>>_eps` permits. The pigeonhole/counting "
                    "obstruction is therefore never asymptotically active against the #39 "
                    "target. Consequence: a NEGATIVE close of #39 cannot come from counting, "
                    "and a POSITIVE close must be a CONSTRUCTION. Elementary; stated here "
                    "because it is the only cheap obstruction the ceiling theorem supplies."),
    }

    with open("receipts.json", "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({kk: (vv if kk != "arm_B_greedy" else
                           {a: b for a, b in vv.items() if a != "first_25"})
                      for kk, vv in out.items()}, indent=1)[:4000])


if __name__ == "__main__":
    main()
