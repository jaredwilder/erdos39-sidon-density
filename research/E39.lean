import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #39 — the exponent bracket

Canonical statement (erdosproblems.com/39, $500, OPEN):

> Is there an infinite Sidon set `A ⊆ ℕ` such that `|A ∩ {1,…,N}| ≫_ε N^(1/2-ε)`
> for all `ε > 0`?

Known: the greedy construction gives `≫ N^(1/3)`; Ajtai–Komlós–Szemerédi give
`≫ (N log N)^(1/3)`; the record is Ruzsa's `N^(√2-1+o(1))`, `√2-1 = 0.41421…`.

This file does **not** close #39.  It machine-checks the two endpoints of the
exponent window inside which the whole problem lives, and states #39 formally.

* `Conjecture`          — the formal statement of the problem (a `Prop`, unproved).
* `sidon_card_sq_le`    — **CEILING.** A Sidon subset of `[1,N]` has `k² ≤ k + 2N + 1`,
                          so `k ≲ √(2N)`: the exponent `1/2` in #39 cannot be improved,
                          which is exactly why the statement carries an `ε`.
* `count_sq_le`         — the ceiling transported to the infinite object of `Conjecture`.
* `maximal_sidon_dense` — **FLOOR.** A Sidon subset of `[1,N]` that is *maximal* there
                          satisfies `N ≤ k + k³ + k²`, so `k ≳ (N/3)^(1/3)`.  Applied to
                          the greedy set this is the `≫ N^(1/3)` baseline of #39.
* `exists_dense_sidon`  — for every `N` there is a Sidon `A ⊆ [1,N]` with `N ≤ 3·k³`.
* `Greedy`, `greedy_is_sidon`, `greedy_infinite`, `greedy_density`
                        — **the baseline of #39, formalized.**  An explicit *infinite*
                          Sidon set with `N ≤ 3·(A(N)+1)³` for every `N`, i.e.
                          `A(N) ≥ (N/3)^(1/3) - 1`.  This is the "trivial greedy
                          construction achieves `≫ N^(1/3)`" quoted in the problem.

The floor proof is the whole content of the greedy bound, stated in its sharp
"obstruction" form (`sidon_insert_of_not_blocked`): an integer `x ∉ A` fails to
extend a Sidon set `A` only if `x = a+b-c` or `2x = a+b` for some `a,b,c ∈ A`.
That is at most `k³ + k²` values, and it is what forces `k ≳ N^(1/3)`.

No `sorry`.  Author: Oracle campaign `erdos39-close-2026-09-05`.
-/

namespace Erdos39

/-! ## Definitions -/

/-- Sidon (`B₂`) set, finite version: all pairwise sums are distinct up to the
forced coincidence `a+b = b+a`.  Diagonal terms are **allowed** (`a = b` is a legal
choice of summands), which is the convention of the canonical statement. -/
def SidonF (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Sidon (`B₂`) set, infinite version. -/
def SidonS (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

open Classical in
/-- The counting function `A(N) = |A ∩ {1,…,N}|`. -/
noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

/-- **Erdős Problem #39** ($500, OPEN).  Is there an infinite Sidon set `A ⊆ ℕ`
with `|A ∩ {1,…,N}| ≫_ε N^(1/2-ε)` for every `ε > 0`?

Quantifier order is the canonical one: `ε` is chosen first, then the implied
constant `c` and threshold `N₀` may depend on `ε`, then the bound holds for every
`N ≥ N₀`.  This is the literal reading of `≫_ε`. -/
def Conjecture : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ SidonS A ∧
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (count A N : ℝ)

/-! ## The ceiling: a Sidon set in `[1,N]` has at most about `√(2N)` elements

All `k(k-1)` ordered differences of a Sidon set are distinct and live in
`[-N, N]`, so `k² - k ≤ 2N + 1`.  Consequently the exponent `1/2` in `Conjecture`
is a hard ceiling and the `ε` in the statement is not removable. -/

theorem sidon_card_sq_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hS : SidonF A) : A.card * A.card ≤ A.card + 2 * N + 1 := by
  have hmap : ∀ p ∈ A.offDiag, ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, _⟩ := hp
    have h1 := Finset.mem_Icc.mp (hA hp1)
    have h2 := Finset.mem_Icc.mp (hA hp2)
    rw [Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)) A.offDiag := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp hq
    obtain ⟨hp1, hp2, hpne⟩ := hp
    obtain ⟨hq1, hq2, _⟩ := hq
    simp only at hpq
    have hsum : p.1 + q.2 = q.1 + p.2 := by omega
    rcases hS p.1 hp1 q.2 hq2 q.1 hq1 p.2 hp2 hsum with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext h1 h2.symm
    · exact absurd h1 hpne
  have hcard : A.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ)).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  have hIcc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    have : ((N : ℤ) + 1 - -(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hkk : A.card ≤ A.card * A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  rw [Finset.offDiag_card, hIcc] at hcard
  omega

open Classical in
/-- The ceiling, transported to the infinite object of `Conjecture`: for every Sidon
set `A ⊆ ℕ` and every `N`, `A(N)² ≤ A(N) + 2N + 1`.  Hence `A(N) ≲ √(2N)`. -/
theorem count_sq_le {A : Set ℕ} (hS : SidonS A) (N : ℕ) :
    count A N * count A N ≤ count A N + 2 * N + 1 := by
  refine sidon_card_sq_le (N := N) (A := (Finset.Icc 1 N).filter (fun n => n ∈ A))
    (Finset.filter_subset _ _) ?_
  intro a ha b hb c hc d hd habcd
  rw [Finset.mem_filter] at ha hb hc hd
  exact hS a ha.2 b hb.2 c hc.2 d hd.2 habcd

/-! ## The floor: a maximal Sidon set in `[1,N]` has at least `(N/3)^(1/3)` elements -/

/-- The values a Sidon set `A` forbids: an integer `x ∉ A` can fail to extend `A`
only by being of the form `a + b - c` or `(a + b)/2` with `a, b, c ∈ A`. -/
def Blocked (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A ×ˢ A).image fun t => t.1 + t.2.1 - t.2.2) ∪ ((A ×ˢ A).image fun t => (t.1 + t.2) / 2)

theorem card_blocked_le (A : Finset ℕ) :
    (Blocked A).card ≤ A.card ^ 3 + A.card ^ 2 := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_product]
    ring_nf
    exact le_refl _
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product]
    ring_nf
    exact le_refl _

theorem mem_blocked_sub {A : Finset ℕ} {x c d b : ℕ} (hc : c ∈ A) (hd : d ∈ A) (hb : b ∈ A)
    (h : x + b = c + d) : x ∈ Blocked A := by
  refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(c, d, b), ?_, ?_⟩)
  · simp [Finset.mem_product, hc, hd, hb]
  · simp only
    omega

theorem mem_blocked_half {A : Finset ℕ} {x c d : ℕ} (hc : c ∈ A) (hd : d ∈ A)
    (h : x + x = c + d) : x ∈ Blocked A := by
  refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, d), ?_, ?_⟩)
  · simp [Finset.mem_product, hc, hd]
  · simp only
    omega

/-- **The obstruction lemma.**  If `A` is Sidon, `x ∉ A`, and `x` is not blocked by
`A`, then `A ∪ {x}` is again Sidon.  This is the entire content of the greedy
`N^(1/3)` lower bound for #39, in contrapositive (and constructive) form. -/
theorem sidon_insert_of_not_blocked {A : Finset ℕ} {x : ℕ} (hS : SidonF A)
    (hx : x ∉ A) (hnb : x ∉ Blocked A) : SidonF (insert x A) := by
  intro a ha b hb c hc d hd hsum
  rw [Finset.mem_insert] at ha hb hc hd
  -- `x` is kept as a live variable throughout; every case is closed either by
  -- `omega` on the accumulated linear equations, or by `hnb`, or by `hS`.
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · -- a = x, b = x, so 2x = c + d
      rcases hc with hc | hc
      · exact Or.inl ⟨by omega, by omega⟩
      · rcases hd with hd | hd
        · have hcx : c = x := by omega
          subst hcx
          exact absurd hc hx
        · exact absurd (mem_blocked_half hc hd (by omega)) hnb
    · -- a = x, b ∈ A
      rcases hc with hc | hc
      · exact Or.inl ⟨by omega, by omega⟩
      · rcases hd with hd | hd
        · exact Or.inr ⟨by omega, by omega⟩
        · exact absurd (mem_blocked_sub hc hd hb (by omega)) hnb
  · rcases hb with hb | hb
    · -- b = x, a ∈ A
      rcases hc with hc | hc
      · exact Or.inr ⟨by omega, by omega⟩
      · rcases hd with hd | hd
        · exact Or.inl ⟨by omega, by omega⟩
        · exact absurd (mem_blocked_sub hc hd ha (by omega)) hnb
    · -- a, b ∈ A
      rcases hc with hc | hc
      · rcases hd with hd | hd
        · exact absurd (mem_blocked_half ha hb (by omega)) hnb
        · exact absurd (mem_blocked_sub ha hb hd (by omega)) hnb
      · rcases hd with hd | hd
        · exact absurd (mem_blocked_sub ha hb hc (by omega)) hnb
        · exact hS a ha b hb c hc d hd hsum

/-- `A` is a maximal Sidon subset of `[1,N]`. -/
def MaximalIn (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ x ∈ Finset.Icc 1 N, x ∉ A → ¬ SidonF (insert x A)

/-- The counting core of the floor: if `A` together with the values it blocks covers
all of `[1,N]`, then `N ≤ k + k³ + k²`. -/
theorem dense_of_covers {N : ℕ} {A : Finset ℕ} (hcov : Finset.Icc 1 N ⊆ A ∪ Blocked A) :
    N ≤ A.card + A.card ^ 3 + A.card ^ 2 := by
  have h1 : (Finset.Icc 1 N).card ≤ (A ∪ Blocked A).card := Finset.card_le_card hcov
  rw [Nat.card_Icc] at h1
  have h2 : (A ∪ Blocked A).card ≤ A.card + (Blocked A).card := Finset.card_union_le _ _
  have h3 := card_blocked_le A
  omega

/-- **FLOOR.**  A maximal Sidon subset of `[1,N]` satisfies `N ≤ k + k³ + k²`. -/
theorem maximal_sidon_dense {N : ℕ} {A : Finset ℕ} (_hA : A ⊆ Finset.Icc 1 N)
    (hS : SidonF A) (hM : MaximalIn N A) :
    N ≤ A.card + A.card ^ 3 + A.card ^ 2 := by
  refine dense_of_covers ?_
  intro x hxI
  by_cases hxA : x ∈ A
  · exact Finset.mem_union_left _ hxA
  · refine Finset.mem_union_right _ ?_
    by_contra hnb
    exact (hM x hxI hxA) (sidon_insert_of_not_blocked hS hxA hnb)

/-- The floor in cube-root form: a maximal Sidon subset of `[1,N]` has `N ≤ 3k³`. -/
theorem maximal_sidon_dense_cube {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hS : SidonF A) (hM : MaximalIn N A) : N ≤ 3 * A.card ^ 3 := by
  have h := maximal_sidon_dense hA hS hM
  rcases Nat.eq_zero_or_pos A.card with h0 | h0
  · rw [h0] at h ⊢
    norm_num at h ⊢
    omega
  · have e1 : A.card ^ 1 ≤ A.card ^ 3 := Nat.pow_le_pow_right h0 (by norm_num)
    have e2 : A.card ^ 2 ≤ A.card ^ 3 := Nat.pow_le_pow_right h0 (by norm_num)
    rw [pow_one] at e1
    omega

/-! ## Existence: dense Sidon sets in `[1,N]` -/

open Classical in
/-- For every `N` there is a Sidon set `A ⊆ [1,N]` with `N ≤ 3·|A|³`, i.e. of size
`≳ (N/3)^(1/3)`.  This is the greedy baseline that Erdős #39 asks to beat. -/
theorem exists_dense_sidon (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ SidonF A ∧ N ≤ 3 * A.card ^ 3 := by
  set S : Finset (Finset ℕ) := (Finset.Icc 1 N).powerset.filter (fun A => SidonF A) with hSdef
  have hemp : (∅ : Finset ℕ) ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro a ha
    simp at ha
  obtain ⟨A, hAS, hAmax⟩ := Finset.exists_max_image S Finset.card ⟨∅, hemp⟩
  rw [hSdef, Finset.mem_filter, Finset.mem_powerset] at hAS
  obtain ⟨hAsub, hAsidon⟩ := hAS
  refine ⟨A, hAsub, hAsidon, maximal_sidon_dense_cube hAsub hAsidon ?_⟩
  intro x hxI hxA hcon
  have hmem : insert x A ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hxI hAsub, hcon⟩
  have hle := hAmax _ hmem
  rw [Finset.card_insert_of_notMem hxA] at hle
  omega

/-! ## The greedy infinite Sidon set — the `N^(1/3)` baseline of #39, formalized

`Greedy` is the set produced by "always take the least integer that keeps the set
Sidon".  `greedy_is_sidon` + `greedy_infinite` + `greedy_density` together say:

> there is an infinite Sidon set `A ⊆ ℕ` with `N ≤ 3·(A(N)+1)³` for every `N`,
> i.e. `A(N) ≥ (N/3)^(1/3) - 1`.

That is exactly the "trivial greedy construction achieves `≫ N^(1/3)`" quoted in
the statement of Erdős #39 — now machine-checked. -/

theorem blocked_mono {A B : Finset ℕ} (h : A ⊆ B) : Blocked A ⊆ Blocked B := by
  refine Finset.union_subset_union ?_ ?_
  · exact Finset.image_subset_image
      (Finset.product_subset_product h (Finset.product_subset_product h h))
  · exact Finset.image_subset_image (Finset.product_subset_product h h)

theorem exists_next (A : Finset ℕ) (m : ℕ) : ∃ x, m < x ∧ x ∉ Blocked A := by
  refine ⟨max m ((Blocked A).sup id) + 1, by omega, ?_⟩
  intro hc
  have hle : id (max m ((Blocked A).sup id) + 1) ≤ (Blocked A).sup id := Finset.le_sup hc
  simp only [id] at hle
  omega

/-- The greedy step: the least integer above `m` that `A` does not block. -/
def nextOf (A : Finset ℕ) (m : ℕ) : ℕ := Nat.find (exists_next A m)

theorem nextOf_gt (A : Finset ℕ) (m : ℕ) : m < nextOf A m :=
  (Nat.find_spec (exists_next A m)).1

theorem nextOf_notBlocked (A : Finset ℕ) (m : ℕ) : nextOf A m ∉ Blocked A :=
  (Nat.find_spec (exists_next A m)).2

theorem nextOf_min {A : Finset ℕ} {m y : ℕ} (h1 : m < y) (h2 : y < nextOf A m) :
    y ∈ Blocked A := by
  by_contra hc
  exact Nat.find_min (exists_next A m) h2 ⟨h1, hc⟩

/-- Stage `n` of the greedy construction: the first `n` elements, paired with the
largest of them. -/
def G : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | n + 1 => (insert (nextOf (G n).1 (G n).2) (G n).1, nextOf (G n).1 (G n).2)

/-- The greedy invariant: stage `n` is a Sidon set of size `n`, contained in
`[1, aₙ]`, whose elements together with the values it blocks cover all of `[1, aₙ]`.
The last clause is what makes the floor theorem apply. -/
theorem G_spec (n : ℕ) :
    SidonF (G n).1 ∧ (G n).1.card = n ∧ (∀ a ∈ (G n).1, 1 ≤ a ∧ a ≤ (G n).2) ∧
      Finset.Icc 1 (G n).2 ⊆ (G n).1 ∪ Blocked (G n).1 := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha; simp [G] at ha
    · simp [G]
    · intro a ha; simp [G] at ha
    · rw [show (G 0).2 = 0 from rfl, Finset.Icc_eq_empty (by omega)]
      exact Finset.empty_subset _
  | succ n ih =>
    obtain ⟨hS, hcard, hbd, hcov⟩ := ih
    have hfst : (G (n + 1)).1 = insert (nextOf (G n).1 (G n).2) (G n).1 := rfl
    have hsnd : (G (n + 1)).2 = nextOf (G n).1 (G n).2 := rfl
    have hgt := nextOf_gt (G n).1 (G n).2
    have hnotin : nextOf (G n).1 (G n).2 ∉ (G n).1 := by
      intro hc
      have := (hbd _ hc).2
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfst]
      exact sidon_insert_of_not_blocked hS hnotin (nextOf_notBlocked _ _)
    · rw [hfst, Finset.card_insert_of_notMem hnotin, hcard]
    · rw [hfst, hsnd]
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · omega
      · have := hbd a ha
        omega
    · rw [hfst, hsnd]
      intro y hy
      rw [Finset.mem_Icc] at hy
      by_cases hyx : y = nextOf (G n).1 (G n).2
      · subst hyx
        exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · by_cases hyn : y ≤ (G n).2
        · have := hcov (Finset.mem_Icc.mpr ⟨hy.1, hyn⟩)
          rcases Finset.mem_union.mp this with h | h
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
          · exact Finset.mem_union_right _ (blocked_mono (Finset.subset_insert _ _) h)
        · refine Finset.mem_union_right _ (blocked_mono (Finset.subset_insert _ _) ?_)
          exact nextOf_min (A := (G n).1) (m := (G n).2) (y := y) (by omega) (by omega)

/-- **The greedy bound `aₙ ≤ n³ + n² + n`.**  Hence `A(N) ≫ N^(1/3)`. -/
theorem G_snd_le (n : ℕ) : (G n).2 ≤ n + n ^ 3 + n ^ 2 := by
  obtain ⟨_, hcard, _, hcov⟩ := G_spec n
  have h := dense_of_covers hcov
  rwa [hcard] at h

theorem G_mono {m n : ℕ} (h : m ≤ n) : (G m).1 ⊆ (G n).1 := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih => exact ih.trans (Finset.subset_insert _ _)

theorem le_G_snd (n : ℕ) : n ≤ (G n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hgt := nextOf_gt (G n).1 (G n).2
    show n + 1 ≤ nextOf (G n).1 (G n).2
    omega

/-- The greedy infinite Sidon set. -/
def Greedy : Set ℕ := {a | ∃ n, a ∈ (G n).1}

theorem greedy_is_sidon : SidonS Greedy := by
  rintro a ⟨na, ha⟩ b ⟨nb, hb⟩ c ⟨nc, hc⟩ d ⟨nd, hd⟩ hsum
  refine (G_spec (max (max na nb) (max nc nd))).1
    a (G_mono ?_ ha) b (G_mono ?_ hb) c (G_mono ?_ hc) d (G_mono ?_ hd) hsum
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem greedy_infinite : Greedy.Infinite := by
  intro hfin
  have h1 : (G (hfin.toFinset.card + 1)).1 ⊆ hfin.toFinset := by
    intro a ha
    rw [Set.Finite.mem_toFinset]
    exact ⟨_, ha⟩
  have h2 := Finset.card_le_card h1
  rw [(G_spec (hfin.toFinset.card + 1)).2.1] at h2
  omega

open Classical in
theorem count_def (A : Set ℕ) (N : ℕ) :
    count A N = ((Finset.Icc 1 N).filter (fun m => m ∈ A)).card := rfl

open Classical in
theorem greedy_count_ge {n N : ℕ} (h : (G n).2 ≤ N) : n ≤ count Greedy N := by
  rw [count_def, ← (G_spec n).2.1]
  refine Finset.card_le_card ?_
  intro a ha
  rw [Finset.mem_filter, Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := (G_spec n).2.2.1 a ha
  exact ⟨⟨h1, by omega⟩, ⟨n, ha⟩⟩

/-- **The `N^(1/3)` baseline of Erdős #39, machine-checked.**  `Greedy` is an
infinite Sidon set (`greedy_is_sidon`, `greedy_infinite`) whose counting function
satisfies `N ≤ 3·(A(N)+1)³` for every `N`, i.e. `A(N) ≥ (N/3)^(1/3) - 1`. -/
theorem greedy_density (N : ℕ) : N ≤ 3 * (count Greedy N + 1) ^ 3 := by
  have hex : ∃ n, N ≤ (G n).2 := ⟨N, le_G_snd N⟩
  have hn1 : N ≤ (G (Nat.find hex)).2 := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · rw [h0] at hn1
    have : (G 0).2 = 0 := rfl
    omega
  · have hlt : ¬ (N ≤ (G (Nat.find hex - 1)).2) := Nat.find_min hex (by omega)
    rw [Nat.not_le] at hlt
    have hcount : Nat.find hex - 1 ≤ count Greedy N := greedy_count_ge (le_of_lt hlt)
    have hb := G_snd_le (Nat.find hex)
    have hk : Nat.find hex ≤ count Greedy N + 1 := by omega
    have e1 : Nat.find hex ^ 1 ≤ Nat.find hex ^ 3 := Nat.pow_le_pow_right h0 (by norm_num)
    have e2 : Nat.find hex ^ 2 ≤ Nat.find hex ^ 3 := Nat.pow_le_pow_right h0 (by norm_num)
    rw [pow_one] at e1
    have e3 : Nat.find hex ^ 3 ≤ (count Greedy N + 1) ^ 3 := Nat.pow_le_pow_left hk 3
    omega

/-! ## The bracket

`maximal_sidon_dense_cube` + `exists_dense_sidon` : exponent `1/3` is **achieved**.
`sidon_card_sq_le` + `count_sq_le`                : exponent `1/2` is a **ceiling**.

Erdős #39 asks whether the infinite problem attains the ceiling up to `ε`.
The published record inside this window is Ruzsa's `√2 - 1 = 0.41421…`; nothing in
this file reaches it, and `Erdos39` is left as a stated, unproved `Prop`. -/

end Erdos39

/-! ## Self-audit: every banked theorem is sorry-free.

Each `#print axioms` below must report only `propext`, `Classical.choice`,
`Quot.sound` — never `sorryAx`. -/

section Audit
#print axioms Erdos39.sidon_card_sq_le
#print axioms Erdos39.count_sq_le
#print axioms Erdos39.card_blocked_le
#print axioms Erdos39.sidon_insert_of_not_blocked
#print axioms Erdos39.maximal_sidon_dense
#print axioms Erdos39.maximal_sidon_dense_cube
#print axioms Erdos39.exists_dense_sidon
#print axioms Erdos39.blocked_mono
#print axioms Erdos39.G_spec
#print axioms Erdos39.G_snd_le
#print axioms Erdos39.greedy_is_sidon
#print axioms Erdos39.greedy_infinite
#print axioms Erdos39.greedy_count_ge
#print axioms Erdos39.greedy_density
end Audit
