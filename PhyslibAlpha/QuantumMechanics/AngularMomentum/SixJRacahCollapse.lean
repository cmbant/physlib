/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacah

/-!

# The collapse of Racah's double sum to a single sum

The purely combinatorial half of the proof of Racah's closed formula for the operator-defined
`sixJ`: the double sum `Tsum` produced by the highest-weight reduction of the recoupling
coefficient equals the single sum `Xs` (a balanced terminating `₄F₃(1)`), up to explicit factorials.
Nothing here involves operators or the Clebsch–Gordan structure of Physlib.

## i. Overview

In doubled units (`a = 2 j₁`, `b = 2 j₂`, `c = 2 j₃`, `J = (a + b + c)/2 - K`,
`j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃`) put `X = b + c - k₃ - K`. All sums are zero-extended over `ℤ`, through
`factZ` (`n!`, zero for `n < 0`) and `invFact` (`1/n!`, zero for `n < 0`).

`Tsum a b c K k₁ k₃ = Σ_α Σ_z (-1)^z (a-α)! (b-k₁+α)! (X+α)! /
  (α! z! (k₃-z)! (k₁-α-z)! (c-K+k₁-z)! (b-k₁-k₃+z+α)! (K-k₁-k₃+z)!)`,

`Xs a b c K k₁ k₃ = Σ_x (-1)^x C(k₃, x) C(a+X+1, k₁-x) (c-k₃+x)! (b-x)! (a-k₁+x)! / (K-k₁-k₃+x)!`,

and the identity proved is

`Tsum = Xs · X! / ((c-K+k₁)! k₃! (b-k₃)! (c-k₃)!)`        (`Tsum_eq_Xs`).

The proof has three ingredients.

* For fixed `α`, the `z`-sum is Racah's form `racahR` of the Clebsch–Gordan sum of
  `ClebschGordanFormula` for `⟨b c k₃; ν β γ⟩`, which equals the `x`-form `racahL` by the
  recursion `racahL_eq_racahR`; this is the same transformation as `cgSum_eq_racahSum`.
* After exchanging the finite sums, the `α`-sum is the upper-index Vandermonde convolution
  `Σ_α (a-α)! (X+α)! / (α! (m-α)!) = (a-m)! X! C(a+X+1, m)` (`vandermonde`), proved by a Pascal
  induction on `m`.
* The remaining sum is `Xs` after the substitution `m = k₁ - x`.

## ii. Key results

- `zbinom`: zero-extended integer binomial coefficient.
- `Tsum`, `Xs`: the two sums.
- `Collapse.vandermonde`: the upper-index Vandermonde evaluation.
- `Collapse.Tsum_eq_Xs_invFact`, `Tsum_eq_Xs`, `Tsum_eq_Xs_of_valid`: the collapse, in the form with
  inverse factorials, in the division form, and under the hypotheses `ValidA`, `ValidB` of `SixJ`.

## iii. Table of contents

- A. The two sums
- B. Zero-extended factorials and binomials
- C. The upper-index Vandermonde convolution
- D. The `z`-sum as `racahR` and the `x`-form
- E. The collapse

## iv. References

- Racah, *Theory of complex spectra II*, Phys. Rev. 62 (1942).
- Phase 2 (not in this file): `Xs` is the balanced `₄F₃(1)` with upper parameters
  `{-k₃, -k₁, c-k₃+1, a-k₁+1}` and lower parameters `{-b, K-k₁-k₃+1, a+b+c-k₁-k₃-K+2}`. Two Sears
  transformations (Whipple type, after a tetrahedral reorientation of the six arguments) give
  `Xs = (-1)^(a+b+c-K) (a-k₁)! (b-k₁)! (a-k₄)! (f-k₄)! (c-K+k₁)! k₃! (b-k₃)! (c-k₃)! /
    ((a+b+c-k₁-K+1)! X!) · racahSum6 …` with `k₄ = K - k₃`, `f = b + c - 2 k₃`; this
  is the identity that turns `Tsum` into Racah's sum `racahSum6` of `SixJRacah`.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

### A. The two sums

-/

/-- `C(n, j)` for integers `n, j`, and `0` unless `0 ≤ j ≤ n`. -/
def zbinom (n j : ℤ) : ℝ := if 0 ≤ j ∧ j ≤ n then ((n.toNat.choose j.toNat : ℕ) : ℝ) else 0

/-- Racah's double sum `T` of the highest-weight reduction of the recoupling coefficient, in the
doubled-spin data `a b c K k₁ k₃`, with `X = b + c - k₃ - K`; zero-extended over `ℤ`. -/
def Tsum (a b c K k₁ k₃ : ℤ) : ℝ :=
  ∑ᶠ α : ℤ, ∑ᶠ z : ℤ, (-1 : ℝ) ^ z * factZ (a - α) * factZ (b - k₁ + α) *
    factZ (b + c - k₃ - K + α) * invFact α * invFact z * invFact (k₃ - z) *
    invFact (k₁ - α - z) * invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) *
    invFact (K - k₁ - k₃ + z)

/-- The single sum `Xs` obtained from `Tsum` by the Vandermonde evaluation of the `α`-sum;
a balanced terminating `₄F₃(1)`. -/
def Xs (a b c K k₁ k₃ : ℤ) : ℝ :=
  ∑ᶠ x : ℤ, (-1 : ℝ) ^ x * zbinom k₃ x * zbinom (a + (b + c - k₃ - K) + 1) (k₁ - x) *
    factZ (c - k₃ + x) * factZ (b - x) * factZ (a - k₁ + x) * invFact (K - k₁ - k₃ + x)

namespace Collapse

/-!

### B. Zero-extended factorials and binomials

-/

lemma factZ_natCast (n : ℕ) : factZ n = (n.factorial : ℝ) := by simp [factZ]

lemma factZ_of_neg {u : ℤ} (h : u < 0) : factZ u = 0 := by
  rw [factZ, ite_eq_right (not_le.mpr h)]

lemma factZ_ne_zero {u : ℤ} (h : 0 ≤ u) : factZ u ≠ 0 := by
  rw [factZ, ite_eq_left h]; exact_mod_cast Nat.factorial_ne_zero _

lemma factZ_mul_invFact {u : ℤ} (h : 0 ≤ u) : factZ u * invFact u = 1 := by
  rw [factZ, invFact, ite_eq_left h, ite_eq_left h]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _)

lemma invFact_eq_inv {u : ℤ} (h : 0 ≤ u) : invFact u = (factZ u)⁻¹ := by
  rw [factZ, invFact, ite_eq_left h, ite_eq_left h]

lemma zbinom_eq (n j : ℤ) : zbinom n j = factZ n * invFact j * invFact (n - j) := by
  by_cases h : 0 ≤ j ∧ j ≤ n
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    obtain ⟨J, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    have hJN : J ≤ N := by omega
    have e : ((N : ℤ) - J) = ((N - J : ℕ) : ℤ) := by omega
    rw [zbinom, ite_eq_left h, e, factZ_natCast, invFact_natCast, invFact_natCast]
    simp only [Int.toNat_natCast]
    have := Nat.choose_mul_factorial_mul_factorial hJN
    have h2 : ((N.choose J : ℕ) : ℝ) * J.factorial * (N - J).factorial = N.factorial := by
      exact_mod_cast this
    field_simp
    linarith
  · rw [zbinom, ite_eq_right h]
    by_cases h1 : n < 0
    · rw [factZ_of_neg h1]; ring
    · by_cases h2 : j < 0
      · rw [invFact_of_neg h2]; ring
      · rw [invFact_of_neg (by omega : n - j < 0)]; ring

/-- A sum over `ℤ` supported in `[0, k]` is a sum over `range (k + 1)`. -/
lemma finsum_eq_sum_range (f : ℤ → ℝ) (k : ℕ) (h : ∀ z : ℤ, (z < 0 ∨ (k : ℤ) < z) → f z = 0) :
    ∑ᶠ z : ℤ, f z = ∑ n ∈ Finset.range (k + 1), f n := by
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range (k + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro z hz
    rw [Function.mem_support] at hz
    by_contra hcon
    apply hz
    apply h
    by_contra h2
    have h3 : 0 ≤ z := by omega
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h3
    apply hcon
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨n, by simp only [Finset.mem_range]; omega, rfl⟩


/-!

### C. The upper-index Vandermonde convolution

-/

/-- Pascal's rule inside a real binomial sum. -/
lemma sum_range_choose_succ_mul_real (f : ℕ → ℝ) (k : ℕ) :
    ∑ a ∈ Finset.range (k + 1 + 1), ((k + 1).choose a : ℝ) * f a =
      ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * f a +
        ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * f (a + 1) := by
  have h : ∑ a ∈ Finset.range (k + 1), (k.choose (a + 1) : ℝ) * f (a + 1) + f 0 =
      ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * f a := by
    have h1 := Finset.sum_range_succ' (fun a => (k.choose a : ℝ) * f a) (k + 1)
    have h2 := Finset.sum_range_succ (fun a => (k.choose a : ℝ) * f a) (k + 1)
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero] at h2
    rw [← h2, h1]
  rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul, ← h]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-- Upper-index Vandermonde, binomial form:
`Σ_α C(m, α) (m + t - α)! (X + α)! = t! X! (m + t + X + 1)(m + t + X)⋯(t + X + 2)`. -/
lemma vand_nat (m : ℕ) : ∀ t X : ℕ,
    ∑ α ∈ Finset.range (m + 1), (m.choose α : ℝ) * (m + t - α).factorial * (X + α).factorial =
      (t.factorial : ℝ) * X.factorial * ((m + t + X + 1).descFactorial m : ℕ) := by
  induction m with
  | zero => intro t X; simp
  | succ m ih =>
    intro t X
    simp only [mul_assoc]
    rw [sum_range_choose_succ_mul_real
      (fun α => ((m + 1 + t - α).factorial : ℝ) * (X + α).factorial)]
    have e1 : ∑ α ∈ Finset.range (m + 1), (m.choose α : ℝ) *
        (((m + 1 + t - α).factorial : ℝ) * (X + α).factorial) =
        (((t + 1).factorial : ℝ) * X.factorial * ((m + (t + 1) + X + 1).descFactorial m : ℕ)) := by
      rw [← ih (t + 1) X]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [show m + 1 + t = m + (t + 1) by omega]; ring
    have e2 : ∑ α ∈ Finset.range (m + 1), (m.choose α : ℝ) *
        (((m + 1 + t - (α + 1)).factorial : ℝ) * (X + (α + 1)).factorial) =
        ((t.factorial : ℝ) * (X + 1).factorial * ((m + t + (X + 1) + 1).descFactorial m : ℕ)) := by
      rw [← ih t (X + 1)]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [show m + 1 + t - (α + 1) = m + t - α by omega,
        show X + (α + 1) = X + 1 + α by omega]
      ring
    rw [e1, e2, show m + (t + 1) + X + 1 = m + t + (X + 1) + 1 by omega,
      show m + 1 + t + X + 1 = m + t + (X + 1) + 1 by omega, Nat.descFactorial_succ,
      show m + t + (X + 1) + 1 - m = t + X + 2 by omega]
    push_cast
    rw [Nat.factorial_succ t, Nat.factorial_succ X]
    push_cast
    ring

/-- **Upper-index Vandermonde** (zero-extended): for `m ≤ a`,
`Σ_α (a - α)! (X + α)! / (α! (m - α)!) = (a - m)! X! C(a + X + 1, m)`. -/
lemma vandermonde (a X : ℕ) (m : ℤ) (hm : m ≤ a) :
    ∑ᶠ α : ℤ, factZ (a - α) * factZ (X + α) * invFact α * invFact (m - α) =
      factZ (a - m) * factZ X * zbinom ((a : ℤ) + X + 1) m := by
  by_cases hm0 : m < 0
  · rw [zbinom, ite_eq_right (by omega)]
    rw [mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
    by_cases hα : α < 0
    · rw [invFact_of_neg hα]; ring
    · rw [invFact_of_neg (by omega : m - α < 0)]; ring
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ m)
    have hMa : M ≤ a := by omega
    rw [finsum_eq_sum_range _ M (fun z hz => ?_)]
    · obtain ⟨t, rfl⟩ : ∃ t, a = M + t := ⟨a - M, by omega⟩
      have key := vand_nat M t X
      rw [zbinom, ite_eq_left (by omega)]
      simp only [Int.toNat_natCast, show (((M + t : ℕ) : ℤ) - M) = (t : ℤ) by omega,
        factZ_natCast]
      have hd : (((M + t + X + 1).descFactorial M : ℕ) : ℝ) =
          (M.factorial : ℝ) * ((M + t + X + 1).choose M : ℕ) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
      rw [hd] at key
      have hM : (M.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [show (((M + t : ℕ) : ℤ) + X + 1) = ((M + t + X + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
      have : ∀ α ∈ Finset.range (M + 1),
          factZ (((M + t : ℕ) : ℤ) - (α : ℕ)) * factZ ((X : ℤ) + (α : ℕ)) *
          invFact (α : ℕ) * invFact ((M : ℤ) - (α : ℕ)) =
          (M.factorial : ℝ)⁻¹ * ((M.choose α : ℝ) * (M + t - α).factorial * (X + α).factorial) := by
        intro α hα
        have hα' : α ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hα)
        have hc : (M.choose α : ℝ) * α.factorial * (M - α).factorial = M.factorial := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hα'
        rw [show (((M + t : ℕ) : ℤ) - (α : ℕ)) = ((M + t - α : ℕ) : ℤ) by omega,
          show (M : ℤ) - (α : ℕ) = ((M - α : ℕ) : ℤ) by omega,
          show (X : ℤ) + (α : ℕ) = ((X + α : ℕ) : ℤ) by push_cast; ring,
          factZ_natCast, factZ_natCast, invFact_natCast, invFact_natCast]
        have h1 : (α.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have h2 : ((M - α).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        field_simp
        rw [← hc]; ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, key]
      field_simp
    · rcases hz with hz | hz
      · rw [invFact_of_neg hz]; ring
      · rw [invFact_of_neg (by omega : (M : ℤ) - z < 0)]; ring

/-!

### D. The `z`-sum as `racahR` and the `x`-form

-/

lemma invFact_congr {u v : ℤ} (h : u = v) : invFact u = invFact v := by rw [h]

lemma factZ_congr {u v : ℤ} (h : u = v) : factZ u = factZ v := by rw [h]

lemma zchoose_eq_zbinom (n : ℕ) (j : ℤ) : ((zchoose n j : ℤ) : ℝ) = zbinom n j := by
  by_cases hj : j < 0
  · rw [zchoose_of_neg hj, zbinom, ite_eq_right (by omega)]; simp
  · obtain ⟨J, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
    rw [zchoose_natCast, zbinom]
    by_cases hJ : J ≤ n
    · rw [ite_eq_left (by omega)]; simp
    · rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma natCast_choose_eq (n z : ℕ) : ((n.choose z : ℕ) : ℝ) = zbinom n z := by
  rw [zbinom]
  by_cases hz : z ≤ n
  · rw [ite_eq_left (by omega)]; simp
  · rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- The inner `z`-sum of `Tsum` is Racah's sum `racahR` (divided by the factorials). -/
lemma z_sum_eq_racahR (b c k₃ : ℕ) (hb : k₃ ≤ b) (hc : k₃ ≤ c) (k₁ K α : ℤ) :
    ∑ᶠ z : ℤ, (-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z) =
      invFact k₃ * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃) *
        (racahR (b - k₃) (c - k₃) k₃ (k₁ - α) (K - k₁ - k₃) : ℝ) := by
  rw [finsum_eq_sum_range _ k₃ (fun z hz => ?_), racahR, Int.cast_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hzk : z ≤ k₃ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
    push_cast
    rw [zchoose_eq_zbinom, zchoose_eq_zbinom, natCast_choose_eq, zbinom_eq, zbinom_eq, zbinom_eq,
      zpow_natCast, Nat.cast_sub hb, Nat.cast_sub hc]
    have f1 : factZ k₃ * invFact k₃ = 1 := factZ_mul_invFact (by omega)
    have f2 : factZ ((b : ℤ) - k₃) * invFact ((b : ℤ) - k₃) = 1 := factZ_mul_invFact (by omega)
    have f3 : factZ ((c : ℤ) - k₃) * invFact ((c : ℤ) - k₃) = 1 := factZ_mul_invFact (by omega)
    rw [invFact_congr (show (b : ℤ) - k₃ - (k₁ - α - z) = b - k₁ - k₃ + z + α by ring),
      invFact_congr (show (c : ℤ) - k₃ - (K - k₁ - k₃ + z) = c - K + k₁ - z by ring)]
    calc _ = (1 : ℝ) * 1 * 1 * ((-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z)) := by
          ring
      _ = (factZ k₃ * invFact k₃) * (factZ ((b : ℤ) - k₃) * invFact ((b : ℤ) - k₃)) *
          (factZ ((c : ℤ) - k₃) * invFact ((c : ℤ) - k₃)) *
          ((-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z)) := by
          rw [f1, f2, f3]
      _ = _ := by ring
  · rcases hz with hz | hz
    · rw [invFact_of_neg hz]; ring
    · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring

/-- The `x`-form: `racahL` as the alternating binomial sum with factorials. -/
lemma racahL_eq_x_sum (b c k₃ : ℕ) (hb : k₃ ≤ b) (hc : k₃ ≤ c) (k₁ K α : ℤ) :
    (racahL (b - k₃) (c - k₃) k₃ (k₁ - α) (K - k₁ - k₃) : ℝ) =
      ∑ x ∈ Finset.range (k₃ + 1), (-1 : ℝ) ^ x * zbinom k₃ x *
        (factZ ((b : ℤ) - x) * invFact (k₁ - α - x) * invFact (b - k₁ + α)) *
        (factZ ((c : ℤ) - k₃ + x) * invFact (K - k₁ - k₃ + x) * invFact (c - K + k₁)) := by
  rw [racahL, Int.cast_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxk : x ≤ k₃ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  push_cast
  rw [zchoose_eq_zbinom, zchoose_eq_zbinom, natCast_choose_eq,
    show (((b - k₃ + k₃ - x : ℕ) : ℤ)) = (b : ℤ) - x by omega,
    show (((c - k₃ + x : ℕ) : ℤ)) = (c : ℤ) - k₃ + x by omega, zbinom_eq, zbinom_eq, zbinom_eq,
    show (b : ℤ) - x - (k₁ - α - x) = b - k₁ + α by ring,
    show (c : ℤ) - k₃ + x - (K - k₁ - k₃ + x) = c - K + k₁ by ring]
  ring

/-!

### E. The collapse

-/

/-- **Step 3 of the collapse.** `Tsum = Xs · X! / ((c - K + k₁)! k₃! (b - k₃)! (c - k₃)!)`,
`X = b + c - k₃ - K`, in the form with inverse factorials (no hypothesis on `K ≤ c + k₁` needed). -/
theorem Tsum_eq_Xs_invFact (a b c K k₁ k₃ : ℕ) (h1a : k₁ ≤ a) (h1b : k₁ ≤ b) (h3b : k₃ ≤ b)
    (h3c : k₃ ≤ c) (hX : K + k₃ ≤ b + c) :
    Tsum a b c K k₁ k₃ = Xs a b c K k₁ k₃ * factZ ((b : ℤ) + c - k₃ - K) *
      (invFact k₃ * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃) *
        invFact ((c : ℤ) - K + k₁)) := by
  obtain ⟨X, hXd⟩ : ∃ X : ℕ, (X : ℤ) = (b : ℤ) + c - k₃ - K := ⟨b + c - (k₃ + K), by omega⟩
  rw [Tsum, Xs, ← hXd]
  -- Step 1: the inner `z`-sum, for each `α`, as a sum over `x`
  have step1 : ∀ α : ℤ, ∑ᶠ z : ℤ, (-1 : ℝ) ^ z * factZ ((a : ℤ) - α) * factZ ((b : ℤ) - k₁ + α) *
      factZ ((X : ℤ) + α) * invFact α * invFact z * invFact ((k₃ : ℤ) - z) *
      invFact ((k₁ : ℤ) - α - z) * invFact ((c : ℤ) - K + k₁ - z) *
      invFact ((b : ℤ) - k₁ - k₃ + z + α) * invFact ((K : ℤ) - k₁ - k₃ + z) =
      (invFact (k₃ : ℤ) * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃)) *
        invFact ((c : ℤ) - K + k₁) * ∑ x ∈ Finset.range (k₃ + 1),
        ((-1 : ℝ) ^ x * zbinom k₃ x * factZ ((b : ℤ) - x) * factZ ((c : ℤ) - k₃ + x) *
          invFact ((K : ℤ) - k₁ - k₃ + x)) *
        (factZ ((a : ℤ) - α) * factZ ((X : ℤ) + α) * invFact α * invFact ((k₁ : ℤ) - x - α)) := by
    intro α
    have e1 : (∑ᶠ z : ℤ, (-1 : ℝ) ^ z * factZ ((a : ℤ) - α) * factZ ((b : ℤ) - k₁ + α) *
        factZ ((X : ℤ) + α) * invFact α * invFact z * invFact ((k₃ : ℤ) - z) *
        invFact ((k₁ : ℤ) - α - z) * invFact ((c : ℤ) - K + k₁ - z) *
        invFact ((b : ℤ) - k₁ - k₃ + z + α) * invFact ((K : ℤ) - k₁ - k₃ + z)) =
        (factZ ((a : ℤ) - α) * factZ ((b : ℤ) - k₁ + α) * factZ ((X : ℤ) + α) * invFact α) *
        ∑ᶠ z : ℤ, (-1 : ℝ) ^ z * invFact z * invFact ((k₃ : ℤ) - z) *
          invFact ((k₁ : ℤ) - α - z) * invFact ((c : ℤ) - K + k₁ - z) *
          invFact ((b : ℤ) - k₁ - k₃ + z + α) * invFact ((K : ℤ) - k₁ - k₃ + z) := by
      rw [finsum_eq_sum_range _ k₃ (fun z hz => ?_), finsum_eq_sum_range _ k₃ (fun z hz => ?_),
        Finset.mul_sum]
      · refine Finset.sum_congr rfl fun z _ => ?_
        ring
      · rcases hz with hz | hz
        · rw [invFact_of_neg hz]; ring
        · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring
      · rcases hz with hz | hz
        · rw [invFact_of_neg hz]; ring
        · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring
    rw [e1, z_sum_eq_racahR b c k₃ h3b h3c, ← Int.cast_inj (α := ℝ) |>.symm.mp
      (racahL_eq_racahR (b - k₃) (c - k₃) k₃ ((k₁ : ℤ) - α) ((K : ℤ) - k₁ - k₃)),
      racahL_eq_x_sum b c k₃ h3b h3c, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [invFact_congr (show (k₁ : ℤ) - α - x = k₁ - x - α by ring)]
    by_cases hα : 0 ≤ α
    · have f4 : factZ ((b : ℤ) - k₁ + α) * invFact ((b : ℤ) - k₁ + α) = 1 :=
        factZ_mul_invFact (by omega)
      linear_combination
        ((invFact (k₃ : ℤ) * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃)) *
          invFact ((c : ℤ) - K + k₁) *
          (((-1 : ℝ) ^ x * zbinom k₃ x * factZ ((b : ℤ) - x) * factZ ((c : ℤ) - k₃ + x) *
            invFact ((K : ℤ) - k₁ - k₃ + x)) *
          (factZ ((a : ℤ) - α) * factZ ((X : ℤ) + α) * invFact α *
            invFact ((k₁ : ℤ) - x - α)))) * f4
    · rw [invFact_of_neg (by omega : α < 0)]; ring
  rw [finsum_congr step1]
  have hWz : ∀ (x : ℕ) (α : ℤ), (α < 0 ∨ (k₁ : ℤ) < α) →
      factZ ((a : ℤ) - α) * factZ ((X : ℤ) + α) * invFact α * invFact ((k₁ : ℤ) - x - α) = 0 := by
    intro x α hα
    rcases hα with hα | hα
    · rw [invFact_of_neg hα]; ring
    · rw [invFact_of_neg (by omega : (k₁ : ℤ) - x - α < 0)]; ring
  have hW : ∀ x : ℕ, ∑ α ∈ Finset.Icc (0 : ℤ) k₁,
      (factZ ((a : ℤ) - α) * factZ ((X : ℤ) + α) * invFact α * invFact ((k₁ : ℤ) - x - α)) =
      factZ ((a : ℤ) - ((k₁ : ℤ) - x)) * factZ X * zbinom ((a : ℤ) + X + 1) ((k₁ : ℤ) - x) := by
    intro x
    rw [← vandermonde a X ((k₁ : ℤ) - x) (by omega)]
    symm
    refine finsum_eq_sum_of_support_subset _ fun α hα => ?_
    rw [Function.mem_support] at hα
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hcon
    exact hα (hWz x α (by omega))
  have hsupp : Function.support (fun α : ℤ =>
      (invFact (k₃ : ℤ) * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃)) *
        invFact ((c : ℤ) - K + k₁) * ∑ x ∈ Finset.range (k₃ + 1),
        ((-1 : ℝ) ^ x * zbinom k₃ x * factZ ((b : ℤ) - x) * factZ ((c : ℤ) - k₃ + x) *
          invFact ((K : ℤ) - k₁ - k₃ + x)) *
        (factZ ((a : ℤ) - α) * factZ ((X : ℤ) + α) * invFact α * invFact ((k₁ : ℤ) - x - α)))
      ⊆ ↑(Finset.Icc (0 : ℤ) k₁) := by
    intro α hα
    rw [Function.mem_support] at hα
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hcon
    apply hα
    rw [Finset.sum_eq_zero fun x _ => by rw [hWz x α (by omega), mul_zero], mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    finsum_eq_sum_range _ k₃ (fun z hz => ?_)]
  · rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hW]
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [factZ_congr (show (a : ℤ) - ((k₁ : ℤ) - x) = a - k₁ + x by ring), zpow_natCast]
    ring
  · rw [zbinom_eq]
    rcases hz with hz | hz
    · rw [invFact_of_neg hz]; ring
    · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring

end Collapse

/-- **Step 3 of the collapse** (the `α`-sum is the upper-index Vandermonde):
`Tsum = Xs · X! / ((c - K + k₁)! k₃! (b - k₃)! (c - k₃)!)`, `X = b + c - k₃ - K`. -/
theorem Tsum_eq_Xs (a b c K k₁ k₃ : ℕ) (h1a : k₁ ≤ a) (h1b : k₁ ≤ b) (h3b : k₃ ≤ b)
    (h3c : k₃ ≤ c) (hKc : K ≤ c + k₁) (hX : K + k₃ ≤ b + c) :
    Tsum a b c K k₁ k₃ = Xs a b c K k₁ k₃ * factZ ((b : ℤ) + c - k₃ - K) /
      (factZ ((c : ℤ) - K + k₁) * factZ k₃ * factZ ((b : ℤ) - k₃) * factZ ((c : ℤ) - k₃)) := by
  rw [Collapse.Tsum_eq_Xs_invFact a b c K k₁ k₃ h1a h1b h3b h3c hX,
    Collapse.invFact_eq_inv (by omega : (0 : ℤ) ≤ k₃),
    Collapse.invFact_eq_inv (by omega : (0 : ℤ) ≤ (b : ℤ) - k₃),
    Collapse.invFact_eq_inv (by omega : (0 : ℤ) ≤ (c : ℤ) - k₃),
    Collapse.invFact_eq_inv (by omega : (0 : ℤ) ≤ (c : ℤ) - K + k₁)]
  rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  ring

/-- `Tsum_eq_Xs` under the admissibility hypotheses of `SixJ` (`ValidA`, `ValidB`, and
`k₁ ≤ min a b`, `k₃ ≤ min b c`, as for the `Fin` indices there). -/
theorem Tsum_eq_Xs_of_valid {a b c K k₁ k₃ : ℕ} (hk₁ : k₁ < min a b + 1) (hk₃ : k₃ < min b c + 1)
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    Tsum a b c K k₁ k₃ = Xs a b c K k₁ k₃ * factZ ((b : ℤ) + c - k₃ - K) /
      (factZ ((c : ℤ) - K + k₁) * factZ k₃ * factZ ((b : ℤ) - k₃) * factZ ((c : ℤ) - k₃)) := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  exact Tsum_eq_Xs a b c K k₁ k₃ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

end PhyslibAlpha.Sl2
