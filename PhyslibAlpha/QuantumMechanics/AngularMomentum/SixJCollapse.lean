/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJProjection
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacah

/-!

# The operator-defined 6j symbol as a double sum of factorials

The highest-weight reduction of the recoupling coefficient: `sixJ` is an explicit constant times a
double sum of factorials. This is the operator half of the proof of Racah's closed formula for
`sixJ`; the purely combinatorial half (the collapse of the double sum to a single sum) is
independent of operators.

## i. Overview

In doubled units (`a = 2 j₁`, `b = 2 j₂`, `c = 2 j₃`, `J = (a + b + c)/2 - K`,
`j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃`), write `e = a + b - 2 k₁`, `f = b + c - 2 k₃`,
`k₂ = K - k₁`, `k₄ = K - k₃` and `X = b + c - k₃ - K`. The projection identity
`sum_cgCoefficient_mul_eq_recoupling` of `SixJProjection`, at `μ = 0` and `γ = k₂`, reads

`Σ_{α β ν} ⟨j₁ α j₂ β | j₁₂ 0⟩ ⟨j₁ α j₂₃ ν | J J⟩ ⟨j₂ β j₃ k₂ | j₂₃ ν⟩ =
  ⟨(j₁ j₂) j₁₂, j₃; J J | j₁, (j₂ j₃) j₂₃; J J⟩ · ⟨j₁₂ 0 j₃ k₂ | J J⟩`.

At weight `μ = 0` two of the three summed coefficients and the one on the right are top-weight
coefficients, which have a one-term Racah sum (`racahSum_top`), and the weight rule leaves the
single sum over `α`. The remaining coefficient `⟨j₂ β j₃ k₂ | j₂₃ ν⟩` is expanded by Racah's
formula (`cgCoefficient_racah`), whose `z`-sum gives the second summation index. The square roots
of the three coefficients combine into a perfect square times a constant (`cg_three_eq`), and the
constant, divided by the top-weight coefficient, is `Cconst` (`collapseConst_div`).

## ii. Key results

- `Tterm`, `collapseSum`: the summand and the double sum
  `Σ_α Σ_z (-1)^z (a-α)! (b-k₁+α)! (X+α)! /
    (α! z! (k₃-z)! (k₁-α-z)! (c-K+k₁-z)! (b-k₁-k₃+z+α)! (K-k₁-k₃+z)!)`, zero-extended over `ℤ`.
- `Cconst`: the constant
  `(-1)^(a+b+c-K) √(Δ₁ Δ₂ Δ₃ Δ₄) (a+b+c-K-k₁+1)! / ((a-k₁)! (b-k₁)! (a-K+k₃)! X!)`, where the
  `Δᵢ²` are the four `triCoeff` of Racah's formula, as in `sixJ_eq_racah`.
- `sixJ_eq_const_mul_collapseSum`: `sixJ = Cconst · collapseSum`, for `0 < a`, `0 < c` and
  admissible `k₁`, `k₃`, `K`.

## iii. Table of contents

- A. The double sum and the constant
- B. Top-weight Clebsch–Gordan coefficients
- C. The weight rule
- D. The double sum as a finite sum
- E. The constant
- F. The explicit formula

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  chapter 6.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. The double sum and the constant

-/

/-- The summand of the double sum `collapseSum`, with `X = b + c - k₃ - K`:
`(-1)^z (a-α)! (b-k₁+α)! (X+α)! / (α! z! (k₃-z)! (k₁-α-z)! (c-K+k₁-z)! (b-k₁-k₃+z+α)!
(K-k₁-k₃+z)!)`, zero unless every factorial argument is nonnegative. -/
def Tterm (a b c K k₁ k₃ α z : ℤ) : ℝ :=
  (-1) ^ z * factZ (a - α) * factZ (b - k₁ + α) * factZ (b + c - k₃ - K + α) * invFact α *
    invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) * invFact (c - K + k₁ - z) *
    invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z)

/-- The double sum `Σ_α Σ_z Tterm`, zero-extended over `ℤ`. By `sixJ_eq_const_mul_collapseSum`,
the recoupling coefficient at `M = J` is a constant times this sum. -/
def collapseSum (a b c K k₁ k₃ : ℤ) : ℝ := ∑ᶠ α : ℤ, ∑ᶠ z : ℤ, Tterm a b c K k₁ k₃ α z

/-- The constant of the explicit formula `sixJ = Cconst · collapseSum`:
`(-1)^(a+b+c-K) √(Δ₁ Δ₂ Δ₃ Δ₄) (a+b+c-K-k₁+1)! / ((a-k₁)! (b-k₁)! (a-K+k₃)! (b+c-K-k₃)!)`,
where `Δ₁ Δ₂ Δ₃ Δ₄` are the squares of Racah's `Δ` for the four triads of
`{j₁ j₂ j₁₂; j₃ J j₂₃}`. -/
def Cconst (a b c K k₁ k₃ : ℤ) : ℝ :=
  (-1) ^ (a + b + c - K) *
    Real.sqrt (triCoeff k₁ (a - k₁) (b - k₁) * triCoeff (a - K + k₃) (K - k₃) (b + c - K - k₃) *
      triCoeff k₃ (c - k₃) (b - k₃) * triCoeff (c - K + k₁) (K - k₁) (a + b - K - k₁)) *
    (factZ (a + b + c - K - k₁ + 1) * invFact (a - k₁) * invFact (b - k₁) * invFact (a - K + k₃) *
      invFact (b + c - K - k₃))

namespace SixJCollapse

/-!

## B. Top-weight Clebsch–Gordan coefficients

-/

/-- A `ℤ`-indexed zero-extended sum supported in `0 ≤ n ≤ N` is the finite sum over
`range (N + 1)`. -/
lemma finsum_int_eq_sum_range {F : ℤ → ℝ} (N : ℕ) (h : ∀ n : ℤ, ¬(0 ≤ n ∧ n ≤ N) → F n = 0) :
    ∑ᶠ n : ℤ, F n = ∑ n ∈ Finset.range (N + 1), F (n : ℤ) := by
  rw [finsum_eq_sum_of_support_subset F (s := (Finset.range (N + 1)).image (Nat.cast : ℕ → ℤ))]
  · rw [Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
  · intro n hn
    rw [Function.mem_support] at hn
    have : 0 ≤ n ∧ n ≤ N := by by_contra hc; exact hn (h n hc)
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨n.toNat, by omega, by omega⟩

lemma factZ_eq_factorial {u : ℤ} {t : ℕ} (h : u = t) : factZ u = (t.factorial : ℝ) := by
  rw [factZ, ite_eq_left (by omega), h, Int.toNat_natCast]

/-- `racahSum` on the top-weight diagonal `β = k - α` has a single term. -/
lemma racahSum_top {m n k α : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ k) :
    racahSum m n k α (k - α) =
      (-1) ^ α /
        ((α.factorial * (k - α).factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ) := by
  rw [racahSum, Finset.sum_eq_single α]
  · rw [ite_eq_left (by omega)]
    have h1 : n - (k - α) - α = n - k := by omega
    have h2 : m - k + α - α = m - k := by omega
    have h3 : k - α + α - k = 0 := by omega
    rw [h1, h2, h3]
    simp only [Nat.sub_self, Nat.factorial_zero, mul_one]
  · intro z _ hz
    rw [ite_eq_right]
    intro h
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma racahSum_eq_zero {m n k α β : ℕ}
    (h : ∀ z : ℕ, ¬(z ≤ α ∧ α ≤ m - k + z ∧ k ≤ β + z ∧ β + z ≤ n)) :
    racahSum m n k α β = 0 := by
  rw [racahSum]
  exact Finset.sum_eq_zero fun z _ => ite_eq_right_iff.mpr fun hz => absurd hz (h z)

/-- The normalisation `(N + 1)(m - k)!(n - k)! k! / (m + n - k + 1)!`, `N = m + n - 2k`, of
`cgCoefficient_racah`. -/
def cgNorm (m n k : ℕ) : ℝ :=
  (((m + n - 2 * k + 1) * (m - k).factorial * (n - k).factorial * k.factorial : ℕ) : ℝ) /
    ((m + n - k + 1).factorial : ℝ)

lemma cgNorm_nonneg (m n k : ℕ) : 0 ≤ cgNorm m n k := by
  unfold cgNorm
  positivity

/-- `cgCoefficient_racah`, with the normalisation `cgNorm`. -/
lemma cgCoefficient_racah' {m n k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) (h : α + β = k + l) :
    cgCoefficient m n k l α β =
      Real.sqrt (cgNorm m n k) * Real.sqrt (((m + n - 2 * k - l).factorial * l.factorial *
        α.factorial * (m - α).factorial * β.factorial * (n - β).factorial : ℕ) : ℝ) *
        racahSum m n k α β :=
  cgCoefficient_racah hkm hkn hl hα hβ h

/-- The top-weight Clebsch–Gordan coefficients `⟨m/2, m/2 - α; n/2, n/2 - (k - α) | J J⟩` have a
one-term Racah sum. -/
lemma cgCoefficient_top_racah {m n k α : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ k) :
    cgCoefficient m n k 0 α (k - α) =
      Real.sqrt (cgNorm m n k) *
        Real.sqrt (((m + n - 2 * k).factorial * α.factorial * (m - α).factorial *
          (k - α).factorial * (n - k + α).factorial : ℕ) : ℝ) *
        ((-1) ^ α /
          ((α.factorial * (k - α).factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ)) := by
  rw [cgCoefficient_racah hkm hkn (by omega) (by omega) (by omega) (by omega),
    racahSum_top hkm hkn hα, cgNorm]
  have h : n - (k - α) = n - k + α := by omega
  rw [h, Nat.sub_zero, Nat.factorial_zero, mul_one, mul_comm ((m + n - 2 * k).factorial) _]

/-- The coefficient `⟨m/2, m/2; n/2, n/2 - k | J J⟩` (`α = 0` of `cgCoefficient_top_racah`). -/
lemma cgCoefficient_top_racah_zero {m n k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    cgCoefficient m n k 0 0 k =
      Real.sqrt (cgNorm m n k) *
        Real.sqrt (((m + n - 2 * k).factorial * m.factorial * k.factorial *
          (n - k).factorial : ℕ) : ℝ) *
        (1 / ((k.factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ)) := by
  have h := cgCoefficient_top_racah (α := 0) hkm hkn (Nat.zero_le k)
  simp only [Nat.sub_zero, pow_zero, Nat.factorial_zero, mul_one, one_mul, Nat.add_zero] at h
  exact h

/-- Three products `√P √Q r`, whose `Q`-factors multiply to a constant times a square, combine. -/
lemma sqrt_combine {P₁ P₂ P₃ Q₁ Q₂ Q₃ Q w r₁ r₂ r₃ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hP₃ : 0 ≤ P₃) (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hQ : 0 ≤ Q) (hw : 0 ≤ w)
    (h : Q₁ * Q₂ * Q₃ = Q * w ^ 2) :
    (Real.sqrt P₁ * Real.sqrt Q₁ * r₁) * ((Real.sqrt P₂ * Real.sqrt Q₂ * r₂) *
      (Real.sqrt P₃ * Real.sqrt Q₃ * r₃)) =
        Real.sqrt (P₁ * P₂ * P₃ * Q) * w * (r₁ * r₂ * r₃) := by
  have hq : Real.sqrt Q₁ * Real.sqrt Q₂ * Real.sqrt Q₃ = Real.sqrt Q * w := by
    rw [← Real.sqrt_mul hQ₁, ← Real.sqrt_mul (mul_nonneg hQ₁ hQ₂), h, Real.sqrt_mul hQ,
      Real.sqrt_sq hw]
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hP₁ hP₂) hP₃), Real.sqrt_mul (mul_nonneg hP₁ hP₂),
    Real.sqrt_mul hP₁]
  linear_combination (Real.sqrt P₁ * Real.sqrt P₂ * Real.sqrt P₃ * r₁ * r₂ * r₃) * hq

/-- The constant of the reduction of the recoupling coefficient to a double sum: the square roots
of the three summed Clebsch–Gordan coefficients, collected into one. -/
def collapseConst (a b c K k₁ k₃ : ℕ) : ℝ :=
  Real.sqrt (cgNorm a b k₁ * cgNorm a (b + c - 2 * k₃) (K - k₃) * cgNorm b c k₃ *
      (((a + b - 2 * k₁).factorial * (a + b + c - 2 * K).factorial * (K - k₁).factorial *
        (c - (K - k₁)).factorial : ℕ) : ℝ)) /
    (((b - k₁).factorial * (a - k₁).factorial * (b + c - k₃ - K).factorial *
      (a - (K - k₃)).factorial : ℕ) : ℝ)

/-- The summand of the collapsed sum over `α`, with the `z`-sum still inside `racahSum`. -/
def collapseTerm (a b c K k₁ k₃ α : ℕ) : ℝ :=
  (((a - α).factorial * (b - k₁ + α).factorial * (b + c - k₃ - K + α).factorial : ℕ) : ℝ) /
    (α.factorial : ℝ) * racahSum b c k₃ (k₁ - α) (K - k₁)

/-- Each summand of the sum of products of the three Clebsch–Gordan coefficients is the constant
`collapseConst` times `collapseTerm`. -/
lemma cg_three_eq {a b c K k₁ k₃ α : ℕ} (ha : 0 < a) (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₃b : k₃ ≤ b) (hk₃c : k₃ ≤ c) (hk₁K : k₁ ≤ K) (hA₃ : K - k₁ ≤ c) (hk₃K : k₃ ≤ K)
    (hB₂ : K - k₃ ≤ a) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) (hα : α ≤ k₁) :
    cgCoefficient a b k₁ 0 α (k₁ - α) *
      (cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α (K - k₃ - α) *
        cgCoefficient b c k₃ (K - k₃ - α) (k₁ - α) (K - k₁)) =
      collapseConst a b c K k₁ k₃ * collapseTerm a b c K k₁ k₃ α := by
  by_cases hα4 : α ≤ K - k₃
  · rw [cgCoefficient_top_racah hk₁a hk₁b hα, cgCoefficient_top_racah hB₂ hB₃ hα4,
      cgCoefficient_racah' hk₃b hk₃c (by omega) (by omega) (by omega) (by omega)]
    have e1 : a + (b + c - 2 * k₃) - 2 * (K - k₃) = a + b + c - 2 * K := by omega
    have e2 : b + c - 2 * k₃ - (K - k₃ - α) = b + c - k₃ - K + α := by omega
    have e3 : b + c - 2 * k₃ - (K - k₃) + α = b + c - k₃ - K + α := by omega
    have e4 : b - (k₁ - α) = b - k₁ + α := by omega
    have e5 : b + c - 2 * k₃ - (K - k₃) = b + c - k₃ - K := by omega
    rw [e1, e2, e3, e4, e5, sqrt_combine (cgNorm_nonneg _ _ _) (cgNorm_nonneg _ _ _)
      (cgNorm_nonneg _ _ _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Q := (((a + b - 2 * k₁).factorial * (a + b + c - 2 * K).factorial *
        (K - k₁).factorial * (c - (K - k₁)).factorial : ℕ) : ℝ))
      (w := ((α.factorial * (a - α).factorial *
          (k₁ - α).factorial * (b - k₁ + α).factorial * (K - k₃ - α).factorial *
          (b + c - k₃ - K + α).factorial : ℕ) : ℝ)) ?_]
    · have hsq : (-1 : ℝ) ^ α * (-1) ^ α = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp
      rw [collapseConst, collapseTerm, div_mul_div_comm, hsq]
      push_cast
      field_simp
    · push_cast
      ring
  · rw [cgCoefficient_eq_zero_of_ne (by omega) hB₂ hB₃ (by omega), zero_mul, mul_zero,
      collapseTerm, racahSum_eq_zero (fun z hz => by omega), mul_zero, mul_zero]

/-!

## C. The weight rule

-/

/-- The weight rule collapses the triple sum over `(α, β, ν)` at `μ = 0`, `γ = K - k₁` to a single
sum over `α ≤ k₁`. -/
lemma sum_three_cg_eq {a b c K k₁ k₃ : ℕ} (ha : 0 < a) (hb : 0 < a + b) (hk₁a : k₁ ≤ a)
    (hk₁b : k₁ ≤ b) (hB₂ : K - k₃ ≤ a) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) :
    ∑ α ∈ Finset.range (a + 1), ∑ β ∈ Finset.range (b + 1),
      cgCoefficient a b k₁ 0 α β *
        ∑ ν ∈ Finset.range (b + c - 2 * k₃ + 1),
          cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α ν * cgCoefficient b c k₃ ν β (K - k₁) =
    ∑ α ∈ Finset.range (k₁ + 1), cgCoefficient a b k₁ 0 α (k₁ - α) *
      (cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α (K - k₃ - α) *
        cgCoefficient b c k₃ (K - k₃ - α) (k₁ - α) (K - k₁)) := by
  have hstep : ∀ α ∈ Finset.range (a + 1), ∑ β ∈ Finset.range (b + 1),
      cgCoefficient a b k₁ 0 α β *
        ∑ ν ∈ Finset.range (b + c - 2 * k₃ + 1),
          cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α ν * cgCoefficient b c k₃ ν β (K - k₁) =
    cgCoefficient a b k₁ 0 α (k₁ - α) *
      (cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α (K - k₃ - α) *
        cgCoefficient b c k₃ (K - k₃ - α) (k₁ - α) (K - k₁)) := fun α _ => by
    rw [Finset.sum_eq_single (k₁ - α)]
    · congr 1
      rw [Finset.sum_eq_single (K - k₃ - α)]
      · intro ν _ hν
        rw [cgCoefficient_eq_zero_of_ne (by omega) hB₂ hB₃ (by omega), zero_mul]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro β _ hβ
      rw [cgCoefficient_eq_zero_of_ne hb hk₁a hk₁b (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [Finset.sum_congr rfl hstep]
  symm
  refine Finset.sum_subset (fun α hα => ?_) fun α _ hα => ?_
  · rw [Finset.mem_range] at hα ⊢
    omega
  · rw [cgCoefficient_eq_zero_of_ne hb hk₁a hk₁b (by simp at hα; omega), zero_mul]

/-!

## D. The double sum as a finite sum

-/

lemma Tterm_eq {a b c K k₁ k₃ α z : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b) (hk₃b : k₃ ≤ b)
    (hk₁K : k₁ ≤ K) (hk₃K : k₃ ≤ K) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) (hα : α ≤ k₁)
    (hz : z ≤ k₃) :
    Tterm a b c K k₁ k₃ α z =
      (((a - α).factorial * (b - k₁ + α).factorial * (b + c - k₃ - K + α).factorial : ℕ) : ℝ) /
        (α.factorial : ℝ) *
      (if z ≤ k₁ - α ∧ k₁ - α ≤ b - k₃ + z ∧ k₃ ≤ K - k₁ + z ∧ K - k₁ + z ≤ c then
        (-1) ^ z / ((z.factorial * (k₃ - z).factorial * (k₁ - α - z).factorial *
          (c - (K - k₁) - z).factorial * (b - k₃ + z - (k₁ - α)).factorial *
          (K - k₁ + z - k₃).factorial : ℕ) : ℝ) else 0) := by
  by_cases hc : z ≤ k₁ - α ∧ k₁ - α ≤ b - k₃ + z ∧ k₃ ≤ K - k₁ + z ∧ K - k₁ + z ≤ c
  · rw [ite_eq_left hc, Tterm, factZ_eq_factorial (t := a - α) (by omega),
      factZ_eq_factorial (t := b - k₁ + α) (by omega),
      factZ_eq_factorial (t := b + c - k₃ - K + α) (by omega),
      invFact_eq (t := α) (by omega), invFact_eq (t := z) (by omega),
      invFact_eq (t := k₃ - z) (by omega), invFact_eq (t := k₁ - α - z) (by omega),
      invFact_eq (t := c - (K - k₁) - z) (by omega),
      invFact_eq (t := b - k₃ + z - (k₁ - α)) (by omega),
      invFact_eq (t := K - k₁ + z - k₃) (by omega), zpow_natCast]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv]
    ring
  · rw [ite_eq_right hc, mul_zero, Tterm]
    have h : ((k₁ : ℤ) - α - z < 0) ∨ ((b : ℤ) - k₁ - k₃ + z + α < 0) ∨
        ((K : ℤ) - k₁ - k₃ + z < 0) ∨ ((c : ℤ) - K + k₁ - z < 0) := by omega
    rcases h with h | h | h | h
    · rw [invFact_of_neg h]; ring
    · rw [invFact_of_neg h]; ring
    · rw [invFact_of_neg h]; ring
    · rw [invFact_of_neg h]; ring

/-- The double sum is the finite sum of the `collapseTerm`. -/
lemma collapseSum_eq_sum_collapseTerm {a b c K k₁ k₃ : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₃b : k₃ ≤ b) (hk₁K : k₁ ≤ K) (hk₃K : k₃ ≤ K) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) :
    collapseSum a b c K k₁ k₃ =
      ∑ α ∈ Finset.range (k₁ + 1), collapseTerm a b c K k₁ k₃ α := by
  have hin : ∀ α : ℤ, ∑ᶠ z : ℤ, Tterm a b c K k₁ k₃ α z =
      ∑ z ∈ Finset.range (k₃ + 1), Tterm a b c K k₁ k₃ α z := fun α => by
    refine finsum_int_eq_sum_range k₃ fun z hz => ?_
    rw [Tterm]
    rcases not_and_or.mp hz with h | h
    · rw [invFact_of_neg (by omega : (z : ℤ) < 0)]; ring
    · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring
  rw [collapseSum, finsum_congr hin]
  rw [finsum_int_eq_sum_range k₁ fun α hα => ?_]
  · refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : α ≤ k₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hα)
    rw [collapseTerm, racahSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    exact Tterm_eq hk₁a hk₁b hk₃b hk₁K hk₃K hB₃ hα' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hz))
  · refine Finset.sum_eq_zero fun z hz => ?_
    rw [Tterm]
    rcases not_and_or.mp hα with h | h
    · rw [invFact_of_neg (by omega : (α : ℤ) < 0)]; ring
    · have hz' : (z : ℤ) ≥ 0 := by simp
      rw [invFact_of_neg (by omega : (k₁ : ℤ) - α - z < 0)]; ring

/-!

## E. The constant

-/

/-- The four `Δ²` of Racah's formula for `{j₁ j₂ j₁₂; j₃ J j₂₃}`, in natural-number form. -/
def racahDelta (a b c K k₁ k₃ : ℕ) : ℝ :=
  ((k₁.factorial * (a - k₁).factorial * (b - k₁).factorial : ℕ) : ℝ) /
      ((a + b - k₁ + 1).factorial : ℝ) *
    (((a - (K - k₃)).factorial * (K - k₃).factorial * (b + c - k₃ - K).factorial : ℕ) : ℝ) /
      ((a + b + c - K - k₃ + 1).factorial : ℝ) *
    (((k₃.factorial * (c - k₃).factorial * (b - k₃).factorial : ℕ) : ℝ) /
      ((b + c - k₃ + 1).factorial : ℝ)) *
    ((((c - (K - k₁)).factorial * (K - k₁).factorial * (a + b - K - k₁).factorial : ℕ) : ℝ) /
      ((a + b + c - K - k₁ + 1).factorial : ℝ))

lemma racahDelta_nonneg (a b c K k₁ k₃ : ℕ) : 0 ≤ racahDelta a b c K k₁ k₃ := by
  unfold racahDelta
  positivity

/-- The constant `collapseConst`, divided by the top-weight coefficient and by
`√((e + 1)(f + 1))`, is the Racah constant. -/
lemma collapseConst_div {a b c K k₁ k₃ : ℕ} (hA₂ : K - k₁ ≤ a + b - 2 * k₁) (hA₃ : K - k₁ ≤ c)
    (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b) (hk₃b : k₃ ≤ b) (hk₃c : k₃ ≤ c) (hk₁K : k₁ ≤ K)
    (hk₃K : k₃ ≤ K) (hB₂ : K - k₃ ≤ a) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) :
    collapseConst a b c K k₁ k₃ /
        (cgCoefficient (a + b - 2 * k₁) c (K - k₁) 0 0 (K - k₁) *
          Real.sqrt (((a + b - 2 * k₁ + 1 : ℕ) : ℝ) * ((b + c - 2 * k₃ + 1 : ℕ) : ℝ))) =
      Real.sqrt (racahDelta a b c K k₁ k₃) * ((a + b + c - K - k₁ + 1).factorial : ℝ) /
        (((a - k₁).factorial * (b - k₁).factorial * (a - (K - k₃)).factorial *
          (b + c - k₃ - K).factorial : ℕ) : ℝ) := by
  have hpos := cgCoefficient_top_pos (m := a + b - 2 * k₁) (n := c) (k := K - k₁) hA₂ hA₃
  have hE : (0 : ℝ) < ((a + b - 2 * k₁ + 1 : ℕ) : ℝ) * ((b + c - 2 * k₃ + 1 : ℕ) : ℝ) := by
    positivity
  have hL : 0 ≤ collapseConst a b c K k₁ k₃ /
        (cgCoefficient (a + b - 2 * k₁) c (K - k₁) 0 0 (K - k₁) *
          Real.sqrt (((a + b - 2 * k₁ + 1 : ℕ) : ℝ) * ((b + c - 2 * k₃ + 1 : ℕ) : ℝ))) := by
    unfold collapseConst
    positivity
  have hR : 0 ≤ Real.sqrt (racahDelta a b c K k₁ k₃) *
        ((a + b + c - K - k₁ + 1).factorial : ℝ) /
        (((a - k₁).factorial * (b - k₁).factorial * (a - (K - k₃)).factorial *
          (b + c - k₃ - K).factorial : ℕ) : ℝ) := by positivity
  refine (pow_left_inj₀ hL hR two_ne_zero).mp ?_
  rw [div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hE.le,
    Real.sq_sqrt (racahDelta_nonneg _ _ _ _ _ _), collapseConst, div_pow,
    Real.sq_sqrt (by unfold cgNorm; positivity), cgCoefficient_top_racah_zero hA₂ hA₃, mul_pow,
    mul_pow, Real.sq_sqrt (cgNorm_nonneg _ _ _), Real.sq_sqrt (Nat.cast_nonneg _)]
  unfold racahDelta cgNorm
  have e1 : a + (b + c - 2 * k₃) - 2 * (K - k₃) = a + b + c - 2 * K := by omega
  have e1' : a + b - 2 * k₁ + c - 2 * (K - k₁) = a + b + c - 2 * K := by omega
  have e2 : b + c - 2 * k₃ - (K - k₃) = b + c - k₃ - K := by omega
  have e3 : a + (b + c - 2 * k₃) - (K - k₃) + 1 = a + b + c - K - k₃ + 1 := by omega
  have e4 : a + b - 2 * k₁ + c - (K - k₁) + 1 = a + b + c - K - k₁ + 1 := by omega
  have e5 : a + b - 2 * k₁ - (K - k₁) = a + b - K - k₁ := by omega
  simp only [e1, e1', e2, e3, e4, e5]
  push_cast
  field_simp

lemma triCoeff_nat {x y z : ℤ} {p q r s : ℕ} (hx : x = p) (hy : y = q) (hz : z = r)
    (hs : x + y + z + 1 = s) :
    triCoeff x y z = ((p.factorial * q.factorial * r.factorial : ℕ) : ℝ) / (s.factorial : ℝ) := by
  rw [triCoeff, factZ_eq_factorial hx, factZ_eq_factorial hy, factZ_eq_factorial hz,
    invFact_eq hs]
  push_cast
  ring

/-- `Cconst` on natural-number data. -/
lemma Cconst_eq {a b c K k₁ k₃ : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b) (hk₃b : k₃ ≤ b)
    (hk₃c : k₃ ≤ c) (hk₁K : k₁ ≤ K) (hA₂ : K - k₁ ≤ a + b - 2 * k₁) (hA₃ : K - k₁ ≤ c)
    (hk₃K : k₃ ≤ K) (hB₂ : K - k₃ ≤ a) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) :
    Cconst a b c K k₁ k₃ = (-1) ^ (a + b + c - K) *
      (Real.sqrt (racahDelta a b c K k₁ k₃) * ((a + b + c - K - k₁ + 1).factorial : ℝ) /
        (((a - k₁).factorial * (b - k₁).factorial * (a - (K - k₃)).factorial *
          (b + c - k₃ - K).factorial : ℕ) : ℝ)) := by
  have hexp : ((a : ℤ) + b + c - K) = ((a + b + c - K : ℕ) : ℤ) := by omega
  have hD : triCoeff (k₁ : ℤ) (a - k₁) (b - k₁) *
      triCoeff ((a : ℤ) - K + k₃) (K - k₃) (b + c - K - k₃) *
      triCoeff (k₃ : ℤ) (c - k₃) (b - k₃) * triCoeff ((c : ℤ) - K + k₁) (K - k₁) (a + b - K - k₁) =
      racahDelta a b c K k₁ k₃ := by
    rw [triCoeff_nat (p := k₁) (q := a - k₁) (r := b - k₁) (s := a + b - k₁ + 1) (by omega)
        (by omega) (by omega) (by omega),
      triCoeff_nat (p := a - (K - k₃)) (q := K - k₃) (r := b + c - k₃ - K)
        (s := a + b + c - K - k₃ + 1) (by omega) (by omega) (by omega) (by omega),
      triCoeff_nat (p := k₃) (q := c - k₃) (r := b - k₃) (s := b + c - k₃ + 1) (by omega)
        (by omega) (by omega) (by omega),
      triCoeff_nat (p := c - (K - k₁)) (q := K - k₁) (r := a + b - K - k₁)
        (s := a + b + c - K - k₁ + 1) (by omega) (by omega) (by omega) (by omega)]
    unfold racahDelta
    ring
  rw [Cconst, hD, hexp, zpow_natCast, factZ_eq_factorial (t := a + b + c - K - k₁ + 1) (by omega),
    invFact_eq (t := a - k₁) (by omega), invFact_eq (t := b - k₁) (by omega),
    invFact_eq (t := a - (K - k₃)) (by omega), invFact_eq (t := b + c - k₃ - K) (by omega)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

end SixJCollapse

/-!

## F. The explicit formula

-/

open SixJCollapse in
/-- **The 6j symbol of `SixJ` as a double sum.** For `0 < a`, `0 < c` and admissible `k₁`, `k₃`,
`K` (`ValidA`, `ValidB`; `k₁ ≤ min a b`, `k₃ ≤ min b c` are the `Fin` bounds),
`{j₁ j₂ j₁₂; j₃ J j₂₃} = Cconst · collapseSum`. The cases `a = 0` and `c = 0` are not covered
(`sixJ_eq_sixJSym` has the same hypotheses). -/
theorem sixJ_eq_const_mul_collapseSum {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ = Cconst a b c K k₁ k₃ * collapseSum a b c K k₁ k₃ := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hproj := sum_cgCoefficient_mul_eq_recoupling hab hbc ha hc ⟨hA1, hA2, hA3⟩
    ⟨hB1, hB2, hB3⟩ 0 (K - k₁)
  rw [sum_three_cg_eq ha hab (by omega) (by omega) hB2 hB3,
    Finset.sum_congr rfl fun α hα => cg_three_eq ha (by omega) (by omega) (by omega) (by omega)
      hA1 hA3 hB1 hB2 hB3 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hα)),
    ← Finset.mul_sum,
    ← collapseSum_eq_sum_collapseTerm (by omega) (by omega) (by omega) hA1 hB1 hB3] at hproj
  have hpos := cgCoefficient_top_pos (m := a + b - 2 * (k₁ : ℕ)) (n := c) (k := K - k₁) hA2 hA3
  have hR : recoupling hab hbc K 0 k₁ k₃ = collapseConst a b c K k₁ k₃ *
      collapseSum a b c K k₁ k₃ / cgCoefficient (a + b - 2 * (k₁ : ℕ)) c (K - k₁) 0 0 (K - k₁) := by
    rw [eq_div_iff hpos.ne']
    exact hproj.symm
  have hE : 0 < Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) *
      ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  rw [sixJ, ite_eq_left ⟨⟨hA1, hA2, hA3⟩, ⟨hB1, hB2, hB3⟩⟩, hR,
    Cconst_eq (by omega) (by omega) (by omega) (by omega) hA1 hA2 hA3 hB1 hB2 hB3,
    ← collapseConst_div hA2 hA3 (by omega) (by omega) (by omega) (by omega) hA1 hB1 hB2 hB3]
  field_simp

end PhyslibAlpha.Sl2
