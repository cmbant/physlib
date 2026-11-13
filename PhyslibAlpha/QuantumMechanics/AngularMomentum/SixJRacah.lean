/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!

# Racah's closed formula for the 6j symbols (PROTOTYPE, scoping only)

Racah's single-sum formula for `{j₁ j₂ j₃; j₄ j₅ j₆}`, stated for `sixJSym` and for the `sixJ` of
`SixJ`, with the reductions between the two. The analytic core `sixJSym_eq_racah` is NOT proved
here (it is the only `sorry`); everything else is.

## i. Overview

All spins are doubled naturals, as in `SixJ` and `SixJSymmetry`. With `j₁ = a/2`, `j₂ = b/2`,
`j₃ = c/2`, `j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃`, `J = (a + b + c)/2 - K`, the four
triads `(j₁ j₂ j₁₂)`, `(j₁ J j₂₃)`, `(j₃ j₂ j₂₃)`, `(j₃ J j₁₂)` have integer half-perimeters

`α₁ = a + b - k₁`, `α₂ = a + b + c - K - k₃`, `α₃ = b + c - k₃`, `α₄ = a + b + c - K - k₁`,

and the three quadrilateral sums are

`β₁ = a + b + c - K`, `β₂ = a + 2b + c - k₁ - K - k₃`, `β₃ = a + b + c - k₁ - k₃`.

Racah's formula (DLMF 34.4.2) reads

`{j₁ j₂ j₁₂; j₃ J j₂₃} = Δ(j₁ j₂ j₁₂) Δ(j₁ J j₂₃) Δ(j₃ j₂ j₂₃) Δ(j₃ J j₁₂) ·
  Σ_t (-1)^t (t + 1)! / ((t - α₁)! (t - α₂)! (t - α₃)! (t - α₄)! (β₁ - t)! (β₂ - t)! (β₃ - t)!)`,

`Δ(j₁ j₂ j₃)² = (j₁ + j₂ - j₃)! (j₁ - j₂ + j₃)! (-j₁ + j₂ + j₃)! / (j₁ + j₂ + j₃ + 1)!`.

Note that `sixSum` of `Wigner3j` is the six-factorial sum of the 3j symbol, not Racah's 6j sum
(which has seven factorials and the numerator `(t + 1)!`).

## ii. Key results

- `racahSum6`, `triCoeff`: Racah's sum and `Δ²`, zero-extended.
- `sixJSym_eq_zero_of_odd`: `sixJSym` vanishes unless all four triads have even perimeter.
- `sixJ_eq_racah` and `sixJ_eq_racah_of_sixJSym`: the formula for `sixJ`, from `sixJSym_eq_racah`.
- `sixJSym_eq_racah`: Racah's formula for `sixJSym` (open).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-- `n!` for `n ≥ 0` and `0` for `n < 0`. -/
def factZ (u : ℤ) : ℝ := if 0 ≤ u then ((u.toNat.factorial : ℝ)) else 0

/-- The square of Racah's `Δ`, `x! y! z! / (x + y + z + 1)!`, where `x, y, z` are the three
integers `j₁ + j₂ - j₃`, `j₁ - j₂ + j₃`, `-j₁ + j₂ + j₃` of a triad (zero unless all are `≥ 0`). -/
def triCoeff (x y z : ℤ) : ℝ := factZ x * factZ y * factZ z * invFact (x + y + z + 1)

/-- Racah's sum `Σ_t (-1)^t (t + 1)! / ∏ (t - αᵢ)! ∏ (βⱼ - t)!`, over the `t` for which all seven
arguments are nonnegative. -/
def racahSum6 (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) : ℝ :=
  ∑ᶠ t : ℤ, (-1 : ℝ) ^ t * factZ (t + 1) *
    (invFact (t - α₁) * invFact (t - α₂) * invFact (t - α₃) * invFact (t - α₄) *
      (invFact (β₁ - t) * invFact (β₂ - t) * invFact (β₃ - t)))

/-- `Δ²` of the triad `(j₁ j₂ j₃)` in doubled units (a half-integer `x/2` only enters through the
integers `(x + y - z)/2`, which are exact for even perimeter). -/
def triD (j₁ j₂ j₃ : ℕ) : ℝ :=
  triCoeff (((j₁ : ℤ) + j₂ - j₃) / 2) (((j₁ : ℤ) - j₂ + j₃) / 2) ((-(j₁ : ℤ) + j₂ + j₃) / 2)

/-- Racah's right-hand side for `{j₁ j₂ j₃; j₄ j₅ j₆}` in doubled units. -/
def racah6j (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  Real.sqrt (triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃) *
    racahSum6 (((j₁ : ℤ) + j₂ + j₃) / 2) (((j₁ : ℤ) + j₅ + j₆) / 2) (((j₄ : ℤ) + j₂ + j₆) / 2)
      (((j₄ : ℤ) + j₅ + j₃) / 2) (((j₁ : ℤ) + j₂ + j₄ + j₅) / 2) (((j₂ : ℤ) + j₃ + j₅ + j₆) / 2)
      (((j₃ : ℤ) + j₁ + j₆ + j₄) / 2)

section Reductions

lemma racahSum6_eq_sum (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) :
    racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ =
      ∑ t ∈ Finset.Icc (max (max α₁ α₂) (max α₃ α₄)) (min β₁ (min β₂ β₃)),
        (-1 : ℝ) ^ t * factZ (t + 1) *
          (invFact (t - α₁) * invFact (t - α₂) * invFact (t - α₃) * invFact (t - α₄) *
            (invFact (β₁ - t) * invFact (β₂ - t) * invFact (β₃ - t))) := by
  rw [racahSum6]
  refine finsum_eq_sum_of_support_subset _ fun t ht => ?_
  rw [Function.mem_support] at ht
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hcon
  apply ht
  have h : t < α₁ ∨ t < α₂ ∨ t < α₃ ∨ t < α₄ ∨ β₁ < t ∨ β₂ < t ∨ β₃ < t := by omega
  rcases h with h | h | h | h | h | h | h
  · rw [invFact_of_neg (by omega : t - α₁ < 0)]; ring
  · rw [invFact_of_neg (by omega : t - α₂ < 0)]; ring
  · rw [invFact_of_neg (by omega : t - α₃ < 0)]; ring
  · rw [invFact_of_neg (by omega : t - α₄ < 0)]; ring
  · rw [invFact_of_neg (by omega : β₁ - t < 0)]; ring
  · rw [invFact_of_neg (by omega : β₂ - t < 0)]; ring
  · rw [invFact_of_neg (by omega : β₃ - t < 0)]; ring

variable {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}

/-- `sixJSym` vanishes unless all four triads have even perimeter. -/
lemma sixJSym_eq_zero_of_odd
    (h : ¬((j₁ + j₂ + j₃) % 2 = 0 ∧ (j₁ + j₅ + j₆) % 2 = 0 ∧ (j₄ + j₂ + j₆) % 2 = 0 ∧
      (j₄ + j₅ + j₃) % 2 = 0)) : sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [sixJTerm]
  by_cases h1 : (j₁ + j₂ + j₃) % 2 = 0
  · by_cases h2 : (j₁ + j₅ + j₆) % 2 = 0
    · by_cases h3 : (j₄ + j₂ + j₆) % 2 = 0
      · have h4 : ¬(j₄ + j₅ + j₃) % 2 = 0 := fun h4 => h ⟨h1, h2, h3, h4⟩
        rw [threeJ_of_not (fun hh => h4 hh.2.2.2.2.2.2.2.2.2.2.2.2.2), mul_zero, mul_zero]
      · rw [threeJ_of_not (fun hh => h3 hh.2.2.2.2.2.2.2.2.2.2.2.2.2)]; ring
    · rw [threeJ_of_not (fun hh => h2 hh.2.2.2.2.2.2.2.2.2.2.2.2.2)]; ring
  · rw [threeJ_of_not (fun hh => h1 hh.2.2.2.2.2.2.2.2.2.2.2.2.2)]; ring

end Reductions

/-- **Racah's formula for the 6j symbol** `{j₁ j₂ j₃; j₄ j₅ j₆}` (doubled units), as the sum over
four 3j symbols `sixJSym`. OPEN: this is the bridge theorem. -/
theorem sixJSym_eq_racah (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (h₁ : (j₁ + j₂ + j₃) % 2 = 0)
    (h₂ : (j₁ + j₅ + j₆) % 2 = 0) (h₃ : (j₄ + j₂ + j₆) % 2 = 0) (h₄ : (j₄ + j₅ + j₃) % 2 = 0) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  sorry

/-- Racah's formula for the 6j symbol of `SixJ`, in terms of the data `a b c K k₁ k₃`
(`j₁ = a/2`, `j₂ = b/2`, `j₃ = c/2`, `j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃`,
`J = (a + b + c)/2 - K`), given Racah's formula for `sixJSym`. -/
theorem sixJ_eq_racah_of_sixJSym {a b c : ℕ}
    (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c) {K : ℕ}
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ =
      racah6j a b (a + b - 2 * (k₁ : ℕ)) c (a + b + c - 2 * K) (b + c - 2 * (k₃ : ℕ)) := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  rw [sixJ_eq_sixJSym hab hbc ha hc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩]
  exact sixJSym_eq_racah _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)

/-- **Racah's closed formula for `sixJ`**, in the natural parameters of `SixJ`:
`{j₁ j₂ j₁₂; j₃ J j₂₃} = Δ₁ Δ₂ Δ₃ Δ₄ Σ_t (-1)^t (t + 1)! / (...)`, with `Δᵢ²` and the seven
arguments given explicitly. -/
theorem sixJ_eq_racah {a b c : ℕ}
    (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c) {K : ℕ}
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ =
      Real.sqrt (triCoeff k₁ ((a : ℤ) - k₁) ((b : ℤ) - k₁) *
          triCoeff ((a : ℤ) - K + k₃) ((K : ℤ) - k₃) ((b : ℤ) + c - K - k₃) *
          triCoeff k₃ ((c : ℤ) - k₃) ((b : ℤ) - k₃) *
          triCoeff ((c : ℤ) - K + k₁) ((K : ℤ) - k₁) ((a : ℤ) + b - K - k₁)) *
        racahSum6 ((a : ℤ) + b - k₁) ((a : ℤ) + b + c - K - k₃) ((b : ℤ) + c - k₃)
          ((a : ℤ) + b + c - K - k₁) ((a : ℤ) + b + c - K)
          ((a : ℤ) + 2 * b + c - k₁ - K - k₃) ((a : ℤ) + b + c - k₁ - k₃) := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have e3 : ∀ x y z x' y' z' : ℤ, x = x' → y = y' → z = z' → triCoeff x y z = triCoeff x' y' z' := by
    intro x y z x' y' z' hx hy hz
    subst hx hy hz
    rfl
  have e7 : ∀ α₁ α₂ α₃ α₄ β₁ β₂ β₃ α₁' α₂' α₃' α₄' β₁' β₂' β₃' : ℤ, α₁ = α₁' → α₂ = α₂' →
      α₃ = α₃' → α₄ = α₄' → β₁ = β₁' → β₂ = β₂' → β₃ = β₃' →
      racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ = racahSum6 α₁' α₂' α₃' α₄' β₁' β₂' β₃' := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
    subst h1 h2 h3 h4 h5 h6 h7
    rfl
  have t1 : triD a b (a + b - 2 * (k₁ : ℕ)) = triCoeff k₁ ((a : ℤ) - k₁) ((b : ℤ) - k₁) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t2 : triD a (a + b + c - 2 * K) (b + c - 2 * (k₃ : ℕ)) =
      triCoeff ((a : ℤ) - K + k₃) ((K : ℤ) - k₃) ((b : ℤ) + c - K - k₃) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t3 : triD c b (b + c - 2 * (k₃ : ℕ)) = triCoeff k₃ ((c : ℤ) - k₃) ((b : ℤ) - k₃) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t4 : triD c (a + b + c - 2 * K) (a + b - 2 * (k₁ : ℕ)) =
      triCoeff ((c : ℤ) - K + k₁) ((K : ℤ) - k₁) ((a : ℤ) + b - K - k₁) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  rw [sixJ_eq_racah_of_sixJSym hab hbc ha hc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩, racah6j, t1, t2, t3,
    t4]
  congr 1
  exact e7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

end PhyslibAlpha.Sl2
