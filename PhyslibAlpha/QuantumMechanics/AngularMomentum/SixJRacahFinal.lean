/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacahSix
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJXsFormula
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacah
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!

# Racah's formula for the 6j symbol

The bridge between the operator-defined `sixJ` and Racah's closed formula, without the open
`sixJSym_eq_racah` of `SixJRacah`.

## i. Overview

1. In the region `R1 : k₁ + k₃ ≤ min b K` (the third column of `{a b e; c g f}` has maximal sum),
   `sixJ_eq_const_mul_Xs` and the six-parameter identity `Xs_eq_racah_six` (`SixJRacahSix`) give
   `sixJ_eq_racah_R1`, Racah's formula for `sixJ` in `sixJ_eq_racah`'s explicit shape.
2. The right-hand side `racah6j` and `sixJSym` are invariant under permutations of the columns
   (`racah6j_swap₁₂`, `racah6j_swap₂₃`; `sixJSym_swap₁₂`, `sixJSym_swap₂₃`). Moving the column of
   maximal sum to the third place, and a column with two positive entries to the first,
   covers every admissible tuple with `j₁ > 0` and `j₄ > 0` (`sixJSym_eq_racah6j`).
3. `sixJ_eq_racah6j` and `sixJ_eq_racah_explicit` are the bridge theorem in the natural parameters
   of `SixJ`. They need `0 < a` and `0 < c`, like `sixJ_eq_racah` and `sixJ_eq_const_mul_Xs`.

## ii. Key results

- `sixJ_eq_racah6j`: `sixJ = racah6j a b (a+b-2k₁) c (a+b+c-2K) (b+c-2k₃)`.
- `sixJ_eq_racah_explicit`: the same, with the four `Δ²` and the seven arguments written out.
- `sixJSym_eq_racah6j`: Racah's formula for `sixJSym` on admissible tuples with `j₁, j₄ > 0`.

Nothing here depends on `sixJSym_eq_racah`.

-/

@[expose] public section

noncomputable section

open Finset PhyslibAlpha.Sl2.Hyper

namespace PhyslibAlpha.Sl2

lemma factZ_cast {e : ℤ} {n : ℕ} (h : e = n) : factZ e = (n.factorial : ℝ) := by
  rw [h]; exact Collapse.factZ_natCast n

lemma invFact_cast {e : ℤ} {n : ℕ} (h : e = n) : invFact e = ((n.factorial : ℝ))⁻¹ := by
  rw [h]; exact invFact_natCast n

lemma racahSum6_congr {α₁ α₂ α₃ α₄ β₁ β₂ β₃ α₁' α₂' α₃' α₄' β₁' β₂' β₃' : ℤ} (h1 : α₁ = α₁')
    (h2 : α₂ = α₂') (h3 : α₃ = α₃') (h4 : α₄ = α₄') (h5 : β₁ = β₁') (h6 : β₂ = β₂') (h7 : β₃ = β₃') :
    racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ = racahSum6 α₁' α₂' α₃' α₄' β₁' β₂' β₃' := by
  subst h1 h2 h3 h4 h5 h6 h7; rfl

/-- The collapse identity in the six free parameters, in the form of `sixJ_eq_const_mul_Xs`. -/
theorem sixJ_six (k1 k3 u v w z : ℕ) :
    Cconst ((v + w + k1 : ℕ) : ℤ) ((z + k1 + k3 : ℕ) : ℤ) ((u + w + k3 : ℕ) : ℤ) ((w + k1 + k3 : ℕ) : ℤ)
        k1 k3 *
      (Xs ((v + w + k1 : ℕ) : ℤ) ((z + k1 + k3 : ℕ) : ℤ) ((u + w + k3 : ℕ) : ℤ) ((w + k1 + k3 : ℕ) : ℤ)
          k1 k3 *
        factZ (((z + k1 + k3 : ℕ) : ℤ) + ((u + w + k3 : ℕ) : ℤ) - k3 - ((w + k1 + k3 : ℕ) : ℤ)) /
        (factZ (((u + w + k3 : ℕ) : ℤ) - ((w + k1 + k3 : ℕ) : ℤ) + k1) * factZ k3 *
          factZ (((z + k1 + k3 : ℕ) : ℤ) - k3) * factZ (((u + w + k3 : ℕ) : ℤ) - k3))) =
    Real.sqrt (triCoeff k1 (((v + w + k1 : ℕ) : ℤ) - k1) (((z + k1 + k3 : ℕ) : ℤ) - k1) *
          triCoeff (((v + w + k1 : ℕ) : ℤ) - ((w + k1 + k3 : ℕ) : ℤ) + k3)
            (((w + k1 + k3 : ℕ) : ℤ) - k3)
            (((z + k1 + k3 : ℕ) : ℤ) + ((u + w + k3 : ℕ) : ℤ) - ((w + k1 + k3 : ℕ) : ℤ) - k3) *
          triCoeff k3 (((u + w + k3 : ℕ) : ℤ) - k3) (((z + k1 + k3 : ℕ) : ℤ) - k3) *
          triCoeff (((u + w + k3 : ℕ) : ℤ) - ((w + k1 + k3 : ℕ) : ℤ) + k1)
            (((w + k1 + k3 : ℕ) : ℤ) - k1)
            (((v + w + k1 : ℕ) : ℤ) + ((z + k1 + k3 : ℕ) : ℤ) - ((w + k1 + k3 : ℕ) : ℤ) - k1)) *
      racahSum6 (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - u) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k3)
          (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - v) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k1)
          ((u + v + w + z + k1 + k3 : ℕ) : ℤ) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + z)
          (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + w) := by
  rw [Xs_eq_racah_six]
  unfold Cconst
  have hpow : (-1 : ℝ) ^ (((v + w + k1 : ℕ) : ℤ) + ((z + k1 + k3 : ℕ) : ℤ) + ((u + w + k3 : ℕ) : ℤ) -
      ((w + k1 + k3 : ℕ) : ℤ)) = (-1) ^ (u + v + w + z + k1 + k3) := by
    rw [show ((v + w + k1 : ℕ) : ℤ) + ((z + k1 + k3 : ℕ) : ℤ) + ((u + w + k3 : ℕ) : ℤ) -
      ((w + k1 + k3 : ℕ) : ℤ) = ((u + v + w + z + k1 + k3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hpow, factZ_cast (n := u + v + w + z + k3 + 1) (by push_cast; ring),
    invFact_cast (n := v + w) (by push_cast; ring), invFact_cast (n := z + k3) (by push_cast; ring),
    invFact_cast (n := v) (by push_cast; ring), invFact_cast (n := u + z) (by push_cast; ring),
    factZ_cast (n := u + z) (by push_cast; ring), factZ_cast (n := u) (by push_cast; ring),
    factZ_cast (n := k3) rfl, factZ_cast (n := z + k1) (by push_cast; ring),
    factZ_cast (n := u + w) (by push_cast; ring)]
  simp only [CxF]
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  rcases neg_one_pow_eq_or ℝ (u + v + w + z + k1 + k3) with h | h <;> rw [h] <;> field_simp


/-- Racah's formula for the operator-defined `sixJ`, in the region `k₁ + k₃ ≤ min b K`
(where `β₁ = a + b + c - K` is the smallest of the quadrilateral sums). -/
theorem sixJ_eq_racah_R1 {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) (hR1 : (k₁ : ℕ) + k₃ ≤ b ∧ (k₁ : ℕ) + k₃ ≤ K) :
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
  obtain ⟨hR1, hR2⟩ := hR1
  rw [sixJ_eq_const_mul_Xs hab hbc ha hc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩]
  generalize (k₁ : ℕ) = p at hk₁ hA1 hA2 hA3 hR1 hR2 ⊢
  generalize (k₃ : ℕ) = q at hk₃ hB1 hB2 hB3 hR1 hR2 ⊢
  obtain ⟨w, hw⟩ : ∃ w, K = w + p + q := ⟨K - p - q, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, b = z + p + q := ⟨b - p - q, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, c = u + w + q := ⟨c - w - q, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, a = v + w + p := ⟨a - w - p, by omega⟩
  subst hw hz hu hv
  rw [sixJ_six]
  congr 1
  apply racahSum6_congr <;> push_cast <;> ring

/-! ### Racah's formula in the tuple form, region `R1` -/

/-- `racah6j` in the explicit form of `sixJ_eq_racah`. -/
lemma racah6j_eq_explicit {a b c K k₁ k₃ : ℕ} (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b) (hk₃b : k₃ ≤ b)
    (hk₃c : k₃ ≤ c) (hA1 : k₁ ≤ K) (hA2 : K - k₁ ≤ a + b - 2 * k₁) (_hA3 : K - k₁ ≤ c)
    (hB1 : k₃ ≤ K) (hB2 : K - k₃ ≤ a) (hB3 : K - k₃ ≤ b + c - 2 * k₃) :
    racah6j a b (a + b - 2 * k₁) c (a + b + c - 2 * K) (b + c - 2 * k₃) =
      Real.sqrt (triCoeff k₁ ((a : ℤ) - k₁) ((b : ℤ) - k₁) *
          triCoeff ((a : ℤ) - K + k₃) ((K : ℤ) - k₃) ((b : ℤ) + c - K - k₃) *
          triCoeff k₃ ((c : ℤ) - k₃) ((b : ℤ) - k₃) *
          triCoeff ((c : ℤ) - K + k₁) ((K : ℤ) - k₁) ((a : ℤ) + b - K - k₁)) *
        racahSum6 ((a : ℤ) + b - k₁) ((a : ℤ) + b + c - K - k₃) ((b : ℤ) + c - k₃)
          ((a : ℤ) + b + c - K - k₁) ((a : ℤ) + b + c - K)
          ((a : ℤ) + 2 * b + c - k₁ - K - k₃) ((a : ℤ) + b + c - k₁ - k₃) := by
  have e3 : ∀ x y z x' y' z' : ℤ, x = x' → y = y' → z = z' → triCoeff x y z = triCoeff x' y' z' := by
    intro x y z x' y' z' hx hy hz
    subst hx hy hz
    rfl
  have t1 : triD a b (a + b - 2 * k₁) = triCoeff k₁ ((a : ℤ) - k₁) ((b : ℤ) - k₁) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t2 : triD a (a + b + c - 2 * K) (b + c - 2 * k₃) =
      triCoeff ((a : ℤ) - K + k₃) ((K : ℤ) - k₃) ((b : ℤ) + c - K - k₃) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t3 : triD c b (b + c - 2 * k₃) = triCoeff k₃ ((c : ℤ) - k₃) ((b : ℤ) - k₃) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have t4 : triD c (a + b + c - 2 * K) (a + b - 2 * k₁) =
      triCoeff ((c : ℤ) - K + k₁) ((K : ℤ) - k₁) ((a : ℤ) + b - K - k₁) := by
    unfold triD; exact e3 _ _ _ _ _ _ (by omega) (by omega) (by omega)
  rw [racah6j, t1, t2, t3, t4]
  congr 1
  exact racahSum6_congr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-! ### Column symmetry of `racah6j` -/

lemma triCoeff_swap₂₃ (x y z : ℤ) : triCoeff x z y = triCoeff x y z := by
  unfold triCoeff; rw [show x + z + y + 1 = x + y + z + 1 by ring]; ring

lemma triCoeff_swap₁₂ (x y z : ℤ) : triCoeff y x z = triCoeff x y z := by
  unfold triCoeff; rw [show y + x + z + 1 = x + y + z + 1 by ring]; ring

lemma triD_swap₁₂ (j₁ j₂ j₃ : ℕ) : triD j₂ j₁ j₃ = triD j₁ j₂ j₃ := by
  unfold triD
  rw [show (((j₂ : ℤ) + j₁ - j₃) / 2) = ((j₁ : ℤ) + j₂ - j₃) / 2 by omega,
    show (((j₂ : ℤ) - j₁ + j₃) / 2) = ((-(j₁ : ℤ) + j₂ + j₃) / 2) by omega,
    show ((-(j₂ : ℤ) + j₁ + j₃) / 2) = (((j₁ : ℤ) - j₂ + j₃) / 2) by omega, triCoeff_swap₂₃]

lemma triD_swap₂₃ (j₁ j₂ j₃ : ℕ) : triD j₁ j₃ j₂ = triD j₁ j₂ j₃ := by
  unfold triD
  rw [show (((j₁ : ℤ) + j₃ - j₂) / 2) = ((j₁ : ℤ) - j₂ + j₃) / 2 by omega,
    show (((j₁ : ℤ) - j₃ + j₂) / 2) = ((j₁ : ℤ) + j₂ - j₃) / 2 by omega,
    show ((-(j₁ : ℤ) + j₃ + j₂) / 2) = ((-(j₁ : ℤ) + j₂ + j₃) / 2) by omega]
  unfold triCoeff
  rw [show ((j₁ : ℤ) - j₂ + j₃) / 2 + ((j₁ : ℤ) + j₂ - j₃) / 2 + (-(j₁ : ℤ) + j₂ + j₃) / 2 + 1 =
    ((j₁ : ℤ) + j₂ - j₃) / 2 + ((j₁ : ℤ) - j₂ + j₃) / 2 + (-(j₁ : ℤ) + j₂ + j₃) / 2 + 1 by ring]
  ring

lemma racahSum6_perm₂₃ (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) :
    racahSum6 α₁ α₃ α₂ α₄ β₁ β₃ β₂ = racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ := by
  unfold racahSum6; refine finsum_congr fun t => ?_; ring

lemma racahSum6_perm₃₄β₁₃ (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) :
    racahSum6 α₁ α₂ α₄ α₃ β₃ β₂ β₁ = racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ := by
  unfold racahSum6; refine finsum_congr fun t => ?_; ring

/-- `racah6j` is invariant under exchanging the first two columns. -/
lemma racah6j_swap₁₂ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racah6j j₂ j₁ j₃ j₅ j₄ j₆ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racah6j
  rw [triD_swap₁₂ j₄ j₂ j₆, triD_swap₁₂ j₁ j₅ j₆, triD_swap₁₂ j₄ j₅ j₃, triD_swap₁₂ j₁ j₂ j₃,
    show triD j₁ j₂ j₃ * triD j₄ j₂ j₆ * triD j₁ j₅ j₆ * triD j₄ j₅ j₃ =
      triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ by ring]
  congr 1
  refine Eq.trans ?_ (racahSum6_perm₂₃ _ _ _ _ _ _ _)
  apply racahSum6_congr <;> omega

/-- `racah6j` is invariant under exchanging the last two columns. -/
lemma racah6j_swap₂₃ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racah6j j₁ j₃ j₂ j₄ j₆ j₅ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racah6j
  rw [triD_swap₂₃ j₁ j₂ j₃, triD_swap₂₃ j₁ j₅ j₆, triD_swap₂₃ j₄ j₂ j₆,
    triD_swap₂₃ j₄ j₅ j₃,
    show triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₅ j₃ * triD j₄ j₂ j₆ =
      triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ by ring]
  congr 1
  refine Eq.trans ?_ (racahSum6_perm₃₄β₁₃ _ _ _ _ _ _ _)
  apply racahSum6_congr <;> omega

/-! ### Racah's formula for `sixJSym` -/

/-- Admissible triad in doubled units: even perimeter and the triangle inequalities. -/
def TriadAdm (x y z : ℕ) : Prop := (x + y + z) % 2 = 0 ∧ x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y

/-- Region `R1`: the third column has maximal sum. -/
lemma sixJSym_eq_racah6j_R1 {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h₁ : TriadAdm j₁ j₂ j₃) (h₂ : TriadAdm j₁ j₅ j₆)
    (h₃ : TriadAdm j₄ j₂ j₆) (h₄ : TriadAdm j₄ j₅ j₃) (hj₁ : 0 < j₁) (hj₄ : 0 < j₄)
    (hc₁ : j₁ + j₄ ≤ j₃ + j₆) (hc₂ : j₂ + j₅ ≤ j₃ + j₆) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold TriadAdm at h₁ h₂ h₃ h₄
  obtain ⟨k₁, hk₁, hk₁'⟩ : ∃ k, j₃ = j₁ + j₂ - 2 * k ∧ 2 * k ≤ j₁ + j₂ :=
    ⟨(j₁ + j₂ - j₃) / 2, by omega, by omega⟩
  obtain ⟨k₃, hk₃, hk₃'⟩ : ∃ k, j₆ = j₂ + j₄ - 2 * k ∧ 2 * k ≤ j₂ + j₄ :=
    ⟨(j₂ + j₄ - j₆) / 2, by omega, by omega⟩
  obtain ⟨K, hK, hK'⟩ : ∃ k, j₅ = j₁ + j₂ + j₄ - 2 * k ∧ 2 * k ≤ j₁ + j₂ + j₄ :=
    ⟨(j₁ + j₂ + j₄ - j₅) / 2, by omega, by omega⟩
  subst hk₁ hk₃ hK
  have hab : 0 < j₁ + j₂ := by omega
  have hbc : 0 < j₂ + j₄ := by omega
  have hA : ValidA j₁ j₂ j₄ K k₁ := by unfold ValidA; omega
  have hB : ValidB j₁ j₂ j₄ K k₃ := by unfold ValidB; omega
  have hf₁ : k₁ < min j₁ j₂ + 1 := by omega
  have hf₃ : k₃ < min j₂ j₄ + 1 := by omega
  have e1 := sixJ_eq_sixJSym hab hbc hj₁ hj₄ (k₁ := ⟨k₁, hf₁⟩) (k₃ := ⟨k₃, hf₃⟩) hA hB
  have e2 := sixJ_eq_racah_R1 hab hbc hj₁ hj₄ (k₁ := ⟨k₁, hf₁⟩) (k₃ := ⟨k₃, hf₃⟩) hA hB
    (by simp only; omega)
  rw [← e1, e2]
  symm
  exact racah6j_eq_explicit (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

/-- **Racah's formula for `sixJSym`** whenever the four triads are admissible and the first
column `(j₁, j₄)` is positive. -/
theorem sixJSym_eq_racah6j {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h₁ : TriadAdm j₁ j₂ j₃) (h₂ : TriadAdm j₁ j₅ j₆)
    (h₃ : TriadAdm j₄ j₂ j₆) (h₄ : TriadAdm j₄ j₅ j₃) (hj₁ : 0 < j₁) (hj₄ : 0 < j₄) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  by_cases hA : j₁ + j₄ ≤ j₃ + j₆ ∧ j₂ + j₅ ≤ j₃ + j₆
  · exact sixJSym_eq_racah6j_R1 h₁ h₂ h₃ h₄ hj₁ hj₄ hA.1 hA.2
  by_cases hB : j₁ + j₄ ≤ j₂ + j₅
  · -- the second column is maximal: exchange columns 2 and 3
    have h := sixJSym_eq_racah6j_R1 (j₁ := j₁) (j₂ := j₃) (j₃ := j₂) (j₄ := j₄) (j₅ := j₆)
      (j₆ := j₅) (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega)
      (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega) hj₁ hj₄ (by omega) (by omega)
    rw [sixJSym_swap₂₃, racah6j_swap₂₃] at h
    exact h
  · -- the first column is maximal
    by_cases hP : 0 < j₂ ∧ 0 < j₅
    · have h := sixJSym_eq_racah6j_R1 (j₁ := j₂) (j₂ := j₃) (j₃ := j₁) (j₄ := j₅) (j₅ := j₆)
        (j₆ := j₄) (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega)
        (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega) hP.1 hP.2 (by omega) (by omega)
      rw [sixJSym_swap₂₃ (j₁ := j₂) (j₂ := j₁) (j₃ := j₃) (j₄ := j₅) (j₅ := j₄) (j₆ := j₆),
        sixJSym_swap₁₂, racah6j_swap₂₃ j₂ j₁ j₃ j₅ j₄ j₆, racah6j_swap₁₂] at h
      exact h
    · have h := sixJSym_eq_racah6j_R1 (j₁ := j₃) (j₂ := j₂) (j₃ := j₁) (j₄ := j₆) (j₅ := j₅)
        (j₆ := j₄) (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega)
        (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega) (by unfold TriadAdm at *; omega)
        (by unfold TriadAdm at *; omega) (by omega) (by omega)
      rw [sixJSym_swap₁₂ (j₁ := j₂) (j₂ := j₃) (j₃ := j₁) (j₄ := j₅) (j₅ := j₆) (j₆ := j₄),
        sixJSym_swap₂₃ (j₁ := j₂) (j₂ := j₁) (j₃ := j₃) (j₄ := j₅) (j₅ := j₄) (j₆ := j₆),
        sixJSym_swap₁₂, racah6j_swap₁₂ j₂ j₃ j₁ j₅ j₆ j₄, racah6j_swap₂₃ j₂ j₁ j₃ j₅ j₄ j₆,
        racah6j_swap₁₂] at h
      exact h

/-- **Racah's formula for the 6j symbol of `SixJ`.** For `0 < a`, `0 < c` and admissible
`(K, k₁)`, `(K, k₃)`, `{j₁ j₂ j₁₂; j₃ J j₂₃}` is `racah6j` of the doubled quantum numbers. -/
theorem sixJ_eq_racah6j {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ =
      racah6j a b (a + b - 2 * (k₁ : ℕ)) c (a + b + c - 2 * K) (b + c - 2 * (k₃ : ℕ)) := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  rw [sixJ_eq_sixJSym hab hbc ha hc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩]
  exact sixJSym_eq_racah6j (by unfold TriadAdm; omega) (by unfold TriadAdm; omega)
    (by unfold TriadAdm; omega) (by unfold TriadAdm; omega) ha hc

/-- **Racah's closed formula for `sixJ`**, in the natural parameters of `SixJ`, with the four `Δ²`
and the seven arguments of Racah's sum written out: the statement of `sixJ_eq_racah`, proved
without `sixJSym_eq_racah`. -/
theorem sixJ_eq_racah_explicit {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a)
    (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
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
  rw [sixJ_eq_racah6j hab hbc ha hc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩]
  exact racah6j_eq_explicit (by omega) (by omega) (by omega) (by omega) hA1 hA2 hA3 hB1 hB2 hB3

end PhyslibAlpha.Sl2
