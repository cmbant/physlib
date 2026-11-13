/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJXsFormula

/-!

# The three-term recurrence of the 6j symbol from the operator definition (PROTOTYPE)

Scoping prototype. The only `sorry` is `casMat_eq`, the matrix of `J₂₃²` in the first coupling
scheme; everything else is proved.

## i. Overview

The Casimir `J₂₃²` of the last two factors of `V(a) ⊗ V(b) ⊗ V(c)` is diagonal in the second
coupling scheme `stateB` (eigenvalue `j₂₃(j₂₃ + 1)`) and, at fixed `J`, `M`, a Jacobi
(tridiagonal) matrix in the first scheme `stateA`, indexed by `j₁₂`. Hence the recoupling
coefficients `R(j₁₂, j₂₃)` are, for every `j₂₃`, an eigenvector of this Jacobi matrix, and the 6j
symbols satisfy a three-term recurrence in `j₁₂` with the eigenvalue `j₂₃(j₂₃ + 1)` as parameter
(the Racah/Hahn-polynomial structure of the 6j symbols; DLMF 34.5.11–13).

Proved here:

- `casBC`: `2 J₂₃²` on the triple product, self-adjoint (`tripleForm_casBC`) with `stateB` as
  eigenvectors (`casBC_stateB`).
- `sum_casMat_mul_recoupling`: **the Jacobi equation** `Σ_{j₁₂'} ⟨j₁₂|2J₂₃²|j₁₂'⟩ R(j₁₂', j₂₃) =
  2 j₂₃(j₂₃ + 1) R(j₁₂, j₂₃)`, with no knowledge of the matrix entries.
- `three_term_recoupling` and `sixJ_three_term`: the three-term recurrence of `R` and of `sixJ`,
  **assuming the entries** `CasMatSpec` (`casMat_eq`, open).
- `eq_of_three_term`: a three-term recurrence with nonvanishing leading coefficient and the first
  value determines the sequence.
- `sixJ_zero_left`: the first value (stretched `j₁₂ = j₁ + j₂`) from `sixJ_eq_const_mul_Xs`.

Open: `casMat_eq`, the entries of the Jacobi matrix: tridiagonality (triangle rule for `J₂`
between the components of `V(a) ⊗ V(b)`), the diagonal (projection theorem) and the off-diagonal
entries (reduced matrix elements of `J₂` between `j₁₂` and `j₁₂ ± 1`, with sign).

## ii. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- K. Schulten, R. G. Gordon, J. Math. Phys. 16, 1961 (1975); DLMF 34.5.11–13.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

section Casimir23

variable {a b c : ℕ}

variable (a b c) in
/-- `2 J₂₃²` on the triple product `V(a) ⊗ V(b) ⊗ V(c)`: the Casimir of `V(b) ⊗ V(c)`, acting on the
last two factors. -/
def casBC : Module.End ℝ (Triple a b c) :=
  (TensorProduct.assoc ℝ _ _ _).symm.toLinearMap ∘ₗ
    (tensorCas b c).lTensor (StandardSl2Module ℝ a) ∘ₗ (TensorProduct.assoc ℝ _ _ _).toLinearMap

lemma casBC_assoc_symm (q : StandardSl2Module ℝ a ⊗[ℝ] (StandardSl2Module ℝ b ⊗[ℝ]
    StandardSl2Module ℝ c)) :
    casBC a b c ((TensorProduct.assoc ℝ _ _ _).symm q) =
      (TensorProduct.assoc ℝ _ _ _).symm ((tensorCas b c).lTensor _ q) := by
  simp [casBC]

lemma casBC_tmul (x : StandardSl2Module ℝ a) (y : StandardSl2Module ℝ b)
    (z : StandardSl2Module ℝ c) :
    casBC a b c ((x ⊗ₜ y) ⊗ₜ z) =
      (TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ tensorCas b c (y ⊗ₜ z)) := by
  simp [casBC]

lemma tensorForm_tensorCas {m n : ℕ} (x y : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    tensorForm m n (tensorCas m n x) y = tensorForm m n x (tensorCas m n y) := by
  simp only [tensorCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, map_add,
    map_smul]
  rw [tensorForm_tensorE, tensorForm_tensorF, tensorForm_tensorF, tensorForm_tensorE,
    tensorForm_tensorH, tensorForm_tensorH]

/-- `casBC` is self-adjoint for the contravariant form. -/
lemma tripleForm_casBC (u v : Triple a b c) :
    tripleForm a b c (casBC a b c u) v = tripleForm a b c u (casBC a b c v) := by
  have h : LinearMap.comp (tripleForm a b c) (casBC a b c) =
      LinearMap.compl₂ (tripleForm a b c) (casBC a b c) :=
    tripleBilin_ext fun x y z x' y' z' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, casBC_tmul]
      rw [← TensorProduct.assoc_symm_tmul x y z, ← TensorProduct.assoc_symm_tmul x' y' z',
        tripleForm_assoc_symm, tripleForm_assoc_symm, tensorForm_tensorCas]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

lemma tensorCas_embed {m n : ℕ} (hmn : 0 < m + n) (k : Fin (min m n + 1))
    (y : StandardSl2Module ℝ (m + n - 2 * (k : ℕ))) :
    tensorCas m n (embed hmn k y) =
      ((((m + n - 2 * (k : ℕ) : ℕ) : ℝ) * (((m + n - 2 * (k : ℕ) : ℕ) : ℝ) + 2) / 2)) •
        embed hmn k y := by
  have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
  have hkn : (k : ℕ) ≤ n := by have := k.isLt; omega
  have h : tensorCas m n ∘ₗ embed hmn k =
      (((m + n - 2 * (k : ℕ) : ℕ) : ℝ) * (((m + n - 2 * (k : ℕ) : ℕ) : ℝ) + 2) / 2) •
        embed hmn k :=
    linearMap_ext_vNat fun l => by
      rw [LinearMap.comp_apply, LinearMap.smul_apply, embed_vNat, map_smul,
        tensorCas_stringVec hmn hkm hkn, smul_comm]
  exact LinearMap.congr_fun h y

lemma casBC_assocEmbed (hbc : 0 < b + c) (k₃ : Fin (min b c + 1))
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    casBC a b c (assocEmbed hbc k₃ w) =
      ((((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) •
        assocEmbed hbc k₃ w := by
  have h : casBC a b c ∘ₗ assocEmbed hbc k₃ =
      ((((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) •
        assocEmbed hbc k₃ :=
    TensorProduct.ext' fun x y => by
      simp only [assocEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
        LinearMap.smul_apply, casBC_assoc_symm, tensorCas_embed, TensorProduct.tmul_smul, map_smul]
  exact LinearMap.congr_fun h w

/-- `stateB` is an eigenvector of `casBC`, with eigenvalue `2 j₂₃ (j₂₃ + 1)`. -/
lemma casBC_stateB (hbc : 0 < b + c) (k₃ : Fin (min b c + 1)) (k₄ l : ℕ) :
    casBC a b c (stateB hbc k₃ k₄ l) =
      ((((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) •
        stateB hbc k₃ k₄ l :=
  casBC_assocEmbed hbc k₃ _

end Casimir23

/-!

## B. The Jacobi equation

-/

section Jacobi

variable {a b c : ℕ}

/-- **Pairing with `stateB`.** For `M = J` and `j₂₃` fixed, the pairing of any vector with
`|j₁, (j₂ j₃) j₂₃; J J⟩` is the sum over `j₁₂` of its components along
`|(j₁ j₂) j₁₂, j₃; J J⟩`, weighted by the recoupling coefficients. -/
lemma tripleForm_stateB_eq_sum (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} {k₃ : Fin (min b c + 1)} (hB : ValidB a b c K k₃) (x : Triple a b c) :
    tripleForm a b c (stateB hbc k₃ (K - k₃) 0) x =
      ∑ k₁ : Fin (min a b + 1), (if ValidA a b c K k₁ then
        tripleForm a b c (stateA hab k₁ (K - k₁) 0) x * recoupling hab hbc K 0 k₁ k₃ else 0) := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hk₃ := k₃.isLt
  conv_lhs => rw [eq_sum_vecA hab hc x]
  rw [map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  have hk₁ := k₁.isLt
  rw [Fintype.sum_sigma]
  by_cases hv : ValidA a b c K k₁
  · obtain ⟨hA1, hA2, hA3⟩ := hv
    rw [ite_eq_left ⟨hA1, hA2, hA3⟩]
    have hk₂ : K - (k₁ : ℕ) < min (a + b - 2 * (k₁ : ℕ)) c + 1 := by omega
    rw [Fintype.sum_eq_single ⟨K - k₁, hk₂⟩]
    · have hl' : 0 < a + b - 2 * (k₁ : ℕ) + c - 2 * (K - k₁) + 1 := by omega
      rw [Fintype.sum_eq_single ⟨0, hl'⟩]
      · simp only [vecA, map_smul, smul_eq_mul, recoupling]
        rw [tripleForm_comm (stateB hbc k₃ (K - k₃) 0)]
      · intro l' hl''
        simp only [vecA, map_smul, smul_eq_mul]
        rw [tripleForm_comm (stateB hbc k₃ (K - k₃) 0),
          tripleForm_stateA_stateB_eq_zero hab hbc ha hc hA2 hA3 hB2 hB3
          (fun h => hl'' (Fin.ext h.2)), mul_zero]
    · intro k₂ hk₂'
      have := k₂.isLt
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp only [vecA, map_smul, smul_eq_mul]
      rw [tripleForm_comm (stateB hbc k₃ (K - k₃) 0),
        tripleForm_stateA_stateB_eq_zero hab hbc ha hc (by omega) (by omega) hB2 hB3
        (fun h => hk₂' (Fin.ext (show (k₂ : ℕ) = K - (k₁ : ℕ) by have := h.1; omega))), mul_zero]
  · rw [ite_eq_right hv]
    refine Finset.sum_eq_zero fun k₂ _ => Finset.sum_eq_zero fun l' _ => ?_
    have := k₂.isLt
    simp only [vecA, map_smul, smul_eq_mul]
    rw [tripleForm_comm (stateB hbc k₃ (K - k₃) 0),
      tripleForm_stateA_stateB_eq_zero hab hbc ha hc (by omega) (by omega) hB2 hB3
      (fun h => hv (by obtain ⟨h1, _⟩ := h; exact ⟨by omega, by omega, by omega⟩)), mul_zero]

/-- The matrix element `⟨(j₁ j₂) j₁₂', j₃; J J | 2J₂₃² | (j₁ j₂) j₁₂, j₃; J J⟩` (`j₁₂ = (a + b)/2 - k₁`,
`j₁₂' = (a + b)/2 - k₁'`, `J = (a + b + c)/2 - K`). -/
def casMat (c : ℕ) (hab : 0 < a + b) (K : ℕ) (k₁' k₁ : Fin (min a b + 1)) : ℝ :=
  tripleForm a b c (stateA hab k₁' (K - k₁') 0) (casBC a b c (stateA hab k₁ (K - k₁) 0))

/-- **The Jacobi equation.** The recoupling coefficients `⟨(j₁ j₂) j₁₂, j₃; J J | j₁, (j₂ j₃) j₂₃; J J⟩`
form, for each `j₂₃`, an eigenvector of the matrix of `2J₂₃²` in the first coupling scheme, with
eigenvalue `2 j₂₃ (j₂₃ + 1) = n (n + 2) / 2`, `n = b + c - 2k₃`:
`Σ_{j₁₂'} ⟨j₁₂| 2J₂₃² |j₁₂'⟩ R(j₁₂', j₂₃) = (n (n + 2) / 2) R(j₁₂, j₂₃)`. -/
lemma sum_casMat_mul_recoupling (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hB : ValidB a b c K k₃) :
    ∑ k₁' : Fin (min a b + 1), (if ValidA a b c K k₁' then
      casMat c hab K k₁' k₁ * recoupling hab hbc K 0 k₁' k₃ else 0) =
        ((((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) *
          recoupling hab hbc K 0 k₁ k₃ := by
  have h1 := tripleForm_stateB_eq_sum hab hbc ha hc hB (casBC a b c (stateA hab k₁ (K - k₁) 0))
  rw [← tripleForm_casBC, casBC_stateB, map_smul, LinearMap.smul_apply, smul_eq_mul,
    tripleForm_comm (stateB hbc k₃ (K - k₃) 0)] at h1
  unfold casMat
  rw [← h1]
  rfl

end Jacobi

/-!

## C. The matrix of `2J₂₃²` (STATEMENT; proof open)

-/

section Matrix

/-- `j (j + 1) = x (x + 2) / 4` for the doubled spin `x = 2j`. -/
def jj (x : ℝ) : ℝ := x * (x + 2) / 4

/-- The diagonal entry of `2J₂₃²` in the basis `|(j₁ j₂) j₁₂, j₃; J J⟩`, with doubled spins `a`, `b`,
`c`, `N = 2J`, `n = 2j₁₂`:
`2 (j₂(j₂+1) + j₃(j₃+1)) + (j₁₂(j₁₂+1) + j₂(j₂+1) - j₁(j₁+1)) (J(J+1) - j₁₂(j₁₂+1) - j₃(j₃+1)) /
j₁₂(j₁₂+1)`
(the projection theorem: `J₂ → (J₂·J₁₂/J₁₂²) J₁₂` on the `j₁₂`-multiplet). -/
def casDiag (a b c N n : ℝ) : ℝ :=
  2 * (jj b + jj c) + (jj n + jj b - jj a) * (jj N - jj n - jj c) / jj n

/-- The radicand `E²` of the off-diagonal entry, in doubled units:
`(n² - (a-b)²)((a+b+2)² - n²)(n² - (N-c)²)((N+c+2)² - n²)`, `16² E² = ` this, where
`E² = (j₁₂² - (j₁-j₂)²)((j₁+j₂+1)² - j₁₂²)(j₁₂² - (J-j₃)²)((J+j₃+1)² - j₁₂²)`. -/
def casPi (a b c N n : ℝ) : ℝ :=
  (n ^ 2 - (a - b) ^ 2) * ((a + b + 2) ^ 2 - n ^ 2) * (n ^ 2 - (N - c) ^ 2) *
    ((N + c + 2) ^ 2 - n ^ 2)

/-- The off-diagonal entry of `2J₂₃²` between `j₁₂ = n/2` and `j₁₂ - 1`:
`E(j₁₂) / (4 j₁₂ √(4 j₁₂² - 1))`, in doubled units `√(casPi) / (8 n √(n² - 1))`. -/
def casOff (a b c N n : ℝ) : ℝ :=
  Real.sqrt (casPi a b c N n) / (8 * n * Real.sqrt (n ^ 2 - 1))

variable (c) in
/-- **The Jacobi matrix of `J₂₃²`** (statement). On the admissible `j₁₂` the matrix of `2J₂₃²` in the
first coupling scheme at `M = J` is tridiagonal, with diagonal `casDiag` and off-diagonal `casOff`.

Verified exactly/numerically (60 digits) against the operator definition in `phys.py`; the proof
needs (i) the triangle rule for the vector operator `J₂` between the components of `V(a) ⊗ V(b)`
(tridiagonality), (ii) the projection theorem on each component (diagonal), and (iii) a normalisation
of the reduced matrix elements of `J₂` between `j₁₂` and `j₁₂ ± 1`, with sign (off-diagonal). -/
def CasMatSpec {a b : ℕ} (hab : 0 < a + b) (K : ℕ) : Prop :=
  ∀ k k' : Fin (min a b + 1), ValidA a b c K k → ValidA a b c K k' →
    casMat c hab K k' k =
      (if (k' : ℕ) = k then casDiag a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k : ℕ) : ℕ) : ℝ)
        else 0) +
      (if (k' : ℕ) = k + 1 then casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ)
        ((a + b - 2 * (k : ℕ) : ℕ) : ℝ) else 0) +
      (if (k' : ℕ) + 1 = k then casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ)
        ((a + b - 2 * (k' : ℕ) : ℕ) : ℝ) else 0)

theorem casMat_eq {a b : ℕ} (hab : 0 < a + b) (ha : 0 < a) (hc : 0 < c) (K : ℕ) :
    CasMatSpec c hab K := by
  sorry

end Matrix

section ThreeTerm

variable {a b c : ℕ}

/-- The recoupling coefficient `R(j₁₂, j₂₃)` at `M = J`, as a function of `k₁ : ℕ` (zero outside the
admissible range). -/
def recN (hab : 0 < a + b) (hbc : 0 < b + c) (K : ℕ) (k₃ : Fin (min b c + 1)) (i : ℕ) : ℝ :=
  if h : i < min a b + 1 then
    (if ValidA a b c K i then recoupling hab hbc K 0 ⟨i, h⟩ k₃ else 0) else 0

/-- **The three-term recurrence for the recoupling coefficients**, from the Jacobi equation and the
matrix `casMat_eq` of `2J₂₃²`. With `n = a + b - 2k₁` (`= 2j₁₂`), `N = a + b + c - 2K` (`= 2J`) and
`ν = b + c - 2k₃` (`= 2j₂₃`):
`casDiag(n) R(k₁) + casOff(n) R(k₁ + 1) + casOff(n + 2) R(k₁ - 1) = (ν (ν + 2) / 2) R(k₁)`
(the last term absent for `k₁ = 0`). -/
theorem three_term_recoupling (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} (hspec : CasMatSpec c hab K) {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    casDiag a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) *
        recN hab hbc K k₃ k₁ +
      casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) *
        recN hab hbc K k₃ (k₁ + 1) +
      (if (k₁ : ℕ) = 0 then 0 else
        casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ) (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 2) *
          recN hab hbc K k₃ (k₁ - 1)) =
      ((((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) *
        recN hab hbc K k₃ k₁ := by
  have hk₁ := k₁.isLt
  have hJ := sum_casMat_mul_recoupling hab hbc ha hc (k₁ := k₁) hB
  have hrN : recN hab hbc K k₃ k₁ = recoupling hab hbc K 0 k₁ k₃ := by
    rw [recN, dite_eq_left hk₁, ite_eq_left hA]
  rw [hrN]
  rw [← hJ]
  -- pass to a sum over `range`
  have hconv : ∑ k' : Fin (min a b + 1), (if ValidA a b c K k' then
      casMat c hab K k' k₁ * recoupling hab hbc K 0 k' k₃ else 0) =
      ∑ i ∈ Finset.range (min a b + 1), (if h : i < min a b + 1 then casMat c hab K ⟨i, h⟩ k₁ else 0) *
        recN hab hbc K k₃ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < min a b + 1 then casMat c hab K ⟨i, h⟩ k₁
      else 0) * recN hab hbc K k₃ i)]
    refine Finset.sum_congr rfl fun k' _ => ?_
    by_cases hv : ValidA a b c K k'
    · simp [recN, k'.isLt, hv]
    · simp [recN, k'.isLt, hv]
  rw [hconv]
  have hterm : ∀ i ∈ Finset.range (min a b + 1),
      (if h : i < min a b + 1 then casMat c hab K ⟨i, h⟩ k₁ else 0) * recN hab hbc K k₃ i =
      (if i = (k₁ : ℕ) then casDiag a b c ((a + b + c - 2 * K : ℕ) : ℝ)
          ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) * recN hab hbc K k₃ i else 0) +
      (if i = (k₁ : ℕ) + 1 then casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ)
          ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) * recN hab hbc K k₃ i else 0) +
      (if i + 1 = (k₁ : ℕ) then casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ)
          (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 2) * recN hab hbc K k₃ i else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hr : recN hab hbc K k₃ i = 0
    · simp [hr]
    · have hvi : ValidA a b c K i := by
        by_contra hv
        apply hr
        simp [recN, hv]
      rw [dite_eq_left hi', hspec k₁ ⟨i, hi'⟩ hA hvi]
      simp only [add_mul, ite_mul, zero_mul]
      by_cases hik : i + 1 = (k₁ : ℕ)
      · have h2 : a + b - 2 * i = (a + b - 2 * (k₁ : ℕ)) + 2 := by omega
        have h3 : i ≠ (k₁ : ℕ) := by omega
        have h4 : i ≠ (k₁ : ℕ) + 1 := by omega
        simp only [hik, h3, h4, ite_true, ite_false, h2]
        push_cast
        ring
      · simp [hik]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hk₁)]
  rw [← hrN]
  have hup : (if (k₁ : ℕ) + 1 ∈ Finset.range (min a b + 1) then
      casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) *
        recN hab hbc K k₃ ((k₁ : ℕ) + 1) else 0) =
      casOff a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) *
        recN hab hbc K k₃ ((k₁ : ℕ) + 1) := by
    split_ifs with h
    · rfl
    · have : ¬ ((k₁ : ℕ) + 1 < min a b + 1) := fun h' => h (Finset.mem_range.mpr h')
      rw [recN, dite_eq_right this, mul_zero]
  rw [hup]
  congr 1
  by_cases h0 : (k₁ : ℕ) = 0
  · rw [ite_eq_left h0, Finset.sum_eq_zero]
    intro x _
    rw [ite_eq_right (by omega)]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [ite_eq_right h0, Finset.sum_eq_single m]
    · simp only [hm, Nat.succ_eq_add_one, ite_true, Nat.add_sub_cancel]
    · intro x _ hx
      rw [ite_eq_right (by omega)]
    · intro hm'
      have hm1 : m < min a b + 1 := by omega
      exact absurd (Finset.mem_range.mpr hm1) hm'


end ThreeTerm

section SixJForm

variable {a b c : ℕ}

/-- The 6j symbol as a function of `k₁ : ℕ` (zero outside the admissible range). -/
def sixJN (hab : 0 < a + b) (hbc : 0 < b + c) (K : ℕ) (k₃ : Fin (min b c + 1)) (i : ℕ) : ℝ :=
  if h : i < min a b + 1 then sixJ hab hbc K ⟨i, h⟩ k₃ else 0

lemma recN_eq_sixJN (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) {K : ℕ}
    {k₃ : Fin (min b c + 1)} (hB : ValidB a b c K k₃) (i : ℕ) :
    recN hab hbc K k₃ i = (-1) ^ (a + b + c - K) *
      Real.sqrt (((a + b - 2 * i + 1 : ℕ) : ℝ) * ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) *
        sixJN hab hbc K k₃ i := by
  by_cases hi : i < min a b + 1
  · by_cases hv : ValidA a b c K i
    · rw [recN, dite_eq_left hi, ite_eq_left hv, sixJN, dite_eq_left hi]
      exact recoupling_eq_sixJ hab hbc ha (k₁ := ⟨i, hi⟩) hv hB (Nat.zero_le _)
    · rw [recN, dite_eq_left hi, ite_eq_right hv, sixJN, dite_eq_left hi, sixJ, ite_eq_right (fun h => hv h.1), mul_zero]
  · rw [recN, dite_eq_right hi, sixJN, dite_eq_right hi, mul_zero]

/-- **The three-term recurrence of the 6j symbol** (Schulten–Gordon, DLMF 34.5.11) in the variable
`j₁₂`, with `n = a + b - 2k₁ = 2j₁₂`, `N = a + b + c - 2K = 2J` and `ν = b + c - 2k₃ = 2j₂₃`:

`√Π(n)/(8n(n+1)) · {k₁ + 1} + (casDiag(n) - ν(ν+2)/2) · {k₁} + √Π(n+2)/(8(n+2)(n+1)) · {k₁ - 1} = 0`

(the last term absent for `k₁ = 0`), where `{k}` is the 6j symbol at `j₁₂ = (a + b)/2 - k` and
`Π = casPi`. Proved from the Jacobi matrix `casMat_eq` of `2J₂₃²` (the only open input). -/
theorem sixJ_three_term (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} (hspec : CasMatSpec c hab K) {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    Real.sqrt (casPi a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ)) /
        (8 * ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) * (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 1)) *
          sixJN hab hbc K k₃ (k₁ + 1) +
      (casDiag a b c ((a + b + c - 2 * K : ℕ) : ℝ) ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) -
        (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) * (((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) + 2) / 2)) *
          sixJN hab hbc K k₃ k₁ +
      (if (k₁ : ℕ) = 0 then 0 else
        Real.sqrt (casPi a b c ((a + b + c - 2 * K : ℕ) : ℝ)
            (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 2)) /
          (8 * (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 2) * (((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) + 1)) *
            sixJN hab hbc K k₃ (k₁ - 1)) = 0 := by
  have h := three_term_recoupling hab hbc ha hc hspec hA hB
  have hk₁ := k₁.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hn : (a + b - 2 * (k₁ : ℕ) : ℕ) + 1 = (a + b - 2 * (k₁ : ℕ) + 1 : ℕ) := rfl
  set n : ℝ := ((a + b - 2 * (k₁ : ℕ) : ℕ) : ℝ) with hn_def
  set N : ℝ := ((a + b + c - 2 * K : ℕ) : ℝ) with hN_def
  set ν : ℝ := ((b + c - 2 * (k₃ : ℕ) : ℕ) : ℝ) with hν_def
  set s : ℝ := (-1) ^ (a + b + c - K) with hs_def
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hν0 : 0 ≤ ν := Nat.cast_nonneg _
  have hspos : s * s = 1 := by
    rw [hs_def, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hx : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < Real.sqrt (ν + 1) := Real.sqrt_pos.mpr (by linarith)
  have hxx := Real.sq_sqrt (show 0 ≤ n + 1 by linarith)
  have hνc : ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ) = ν + 1 := by
    rw [hν_def]; push_cast; ring
  have e0 : recN hab hbc K k₃ k₁ = s * (Real.sqrt (n + 1) * Real.sqrt (ν + 1)) * sixJN hab hbc K k₃ k₁ := by
    rw [recN_eq_sixJN hab hbc ha hB, Real.sqrt_mul (by linarith)]
    push_cast [hn_def, hν_def]
    rfl
  -- the neighbour `k₁ + 1`
  have e1 : casOff a b c N n * recN hab hbc K k₃ (k₁ + 1) =
      Real.sqrt (casPi a b c N n) / (8 * n * (n + 1)) * sixJN hab hbc K k₃ (k₁ + 1) *
        (s * Real.sqrt (n + 1) * Real.sqrt (ν + 1)) := by
    by_cases hi : (k₁ : ℕ) + 1 < min a b + 1
    · have hmin1 := Nat.min_le_left a b
      have hmin2 := Nat.min_le_right a b
      have hn2 : 2 ≤ n := by
        have : 2 ≤ a + b - 2 * (k₁ : ℕ) := by omega
        rw [hn_def]; exact_mod_cast this
      have hcast : ((a + b - 2 * ((k₁ : ℕ) + 1) + 1 : ℕ) : ℝ) = n - 1 := by
        have h' : (a + b - 2 * (k₁ : ℕ) : ℕ) = (a + b - 2 * ((k₁ : ℕ) + 1) + 1) + 1 := by omega
        rw [hn_def, h']; push_cast; ring
      have hz : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr (by linarith)
      rw [recN_eq_sixJN hab hbc ha hB, hcast, hνc, casOff, show n ^ 2 - 1 = (n - 1) * (n + 1) by ring,
        Real.sqrt_mul (by linarith), Real.sqrt_mul (by linarith)]
      have hzz := Real.sq_sqrt (show 0 ≤ n - 1 by linarith)
      have hxx' := Real.sq_sqrt (show 0 ≤ n + 1 by linarith)
      have hn0' : n ≠ 0 := by linarith
      field_simp
      rw [show (Real.sqrt (n + 1)) ^ 2 = n + 1 from hxx']
      ring
    · rw [recN, dite_eq_right hi, sixJN, dite_eq_right hi]
      ring
  -- the neighbour `k₁ - 1`
  have e2 : (if (k₁ : ℕ) = 0 then 0 else
      casOff a b c N (n + 2) * recN hab hbc K k₃ ((k₁ : ℕ) - 1)) =
      (if (k₁ : ℕ) = 0 then 0 else
        Real.sqrt (casPi a b c N (n + 2)) / (8 * (n + 2) * (n + 1)) *
          sixJN hab hbc K k₃ ((k₁ : ℕ) - 1) * (s * Real.sqrt (n + 1) * Real.sqrt (ν + 1))) := by
    by_cases h0 : (k₁ : ℕ) = 0
    · simp only [h0, ite_true]
    · rw [ite_eq_right h0, ite_eq_right h0]
      have hcast : ((a + b - 2 * ((k₁ : ℕ) - 1) + 1 : ℕ) : ℝ) = n + 3 := by
        have h' : (a + b - 2 * ((k₁ : ℕ) - 1) + 1 : ℕ) = (a + b - 2 * (k₁ : ℕ)) + 3 := by omega
        rw [h', hn_def]; push_cast; ring
      have hy : 0 < Real.sqrt (n + 3) := Real.sqrt_pos.mpr (by linarith)
      have hyy := Real.sq_sqrt (show 0 ≤ n + 3 by linarith)
      rw [recN_eq_sixJN hab hbc ha hB, hcast, hνc, casOff,
        show (n + 2) ^ 2 - 1 = (n + 1) * (n + 3) by ring, Real.sqrt_mul (by linarith),
        Real.sqrt_mul (by linarith)]
      field_simp
      rw [show (Real.sqrt (n + 1)) ^ 2 = n + 1 from hxx]
      ring
  have hne : s * Real.sqrt (n + 1) * Real.sqrt (ν + 1) ≠ 0 := by
    have : s ≠ 0 := fun h0 => by rw [h0] at hspos; norm_num at hspos
    positivity
  have hmain : (Real.sqrt (casPi a b c N n) / (8 * n * (n + 1)) * sixJN hab hbc K k₃ (k₁ + 1) +
      (casDiag a b c N n - ν * (ν + 2) / 2) * sixJN hab hbc K k₃ k₁ +
      (if (k₁ : ℕ) = 0 then 0 else
        Real.sqrt (casPi a b c N (n + 2)) / (8 * (n + 2) * (n + 1)) *
          sixJN hab hbc K k₃ ((k₁ : ℕ) - 1))) *
      (s * Real.sqrt (n + 1) * Real.sqrt (ν + 1)) = 0 := by
    have e2' : (if (k₁ : ℕ) = 0 then 0 else
        Real.sqrt (casPi a b c N (n + 2)) / (8 * (n + 2) * (n + 1)) *
          sixJN hab hbc K k₃ ((k₁ : ℕ) - 1)) * (s * Real.sqrt (n + 1) * Real.sqrt (ν + 1)) =
        (if (k₁ : ℕ) = 0 then 0 else
          casOff a b c N (n + 2) * recN hab hbc K k₃ ((k₁ : ℕ) - 1)) := by
      rw [e2]; split_ifs <;> ring
    rw [add_mul, add_mul, e2', ← e1]
    rw [e0] at h
    linear_combination h
  exact (mul_eq_zero.mp hmain).resolve_right hne

end SixJForm

/-!

## D. Closing the induction

-/

section Closure

/-- **Uniqueness for a three-term recurrence.** Two sequences satisfying the same three-term
recurrence `p k · u (k + 1) = q k · u k + r k · u (k - 1)` (`r 0 = 0`) with `p k ≠ 0` for `k < N` and
the same initial value agree up to `N`. -/
lemma eq_of_three_term {u v p q r : ℕ → ℝ} (N : ℕ) (hr : r 0 = 0) (hp : ∀ k < N, p k ≠ 0)
    (hu : ∀ k < N, p k * u (k + 1) = q k * u k + r k * u (k - 1))
    (hv : ∀ k < N, p k * v (k + 1) = q k * v k + r k * v (k - 1)) (h0 : u 0 = v 0) :
    ∀ k ≤ N, u k = v k := by
  have key : ∀ k ≤ N, u k = v k ∧ (k = 0 ∨ u (k - 1) = v (k - 1)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨h0, Or.inl rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨?_, Or.inr (by simpa using h1)⟩
      have e1 := hu k (by omega)
      have e2 := hv k (by omega)
      have hrk : r k * u (k - 1) = r k * v (k - 1) := by
        rcases h2 with h2 | h2
        · subst h2; simp [hr]
        · rw [h2]
      have : p k * u (k + 1) = p k * v (k + 1) := by rw [e1, e2, h1, hrk]
      exact mul_left_cancel₀ (hp k (by omega)) this
  exact fun k hk => (key k hk).1

end Closure

/-!

## E. The boundary value

At the extremal `j₁₂ = j₁ + j₂` (`k₁ = 0`) the sum `Xs` of `SixJXsFormula` has a single term.

-/

section Boundary

lemma Xs_zero_left (a b c K k₃ : ℤ) (hk : 0 ≤ k₃) (hA : 0 ≤ a + (b + c - k₃ - K) + 1) :
    Xs a b c K 0 k₃ = factZ (c - k₃) * factZ b * factZ a * invFact (K - k₃) := by
  rw [Xs, finsum_eq_single _ 0]
  · simp [zbinom, hk, hA]
  · intro x hx
    have h : zbinom k₃ x = 0 ∨ zbinom (a + (b + c - k₃ - K) + 1) (0 - x) = 0 := by
      by_cases h : 0 ≤ x
      · right; simp only [zbinom]; split_ifs with hh
        · omega
        · rfl
      · left; simp only [zbinom]; split_ifs with hh
        · omega
        · rfl
    rcases h with h | h <;> simp only [h, mul_zero, zero_mul]

/-- **The stretched value.** At `j₁₂ = j₁ + j₂` the 6j symbol is a closed product. -/
theorem sixJ_zero_left {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K 0) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K ⟨0, by omega⟩ k₃ = Cconst a b c K 0 k₃ *
      (factZ ((c : ℤ) - k₃) * factZ b * factZ a * invFact ((K : ℤ) - k₃) *
        factZ ((b : ℤ) + c - k₃ - K) /
        (factZ ((c : ℤ) - K + 0) * factZ k₃ * factZ ((b : ℤ) - k₃) * factZ ((c : ℤ) - k₃))) := by
  have h := sixJ_eq_const_mul_Xs hab hbc ha hc (k₁ := ⟨0, by omega⟩) hA hB
  have hk₃ := k₃.isLt
  obtain ⟨_, hB2, hB3⟩ := hB
  simp only [Nat.cast_zero] at h ⊢
  rw [h, Xs_zero_left _ _ _ _ _ (by positivity) (by omega)]

end Boundary

end PhyslibAlpha.Sl2
