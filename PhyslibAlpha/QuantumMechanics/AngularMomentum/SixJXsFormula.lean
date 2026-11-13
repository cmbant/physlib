/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJCollapse
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacahCollapse

/-!

# The operator-defined 6j symbol as a single sum

Composition of the operator half (`SixJCollapse`: `sixJ` is a constant times the double sum) with
the combinatorial half (`SixJRacahCollapse`: the double sum is a single sum `Xs`).

## i. Key results

- `sixJ_eq_const_mul_Tsum`: `sixJ = Cconst · Tsum`.
- `sixJ_eq_const_mul_Xs`: `sixJ = Cconst · Xs · X! / ((c-K+k₁)! k₃! (b-k₃)! (c-k₃)!)`,
  `X = b + c - k₃ - K`.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-- `sixJ` is the constant `Cconst` times Racah's double sum `Tsum`. -/
theorem sixJ_eq_const_mul_Tsum {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ = Cconst a b c K k₁ k₃ * Tsum a b c K k₁ k₃ :=
  sixJ_eq_const_mul_collapseSum hab hbc ha hc hA hB

/-- `sixJ` is the constant `Cconst` times the single sum `Xs`, up to explicit factorials. -/
theorem sixJ_eq_const_mul_Xs {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ = Cconst a b c K k₁ k₃ *
      (Xs a b c K k₁ k₃ * factZ ((b : ℤ) + c - k₃ - K) /
        (factZ ((c : ℤ) - K + k₁) * factZ k₃ * factZ ((b : ℤ) - k₃) * factZ ((c : ℤ) - k₃))) := by
  rw [sixJ_eq_const_mul_Tsum hab hbc ha hc hA hB]
  congr 1
  exact Tsum_eq_Xs_of_valid k₁.isLt k₃.isLt hA hB

end PhyslibAlpha.Sl2
