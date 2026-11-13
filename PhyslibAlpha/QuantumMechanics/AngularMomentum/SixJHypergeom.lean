/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3j

/-!

# Terminating balanced hypergeometric sums: Saalschütz and Sears

Two classical summation and transformation formulas for terminating balanced hypergeometric series
at argument `1`, with real parameters and explicit non-vanishing hypotheses, in the form used for the
proof of Racah's formula for the 6j symbol.

## i. Overview

`rf x k = x (x + 1) ⋯ (x + k - 1)` is the rising factorial. The terminating balanced `₃F₂(1)`
(Pfaff–Saalschütz) is evaluated by a Pascal-type recursion in the length `n`: with
`sT n a b c e k = (-n)_k (a)_k (b)_k / (k! (c)_k (e)_k)` and `e = 1 + a + b - c - n` one has
`T(n + 1, k) = α(k) T(n, k) + β(k) T(n, k - 1)` with polynomial coefficients, so the sum
telescopes (`saal_step`). The Sears (Whipple) transformation of a terminating balanced `₄F₃(1)`
(`sears`) is then proved as in Andrews–Askey–Roy, Thm 3.3.3: one ratio of Pochhammer symbols is
expanded by Saalschütz, the double sum is exchanged, and the inner sum is again Saalschütz.

## ii. Key results

- `saal`: `Σ_k (-n)_k (a)_k (b)_k / (k! (c)_k (e)_k) = (-1)^n (c - a)_n (c - b)_n / ((c)_n (e)_n)` for
  `e = 1 + a + b - c - n`.
- `sears`: `₄F₃(-n, A, B, C; d, e, f) = (e - A)_n (f - A)_n / ((e)_n (f)_n) ·
  ₄F₃(-n, A, d - B, d - C; d, A - e - n + 1, A - f - n + 1)`, `d + e + f = A + B + C - n + 1`
  (stated in the multiplied form, with the hypotheses needed by the proof).

## iii. References

- G. E. Andrews, R. Askey, R. Roy, *Special Functions*, Thm 2.2.6 and Thm 3.3.3.
- W. N. Bailey, *Generalized hypergeometric series*, §4.3 and §7.2.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2.Hyper

open Finset

/-- Rising factorial `(x)_k = x (x + 1) ⋯ (x + k - 1)`. -/
def rf (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => rf x k * (x + k)

@[simp] lemma rf_zero (x : ℝ) : rf x 0 = 1 := rfl
lemma rf_succ (x : ℝ) (k : ℕ) : rf x (k + 1) = rf x k * (x + k) := rfl

lemma rf_succ' (x : ℝ) (k : ℕ) : rf x (k + 1) = x * rf (x + 1) k := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    rw [rf_succ, ih, rf_succ]; push_cast; ring

lemma rf_add (x : ℝ) (i j : ℕ) : rf x (i + j) = rf x i * rf (x + i) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, rf_succ, ih, rf_succ]; push_cast; ring

lemma rf_ne_zero_of_le {x : ℝ} {n k : ℕ} (h : rf x n ≠ 0) (hk : k ≤ n) : rf x k ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [rf_add] at h
  exact left_ne_zero_of_mul h

lemma rf_ne_zero_shift {x : ℝ} {n k : ℕ} (h : rf x n ≠ 0) (hk : k ≤ n) :
    rf (x + k) (n - k) ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [rf_add] at h
  simpa using right_ne_zero_of_mul h

lemma rf_reflect (y : ℝ) (j : ℕ) : rf (1 - y - j) j = (-1) ^ j * rf y j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [rf_succ', rf_succ]
    have : (1 - y - ((j + 1 : ℕ) : ℝ)) + 1 = 1 - y - j := by push_cast; ring
    rw [this, ih]; push_cast; ring

lemma rf_one (n : ℕ) : rf 1 n = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [rf_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- The summand of the terminating Saalschütz sum. -/
def sT (n : ℕ) (a b c e : ℝ) (k : ℕ) : ℝ :=
  rf (-n) k * rf a k * rf b k / ((k.factorial : ℝ) * rf c k * rf e k)

lemma sT_zero (n : ℕ) (a b c e : ℝ) : sT n a b c e 0 = 1 := by simp [sT]

lemma sT_succ_self (n : ℕ) (a b c e : ℝ) : sT n a b c e (n + 1) = 0 := by
  have : rf (-(n : ℝ)) (n + 1) = 0 := by
    rw [rf_succ]; simp
  simp [sT, this]

lemma sT_rel (n k : ℕ) (a b c e : ℝ) (he : e = 1 + a + b - c - n)
    (hc : rf c (k + 1) ≠ 0) (he1 : rf e (k + 1) ≠ 0) (he2 : e - 1 ≠ 0) :
    (c + n) * (c - a - b + n) * sT (n + 1) a b c (e - 1) (k + 1) =
      ((c - a + n) * (c - b + n) - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        (a + k) * (b + k) * sT n a b c e k := by
  have hck : rf c k ≠ 0 := rf_ne_zero_of_le hc (Nat.le_succ k)
  have hek : rf e k ≠ 0 := rf_ne_zero_of_le he1 (Nat.le_succ k)
  have hc' : c + k ≠ 0 := by
    rw [rf_succ] at hc; exact right_ne_zero_of_mul hc
  have he' : e + k ≠ 0 := by
    rw [rf_succ] at he1; exact right_ne_zero_of_mul he1
  have h1 : (-(((n + 1 : ℕ)) : ℝ)) + 1 = -(n : ℝ) := by push_cast; ring
  simp only [sT]
  rw [rf_succ' (-(((n + 1 : ℕ)) : ℝ)) k, h1, rf_succ' (e - 1) k, sub_add_cancel,
    rf_succ (-(n : ℝ)) k, rf_succ e k, rf_succ c k, rf_succ a k, rf_succ b k,
    Nat.factorial_succ]
  have hk0 : ((k.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp
  subst he
  ring


lemma rf_neg_self (n : ℕ) : rf (-(n : ℝ)) n = (-1) ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rf_succ' ]
    have : (-(((n + 1 : ℕ)) : ℝ)) + 1 = -(n : ℝ) := by push_cast; ring
    rw [this, ih, Nat.factorial_succ]; push_cast; ring

lemma sT_rel_last (n : ℕ) (a b c e : ℝ) (he : e = 1 + a + b - c - n)
    (hc : rf c (n + 1) ≠ 0) (he1 : rf e n ≠ 0) (he2 : e - 1 ≠ 0) :
    (c + n) * (c - a - b + n) * sT (n + 1) a b c (e - 1) (n + 1) =
      (a + n) * (b + n) * sT n a b c e n := by
  have hcn : rf c n ≠ 0 := rf_ne_zero_of_le hc (Nat.le_succ n)
  have hc' : c + n ≠ 0 := by
    rw [rf_succ] at hc; exact right_ne_zero_of_mul hc
  have h1 : (-(((n + 1 : ℕ)) : ℝ)) + 1 = -(n : ℝ) := by push_cast; ring
  have hn0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [sT]
  rw [rf_neg_self n, rf_succ' (-(((n + 1 : ℕ)) : ℝ)) n, h1, rf_neg_self n, rf_succ' (e - 1) n,
    sub_add_cancel, rf_succ c n, rf_succ a n, rf_succ b n, Nat.factorial_succ]
  push_cast
  field_simp
  subst he
  ring

theorem saal_step (n : ℕ) (a b c e : ℝ) (he : e = 1 + a + b - c - n)
    (hc : ∀ k, k ≤ n → rf c k ≠ 0) (he1 : ∀ k, k ≤ n → rf e k ≠ 0) (hc1 : rf c (n + 1) ≠ 0)
    (he2 : e - 1 ≠ 0) :
    (c + n) * (c - a - b + n) * ∑ k ∈ range (n + 2), sT (n + 1) a b c (e - 1) k =
      (c - a + n) * (c - b + n) * ∑ k ∈ range (n + 1), sT n a b c e k := by
  have key : ∀ k, k < n + 1 → (c + n) * (c - a - b + n) * sT (n + 1) a b c (e - 1) (k + 1) =
      ((c - a + n) * (c - b + n) - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        (a + k) * (b + k) * sT n a b c e k := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact sT_rel n k a b c e he (by
        have := hc (k + 1) (by omega); exact this) (he1 (k + 1) (by omega)) he2
    · rw [sT_succ_self, mul_zero, zero_add]
      exact sT_rel_last k a b c e he hc1 (he1 k le_rfl) he2
  set ρ := (c + n) * (c - a - b + n) with hρ
  set σ := (c - a + n) * (c - b + n) with hσ
  have hρσ : ρ + a * b = σ := by rw [hρ, hσ]; ring
  have h0 : ρ * ∑ k ∈ range (n + 2), sT (n + 1) a b c (e - 1) k =
      ρ + ∑ k ∈ range (n + 1), ((σ - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        (a + k) * (b + k) * sT n a b c e k) := by
    rw [Finset.sum_range_succ', mul_add, sT_zero, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k hk => key k (Finset.mem_range.mp hk)
  have e1 : ∑ k ∈ range (n + 1), ((σ - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        (a + k) * (b + k) * sT n a b c e k) =
      ∑ k ∈ range n, (σ - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        ((a * b) + ∑ k ∈ range n, (a + (k + 1 : ℕ)) * (b + (k + 1 : ℕ)) * sT n a b c e (k + 1)) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_succ, sT_succ_self, mul_zero, add_zero,
      Finset.sum_range_succ' (fun k => (a + k) * (b + k) * sT n a b c e k)]
    simp [sT_zero, add_comm]
  have e2 : ∑ k ∈ range n, (σ - (a + k + 1) * (b + k + 1)) * sT n a b c e (k + 1) +
        ∑ k ∈ range n, (a + (k + 1 : ℕ)) * (b + (k + 1 : ℕ)) * sT n a b c e (k + 1) =
      σ * ∑ k ∈ range n, sT n a b c e (k + 1) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  have e3 : ∑ k ∈ range (n + 1), sT n a b c e k = 1 + ∑ k ∈ range n, sT n a b c e (k + 1) := by
    rw [Finset.sum_range_succ', sT_zero, add_comm]
  rw [h0, e1, e3]
  linear_combination e2 + (1 : ℝ) * hρσ + 0 * e2


/-- **Pfaff–Saalschütz** for the terminating balanced `₃F₂(1)`. -/
theorem saal (a b c : ℝ) : ∀ n : ℕ, rf c n ≠ 0 → rf (1 + a + b - c - n) n ≠ 0 →
    ∑ k ∈ range (n + 1), sT n a b c (1 + a + b - c - n) k =
      (-1) ^ n * rf (c - a) n * rf (c - b) n / (rf c n * rf (1 + a + b - c - n) n) := by
  intro n
  induction n with
  | zero => intro _ _; simp [sT_zero]
  | succ n ih =>
    intro hc he
    set e : ℝ := 1 + a + b - c - n with hedef
    have he1 : (1 + a + b - c - ((n + 1 : ℕ) : ℝ)) = e - 1 := by rw [hedef]; push_cast; ring
    rw [he1] at he ⊢
    have hcn : rf c n ≠ 0 := rf_ne_zero_of_le hc (Nat.le_succ n)
    have he' : e - 1 ≠ 0 ∧ rf e n ≠ 0 := by
      rw [rf_succ', sub_add_cancel] at he
      exact ⟨left_ne_zero_of_mul he, right_ne_zero_of_mul he⟩
    have hc' : c + n ≠ 0 := by rw [rf_succ] at hc; exact right_ne_zero_of_mul hc
    have ihn := ih hcn he'.2
    have hstep := saal_step n a b c e hedef (fun k hk => rf_ne_zero_of_le hcn hk)
      (fun k hk => rf_ne_zero_of_le he'.2 hk) hc he'.1
    have hρ : (c + n) * (c - a - b + n) ≠ 0 := by
      refine mul_ne_zero hc' ?_
      have : c - a - b + n = -(e - 1) := by rw [hedef]; ring
      rw [this]; exact neg_ne_zero.mpr he'.1
    have hσ : ∑ k ∈ range (n + 2), sT (n + 1) a b c (e - 1) k =
        (c - a + n) * (c - b + n) / ((c + n) * (c - a - b + n)) *
          ∑ k ∈ range (n + 1), sT n a b c e k := by
      have hc2 : c - a - b + n ≠ 0 := right_ne_zero_of_mul hρ
      field_simp
      linear_combination hstep
    rw [hσ, ihn, rf_succ (c - a) n, rf_succ (c - b) n, rf_succ c n, rf_succ' (e - 1) n,
      sub_add_cancel]
    have h2 : c - a - b + n = -(e - 1) := by rw [hedef]; ring
    rw [h2]
    have h3 := he'.1
    have h4 := he'.2
    have h5 : (c + n) ≠ 0 := hc'
    field_simp
    ring


lemma rf_reflect' (x y : ℝ) (j : ℕ) (h : x = 1 - y - j) : rf x j = (-1) ^ j * rf y j := by
  rw [h, rf_reflect]

lemma rf_one_add (i j : ℕ) : rf (1 + i) j * i.factorial = (i + j).factorial := by
  have := rf_add 1 i j
  rw [rf_one, rf_one] at this
  have h2 : (((i + j).factorial : ℕ) : ℝ) = i.factorial * rf (1 + i) j := by exact_mod_cast this
  rw [h2]; ring

/-- The first-stage double sum term of the Sears transformation. -/
def tA (n : ℕ) (A B C d A2 A3 : ℝ) (j : ℕ) : ℝ :=
  rf (-n) j * rf A j * rf B j * rf C j / ((j.factorial : ℝ) * rf A2 j * rf A3 j * rf d j)

def tB (n : ℕ) (A D A2 A3 : ℝ) (j i : ℕ) : ℝ :=
  rf (-(n : ℝ) + j) i * rf (A + j) i * rf D i /
    ((i.factorial : ℝ) * rf (A2 + j) i * rf (A3 + j) i)

lemma term_split (n j i : ℕ) (A B C d A2 A3 : ℝ)
    (hD : rf (d - B - C) (j + i) ≠ 0) (hA2 : rf A2 (j + i) ≠ 0) (hA3 : rf A3 (j + i) ≠ 0)
    (hdj : rf d j ≠ 0) :
    rf (-(n : ℝ)) (j + i) * rf A (j + i) / (((j + i).factorial : ℝ) * rf A2 (j + i) * rf A3 (j + i)) *
      ((-1) ^ (j + i) * rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) (j + i)) *
      sT (j + i) B C d (1 + B + C - d - ((j + i : ℕ) : ℝ)) j =
    tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j i := by
  have hij : j + i = i + j := add_comm j i
  have hD' : rf (d - B - C) i * rf (d - B - C + i) j ≠ 0 := by
    rw [← rf_add, ← hij]; exact hD
  have hDi : rf (d - B - C) i ≠ 0 := left_ne_zero_of_mul hD'
  have hDij : rf (d - B - C + i) j ≠ 0 := right_ne_zero_of_mul hD'
  have hA2' : rf A2 j * rf (A2 + j) i ≠ 0 := by rw [← rf_add]; exact hA2
  have hA3' : rf A3 j * rf (A3 + j) i ≠ 0 := by rw [← rf_add]; exact hA3
  have hA2j := left_ne_zero_of_mul hA2'
  have hA2i := right_ne_zero_of_mul hA2'
  have hA3j := left_ne_zero_of_mul hA3'
  have hA3i := right_ne_zero_of_mul hA3'
  have hfact : (((j + i).factorial : ℕ) : ℝ) = i.factorial * rf (1 + i) j := by
    have h := rf_one_add i j
    rw [hij, ← h]; ring
  have hE : rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) (j + i) = (-1) ^ (j + i) * rf (d - B - C) (j + i) :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hsgn : ((-1 : ℝ) ^ (j + i)) * (-1) ^ (j + i) = 1 := by rw [← mul_pow]; simp
  have hneg : rf (-(((j + i : ℕ)) : ℝ)) j = (-1) ^ j * rf (1 + i) j :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hE2 : rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) j = (-1) ^ j * rf (d - B - C + i) j :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hDs : rf (d - B - C) (j + i) = rf (d - B - C) i * rf (d - B - C + i) j := by
    rw [hij, rf_add]
  have hsj : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  have hf1 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hf2 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hr1 : rf (1 + (i : ℝ)) j ≠ 0 := by
    intro h0
    have := rf_one_add i j
    rw [h0] at this
    have h3 : (((i + j).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact h3 (by rw [← this]; ring)
  simp only [tA, tB, sT]
  rw [rf_add (-(n : ℝ)) j i, rf_add A j i, rf_add A2 j i, rf_add A3 j i, hE, hDs, hneg, hE2, hfact]
  rw [show ((-1 : ℝ) ^ (j + i) * ((-1) ^ (j + i) * (rf (d - B - C) i * rf (d - B - C + i) j))) =
    rf (d - B - C) i * rf (d - B - C + i) j by rw [← mul_assoc, hsgn, one_mul]]
  field_simp


lemma term_split' (n k j : ℕ) (hj : j ≤ k) (A B C d A2 A3 : ℝ)
    (hD : rf (d - B - C) k ≠ 0) (hA2 : rf A2 k ≠ 0) (hA3 : rf A3 k ≠ 0)
    (hdj : rf d j ≠ 0) :
    rf (-(n : ℝ)) k * rf A k / ((k.factorial : ℝ) * rf A2 k * rf A3 k) *
      ((-1) ^ k * rf (1 + B + C - d - (k : ℝ)) k) *
      sT k B C d (1 + B + C - d - (k : ℝ)) j =
    tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j (k - j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have := term_split n j i A B C d A2 A3 hD hA2 hA3 hdj
  simpa using this


lemma final_pt (j m : ℕ) (A B C d e f : ℝ) (hbal : d + e + f = A + B + C - ((j + m : ℕ) : ℝ) + 1)
    (he : rf e (j + m) ≠ 0) (hf : rf f (j + m) ≠ 0)
    (hA2 : rf (A - e - ((j + m : ℕ) : ℝ) + 1) (j + m) ≠ 0)
    (hA3 : rf (A - f - ((j + m : ℕ) : ℝ) + 1) (j + m) ≠ 0) (hd : rf d (j + m) ≠ 0) :
    tA (j + m) A B C d (A - e - ((j + m : ℕ) : ℝ) + 1) (A - f - ((j + m : ℕ) : ℝ) + 1) j *
      ((-1) ^ (j + m - j) * rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j - (A + j)) (j + m - j) *
        rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j - (d - B - C)) (j + m - j) /
        (rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j) (j + m - j) *
          rf ((A - f - ((j + m : ℕ) : ℝ) + 1) + j) (j + m - j))) =
    rf e (j + m) * rf f (j + m) / (rf (A - e - ((j + m : ℕ) : ℝ) + 1) (j + m) *
        rf (A - f - ((j + m : ℕ) : ℝ) + 1) (j + m)) *
      (rf (-(((j + m : ℕ)) : ℝ)) j * rf A j * rf B j * rf C j /
        ((j.factorial : ℝ) * rf d j * rf e j * rf f j)) := by
  set A2 : ℝ := A - e - ((j + m : ℕ) : ℝ) + 1 with hA2d
  set A3 : ℝ := A - f - ((j + m : ℕ) : ℝ) + 1 with hA3d
  have hjm : j + m - j = m := by omega
  rw [hjm]
  have hs : ∀ x : ℝ, rf x (j + m) = rf x j * rf (x + j) m := fun x => rf_add x j m
  have e1 : rf (A2 + j - (A + j)) m = (-1) ^ m * rf (e + j) m :=
    rf_reflect' _ _ _ (by rw [hA2d]; push_cast; ring)
  have e2 : A2 + j - (d - B - C) = f + j := by rw [hA2d]; push_cast at hbal ⊢; linarith
  rw [e2, e1]
  have hej : rf e j ≠ 0 := rf_ne_zero_of_le he (by omega)
  have hfj : rf f j ≠ 0 := rf_ne_zero_of_le hf (by omega)
  have hdj : rf d j ≠ 0 := rf_ne_zero_of_le hd (by omega)
  have hA2' : rf A2 j * rf (A2 + j) m ≠ 0 := by rw [← hs]; exact hA2
  have hA3' : rf A3 j * rf (A3 + j) m ≠ 0 := by rw [← hs]; exact hA3
  have hA2j := left_ne_zero_of_mul hA2'
  have hA2m := right_ne_zero_of_mul hA2'
  have hA3j := left_ne_zero_of_mul hA3'
  have hA3m := right_ne_zero_of_mul hA3'
  have hsg : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hf0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [hs e, hs f, hs A2, hs A3]
  simp only [tA]
  rcases neg_one_pow_eq_or ℝ m with h | h <;> simp only [h] <;> field_simp


theorem sears (n : ℕ) (A B C d e f : ℝ) (hbal : d + e + f = A + B + C - n + 1)
    (hd : rf d n ≠ 0) (he : rf e n ≠ 0) (hf : rf f n ≠ 0)
    (hA2 : rf (A - e - n + 1) n ≠ 0) (hA3 : rf (A - f - n + 1) n ≠ 0)
    (h1 : ∀ k, k ≤ n → rf (1 + B + C - d - k) k ≠ 0) :
    (∑ k ∈ range (n + 1), rf (-(n : ℝ)) k * rf A k * rf (d - B) k * rf (d - C) k /
        ((k.factorial : ℝ) * rf d k * rf (A - e - n + 1) k * rf (A - f - n + 1) k)) *
      (rf (e - A) n * rf (f - A) n / (rf e n * rf f n)) =
    ∑ k ∈ range (n + 1), rf (-(n : ℝ)) k * rf A k * rf B k * rf C k /
        ((k.factorial : ℝ) * rf d k * rf e k * rf f k) := by
  set A2 : ℝ := A - e - n + 1 with hA2d
  set A3 : ℝ := A - f - n + 1 with hA3d
  -- Step 1: expand each term of the right-hand sum
  have step1 : ∀ k ∈ range (n + 1), rf (-(n : ℝ)) k * rf A k * rf (d - B) k * rf (d - C) k /
        ((k.factorial : ℝ) * rf d k * rf A2 k * rf A3 k) =
      ∑ j ∈ range (k + 1), tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j (k - j) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdk := rf_ne_zero_of_le hd hkn
    have hEk := h1 k hkn
    have hsaal := saal B C d k hdk hEk
    have hE : rf (1 + B + C - d - (k : ℝ)) k = (-1) ^ k * rf (d - B - C) k :=
      rf_reflect' _ _ _ (by ring)
    have hDk : rf (d - B - C) k ≠ 0 := by
      intro h0; apply hEk; rw [hE, h0, mul_zero]
    have hA2k := rf_ne_zero_of_le hA2 hkn
    have hA3k := rf_ne_zero_of_le hA3 hkn
    have hfk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hratio : rf (d - B) k * rf (d - C) k / rf d k =
        (-1) ^ k * rf (1 + B + C - d - (k : ℝ)) k *
          ∑ j ∈ range (k + 1), sT k B C d (1 + B + C - d - (k : ℝ)) j := by
      rw [hsaal]
      rcases neg_one_pow_eq_or ℝ k with h | h <;> simp only [h] <;> field_simp
    have e1 : rf (-(n : ℝ)) k * rf A k * rf (d - B) k * rf (d - C) k /
        ((k.factorial : ℝ) * rf d k * rf A2 k * rf A3 k) =
        rf (-(n : ℝ)) k * rf A k / ((k.factorial : ℝ) * rf A2 k * rf A3 k) *
          (rf (d - B) k * rf (d - C) k / rf d k) := by field_simp
    rw [e1, hratio, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact term_split' n k j hjk A B C d A2 A3 hDk hA2k hA3k (rf_ne_zero_of_le hdk hjk)
  -- Step 2: exchange the order of summation
  have step2 : ∑ k ∈ range (n + 1), rf (-(n : ℝ)) k * rf A k * rf (d - B) k * rf (d - C) k /
        ((k.factorial : ℝ) * rf d k * rf A2 k * rf A3 k) =
      ∑ j ∈ range (n + 1), ∑ i ∈ range (n + 1 - j), tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j i := by
    rw [Finset.sum_congr rfl step1]
    exact Finset.sum_range_diag_flip (n + 1) (fun j i => tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j i)
  -- Step 3: the inner sums are Saalschütz sums
  have step3 : ∀ j ∈ range (n + 1), ∑ i ∈ range (n + 1 - j), tA n A B C d A2 A3 j * tB n A (d - B - C) A2 A3 j i =
      tA n A B C d A2 A3 j * ((-1) ^ (n - j) * rf (A2 + j - (A + j)) (n - j) *
        rf (A2 + j - (d - B - C)) (n - j) / (rf (A2 + j) (n - j) * rf (A3 + j) (n - j))) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.mul_sum]
    congr 1
    have hc0 : rf (A2 + j) (n - j) ≠ 0 := rf_ne_zero_shift hA2 hjn
    have he0eq : (1 + (A + j) + (d - B - C) - (A2 + j) - ((n - j : ℕ) : ℝ)) = A3 + j := by
      rw [Nat.cast_sub hjn, hA2d, hA3d]; linarith [hbal]
    have he0 : rf (1 + (A + j) + (d - B - C) - (A2 + j) - ((n - j : ℕ) : ℝ)) (n - j) ≠ 0 := by
      rw [he0eq]; exact rf_ne_zero_shift hA3 hjn
    have hs := saal (A + j) (d - B - C) (A2 + j) (n - j) hc0 he0
    rw [he0eq] at hs
    have : n + 1 - j = n - j + 1 := by omega
    rw [this]
    have hT : ∀ i : ℕ, tB n A (d - B - C) A2 A3 j i = sT (n - j) (A + j) (d - B - C) (A2 + j) (A3 + j) i := by
      intro i
      simp only [tB, sT]
      rw [Nat.cast_sub hjn]; ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hT i), hs]
  -- Step 4: each term is a multiple of the term of the left-hand sum
  have step4 : ∀ j ∈ range (n + 1), tA n A B C d A2 A3 j * ((-1) ^ (n - j) * rf (A2 + j - (A + j)) (n - j) *
        rf (A2 + j - (d - B - C)) (n - j) / (rf (A2 + j) (n - j) * rf (A3 + j) (n - j))) =
      rf e n * rf f n / (rf A2 n * rf A3 n) *
        (rf (-(n : ℝ)) j * rf A j * rf B j * rf C j /
          ((j.factorial : ℝ) * rf d j * rf e j * rf f j)) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjn
    exact final_pt j m A B C d e f hbal he hf hA2 hA3 hd
  rw [step2, Finset.sum_congr rfl step3, Finset.sum_congr rfl step4, ← Finset.mul_sum]
  have hA2n : rf A2 n = (-1) ^ n * rf (e - A) n := rf_reflect' _ _ _ (by rw [hA2d]; ring)
  have hA3n : rf A3 n = (-1) ^ n * rf (f - A) n := rf_reflect' _ _ _ (by rw [hA3d]; ring)
  have hn2 : rf (e - A) n ≠ 0 := by
    intro h0; apply hA2; rw [hA2n, h0, mul_zero]
  have hn3 : rf (f - A) n ≠ 0 := by
    intro h0; apply hA3; rw [hA3n, h0, mul_zero]
  rw [hA2n, hA3n]
  rcases neg_one_pow_eq_or ℝ n with h | h <;> simp only [h] <;> field_simp

end PhyslibAlpha.Sl2.Hyper
