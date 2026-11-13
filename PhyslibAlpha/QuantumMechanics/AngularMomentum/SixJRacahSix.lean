/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJHypergeom
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJXsFormula
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacah

/-!

# From the single sum `Xs` to Racah's sum

The combinatorial identity that turns the single sum `Xs` of `SixJRacahCollapse` into Racah's sum
`racahSum6` of `SixJRacah`, by one Sears transformation (`Hyper.sears`).

## i. Overview

Write `a = v + w + k₁`, `b = z + k₁ + k₃`, `c = u + w + k₃`, `K = w + k₁ + k₃` with six free natural
numbers `k₁ k₃ u v w z`, and `N = u + v + w + z + k₁ + k₃ = a + b + c - K`. This parametrization is
exactly the region `k₁ + k₃ ≤ min b K` of the admissible `(a, b, c, K, k₁, k₃)` (it is where
`β₁ = N` is the smallest of Racah's three quadrilateral sums). In it

`Xs = Σ_x (-1)^x C(k₃,x) C(N-k₃+1, k₁-x) (u+w+x)! (b-x)! (v+w+x)! / (w+x)!`

is the balanced `₄F₃(1)` with upper parameters `-k₃, -k₁, u+w+1, v+w+1` and lower parameters
`w+1, -b, u+v+w+z+2`, and `racahSum6 (N-u) (N-k₃) (N-v) (N-k₁) N (N+z) (N+w)`, summed from the top
`t = N - s`, is the `₄F₃(1)` with upper parameters `-k₃, -k₁, -u, -v` and lower parameters
`w+1, z+1, -(N+1)`. The Sears move (`sears_instance`) takes one into the other, and the constants
are matched by factorial identities (`const_id`).

## ii. Key results

- `Xs_eq_XsS`, `racahSum6_eq_RS`: `Xs` and `racahSum6` as `₄F₃(1)` sums, up to explicit factorials.
- `sears_instance`: the Sears transformation in this instance.
- `Xs_eq_racah_six`: `Xs = (-1)^N · CxF · racahSum6 (N-u) (N-k₃) (N-v) (N-k₁) N (N+z) (N+w)`.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2.Hyper

open Finset

lemma rf_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < rf x k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rf_succ]; exact mul_pos ih (by positivity)

lemma rf_ne_zero_neg {m k : ℕ} (hk : k ≤ m) : rf (-(m : ℝ)) k ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rf_succ]
    refine mul_ne_zero (ih (by omega)) ?_
    have : (k : ℝ) < m := by exact_mod_cast hk
    linarith

/-- The `₄F₃` form of `Xs`. -/
def XsS (k1 k3 u v w z : ℕ) : ℝ :=
  ∑ k ∈ range (k3 + 1), rf (-(k3 : ℝ)) k * rf (-(k1 : ℝ)) k * rf ((u : ℝ) + w + 1) k *
    rf ((v : ℝ) + w + 1) k / ((k.factorial : ℝ) * rf ((w : ℝ) + 1) k * rf (-((z : ℝ) + k1 + k3)) k *
      rf ((u : ℝ) + v + w + z + 2) k)

/-- The `₄F₃` form of Racah's sum, summed from the top. -/
def RS (k1 k3 u v w z : ℕ) : ℝ :=
  ∑ k ∈ range (k3 + 1), rf (-(k3 : ℝ)) k * rf (-(k1 : ℝ)) k * rf (-(u : ℝ)) k * rf (-(v : ℝ)) k /
    ((k.factorial : ℝ) * rf ((w : ℝ) + 1) k * rf ((z : ℝ) + 1) k *
      rf (-((u : ℝ) + v + w + z + k1 + k3 + 1)) k)

def prefS (k1 k3 u v w z : ℕ) : ℝ :=
  rf ((z : ℝ) + 1 + k1) k3 * rf (-((u : ℝ) + v + w + z + k1 + k3 + 1) + k1) k3 /
    (rf ((z : ℝ) + 1) k3 * rf (-((u : ℝ) + v + w + z + k1 + k3 + 1)) k3)

theorem sears_instance (k1 k3 u v w z : ℕ) :
    XsS k1 k3 u v w z * prefS k1 k3 u v w z = RS k1 k3 u v w z := by
  set N : ℝ := (u : ℝ) + v + w + z + k1 + k3 with hN
  have hbal : ((w : ℝ) + 1) + ((z : ℝ) + 1) + (-(N + 1)) = -(k1 : ℝ) + (-(u : ℝ)) + (-(v : ℝ)) - k3 + 1 := by
    rw [hN]; ring
  have hNk : k3 ≤ u + v + w + z + k1 + k3 + 1 := by omega
  have hd : rf ((w : ℝ) + 1) k3 ≠ 0 := (rf_pos (by positivity) k3).ne'
  have he : rf ((z : ℝ) + 1) k3 ≠ 0 := (rf_pos (by positivity) k3).ne'
  have hf : rf (-(N + 1)) k3 ≠ 0 := by
    have := rf_ne_zero_neg (m := u + v + w + z + k1 + k3 + 1) (k := k3) hNk
    convert this using 2; rw [hN]; push_cast; ring
  have hA2 : rf (-(k1 : ℝ) - ((z : ℝ) + 1) - k3 + 1) k3 ≠ 0 := by
    have := rf_ne_zero_neg (m := z + k1 + k3) (k := k3) (by omega)
    convert this using 2; push_cast; ring
  have hA3 : rf (-(k1 : ℝ) - (-(N + 1)) - k3 + 1) k3 ≠ 0 := by
    have h0 : (0 : ℝ) ≤ (u : ℝ) + v + w + z := by positivity
    have : 0 < -(k1 : ℝ) - (-(N + 1)) - k3 + 1 := by rw [hN]; linarith
    exact (rf_pos this k3).ne'
  have h1 : ∀ k, k ≤ k3 → rf (1 + (-(u : ℝ)) + (-(v : ℝ)) - ((w : ℝ) + 1) - k) k ≠ 0 := by
    intro k hk
    have := rf_ne_zero_neg (m := u + v + w + k) (k := k) (by omega)
    convert this using 2; push_cast; ring
  have key := sears k3 (-(k1 : ℝ)) (-(u : ℝ)) (-(v : ℝ)) ((w : ℝ) + 1) ((z : ℝ) + 1) (-(N + 1)) hbal hd he hf hA2 hA3 h1
  have e1 : (w : ℝ) + 1 - (-(u : ℝ)) = (u : ℝ) + w + 1 := by ring
  have e2 : (w : ℝ) + 1 - (-(v : ℝ)) = (v : ℝ) + w + 1 := by ring
  have e3 : -(k1 : ℝ) - ((z : ℝ) + 1) - k3 + 1 = -((z : ℝ) + k1 + k3) := by ring
  have e4 : -(k1 : ℝ) - (-(N + 1)) - k3 + 1 = (u : ℝ) + v + w + z + 2 := by rw [hN]; try ring
  have e5 : (z : ℝ) + 1 - (-(k1 : ℝ)) = (z : ℝ) + 1 + k1 := by ring
  have e6 : -(N + 1) - (-(k1 : ℝ)) = -((u : ℝ) + v + w + z + k1 + k3 + 1) + k1 := by rw [hN]; ring
  have e7 : -(N + 1) = -((u : ℝ) + v + w + z + k1 + k3 + 1) := by rw [hN]
  rw [e1, e2, e3, e4, e5, e6] at key
  rw [e7] at key
  exact key


lemma rf_neg_dec (x j : ℕ) : rf (-(((x + j : ℕ)) : ℝ)) x =
    (-1) ^ x * ((x + j).factorial : ℝ) / (j.factorial : ℝ) := by
  have h := rf_reflect (1 + (j : ℝ)) x
  have e : (1 : ℝ) - (1 + j) - x = -(((x + j : ℕ)) : ℝ) := by push_cast; ring
  rw [e] at h
  rw [h]
  have h2 := rf_one_add j x
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [add_comm j x] at h2
  field_simp
  rw [← h2]

lemma rf_pos_dec (m x : ℕ) : rf ((m : ℝ) + 1) x = ((m + x).factorial : ℝ) / (m.factorial : ℝ) := by
  have h2 := rf_one_add m x
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  rw [add_comm (1 : ℝ) m] at h2
  field_simp
  rw [← h2]

lemma rf_neg_zero (m x : ℕ) (h : m < x) : rf (-(m : ℝ)) x = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show m + 1 + t = (m + 1) + t from rfl, rf_add, rf_succ]
  simp


/-- The constant relating `Xs` and its `₄F₃` form. -/
def Cx1 (k1 k3 u v w z : ℕ) : ℝ :=
  (((u + v + w + z + k1 + 1).factorial : ℝ) * ((u + w).factorial : ℝ) * ((v + w).factorial : ℝ) *
    ((z + k1 + k3).factorial : ℝ)) /
  ((k1.factorial : ℝ) * (w.factorial : ℝ) * ((u + v + w + z + 1).factorial : ℝ))

lemma term_Xs (x i j u v w z : ℕ) :
    (-1 : ℝ) ^ x * (((x + j).choose x : ℕ) : ℝ) *
        (((u + v + w + z + (x + i) + 1).choose i : ℕ) : ℝ) * ((u + w + x).factorial : ℝ) *
        ((z + x + i + j).factorial : ℝ) * ((v + w + x).factorial : ℝ) / ((w + x).factorial : ℝ) =
      Cx1 (x + i) (x + j) u v w z *
        (rf (-(((x + j : ℕ)) : ℝ)) x * rf (-(((x + i : ℕ)) : ℝ)) x * rf ((u : ℝ) + w + 1) x *
          rf ((v : ℝ) + w + 1) x /
          ((x.factorial : ℝ) * rf ((w : ℝ) + 1) x *
            rf (-((z : ℝ) + ((x + i : ℕ) : ℝ) + ((x + j : ℕ) : ℝ))) x *
            rf ((u : ℝ) + v + w + z + 2) x)) := by
  have hb : (z : ℝ) + ((x + i : ℕ) : ℝ) + ((x + j : ℕ) : ℝ) = ((x + (z + i + x + j) : ℕ) : ℝ) := by
    push_cast; ring
  have h1 : (u : ℝ) + w + 1 = ((u + w : ℕ) : ℝ) + 1 := by push_cast; ring
  have h2 : (v : ℝ) + w + 1 = ((v + w : ℕ) : ℝ) + 1 := by push_cast; ring
  have h3 : (u : ℝ) + v + w + z + 2 = ((u + v + w + z + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hb, h1, h2, h3, rf_neg_dec x j, rf_neg_dec x i, rf_neg_dec x (z + i + x + j), rf_pos_dec (u + w) x,
    rf_pos_dec (v + w) x, rf_pos_dec w x, rf_pos_dec (u + v + w + z + 1) x]
  have hc1 : (((x + j).choose x : ℕ) : ℝ) = ((x + j).factorial : ℝ) / ((x.factorial : ℝ) * (j.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : x ≤ x + j)]; simp
  have hc2 : (((u + v + w + z + (x + i) + 1).choose i : ℕ) : ℝ) =
      ((u + v + w + z + (x + i) + 1).factorial : ℝ) / ((i.factorial : ℝ) * ((u + v + w + z + x + 1).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : i ≤ u + v + w + z + (x + i) + 1),
      show u + v + w + z + (x + i) + 1 - i = u + v + w + z + x + 1 by omega]
  rw [hc1, hc2]
  simp only [Cx1]
  have e1 : z + x + i + j = z + i + x + j := by ring
  have e2 : x + (z + i + x + j) = z + (x + i) + (x + j) := by ring
  have e3 : u + v + w + z + 1 + x = u + v + w + z + x + 1 := by ring
  rw [e1, e2, e3]
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  rcases neg_one_pow_eq_or ℝ x with h | h <;> simp only [h] <;> field_simp


lemma termX (x k1 k3 u v w z : ℕ) (hx1 : x ≤ k1) (hx3 : x ≤ k3) :
    (-1 : ℝ) ^ (x : ℤ) * zbinom (k3 : ℤ) (x : ℤ) *
        zbinom (((v + w + k1 : ℕ) : ℤ) + (((z + k1 + k3 : ℕ) : ℤ) + ((u + w + k3 : ℕ) : ℤ) - k3 -
          ((w + k1 + k3 : ℕ) : ℤ)) + 1) ((k1 : ℤ) - x) *
        factZ (((u + w + k3 : ℕ) : ℤ) - k3 + x) * factZ (((z + k1 + k3 : ℕ) : ℤ) - x) *
        factZ (((v + w + k1 : ℕ) : ℤ) - k1 + x) *
        invFact (((w + k1 + k3 : ℕ) : ℤ) - k1 - k3 + x) =
      Cx1 k1 k3 u v w z *
        (rf (-(k3 : ℝ)) x * rf (-(k1 : ℝ)) x * rf ((u : ℝ) + w + 1) x * rf ((v : ℝ) + w + 1) x /
          ((x.factorial : ℝ) * rf ((w : ℝ) + 1) x * rf (-((z : ℝ) + k1 + k3)) x *
            rf ((u : ℝ) + v + w + z + 2) x)) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hx1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hx3
  have key := term_Xs x i j u v w z
  have e1 : (((v + w + (x + i) : ℕ) : ℤ) + (((z + (x + i) + (x + j) : ℕ) : ℤ) + ((u + w + (x + j) : ℕ) : ℤ) -
      ((x + j : ℕ) : ℤ) - ((w + (x + i) + (x + j) : ℕ) : ℤ)) + 1) =
      ((u + v + w + z + (x + i) + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : (((x + i : ℕ) : ℤ) - (x : ℤ)) = ((i : ℕ) : ℤ) := by push_cast; ring
  have e3 : ((u + w + (x + j) : ℕ) : ℤ) - ((x + j : ℕ) : ℤ) + (x : ℤ) = ((u + w + x : ℕ) : ℤ) := by
    push_cast; ring
  have e4 : ((z + (x + i) + (x + j) : ℕ) : ℤ) - (x : ℤ) = ((z + x + i + j : ℕ) : ℤ) := by
    push_cast; ring
  have e5 : ((v + w + (x + i) : ℕ) : ℤ) - ((x + i : ℕ) : ℤ) + (x : ℤ) = ((v + w + x : ℕ) : ℤ) := by
    push_cast; ring
  have e6 : ((w + (x + i) + (x + j) : ℕ) : ℤ) - ((x + i : ℕ) : ℤ) - ((x + j : ℕ) : ℤ) + (x : ℤ) =
      ((w + x : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, ← Collapse.natCast_choose_eq (x + j) x, ← Collapse.natCast_choose_eq,
    Collapse.factZ_natCast, Collapse.factZ_natCast, Collapse.factZ_natCast, invFact_natCast,
    zpow_natCast]
  rw [← key]; ring


lemma zbinom_zero_of {n j : ℤ} (h : ¬(0 ≤ j ∧ j ≤ n)) : zbinom n j = 0 := by
  rw [zbinom, ite_eq_right h]

theorem Xs_eq_XsS (k1 k3 u v w z : ℕ) :
    Xs ((v + w + k1 : ℕ) : ℤ) ((z + k1 + k3 : ℕ) : ℤ) ((u + w + k3 : ℕ) : ℤ) ((w + k1 + k3 : ℕ) : ℤ)
      k1 k3 = Cx1 k1 k3 u v w z * XsS k1 k3 u v w z := by
  unfold Xs
  rw [Collapse.finsum_eq_sum_range _ k3 (fun x hx => by
    rw [zbinom_zero_of (by omega : ¬(0 ≤ x ∧ x ≤ (k3 : ℤ)))]; ring)]
  unfold XsS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx3 : x ≤ k3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  by_cases hx1 : x ≤ k1
  · exact termX x k1 k3 u v w z hx1 hx3
  · rw [zbinom_zero_of (by omega : ¬(0 ≤ (k1 : ℤ) - x ∧ (k1 : ℤ) - x ≤ _)), rf_neg_zero k1 x (by omega)]
    simp


lemma rf_neg_inv (m s : ℕ) : rf (-(m : ℝ)) s = (-1) ^ s * (m.factorial : ℝ) * invFact ((m : ℤ) - s) := by
  by_cases h : s ≤ m
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [rf_neg_dec, show (((s + j : ℕ) : ℤ) - s) = (j : ℤ) by push_cast; ring, invFact_natCast]
    have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  · rw [rf_neg_zero m s (by omega), invFact_of_neg (by omega)]; ring

/-- Racah's sum, from the top, as a `₄F₃`. -/
def Cr (k1 k3 u v w z : ℕ) : ℝ :=
  (-1) ^ (u + v + w + z + k1 + k3) * ((u + v + w + z + k1 + k3 + 1).factorial : ℝ) /
    ((k3.factorial : ℝ) * (k1.factorial : ℝ) * (u.factorial : ℝ) * (v.factorial : ℝ) *
      (w.factorial : ℝ) * (z.factorial : ℝ))

lemma termR (s k1 k3 u v w z : ℕ) (hs : s ≤ k3) :
    (-1 : ℝ) ^ (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s) *
      factZ (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s + 1) *
      (invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - u)) *
        invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k3)) *
        invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - v)) *
        invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k1)) *
        (invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s)) *
          invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + z - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s)) *
          invFact (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + w - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s)))) =
    Cr k1 k3 u v w z *
      (rf (-(k3 : ℝ)) s * rf (-(k1 : ℝ)) s * rf (-(u : ℝ)) s * rf (-(v : ℝ)) s /
        ((s.factorial : ℝ) * rf ((w : ℝ) + 1) s * rf ((z : ℝ) + 1) s *
          rf (-((u : ℝ) + v + w + z + k1 + k3 + 1)) s)) := by
  generalize hM : u + v + w + z + k1 + k3 = M
  have hsM : s ≤ M := by omega
  have hMN : (M : ℝ) = (u : ℝ) + v + w + z + k1 + k3 := by rw [← hM]; push_cast; ring
  have a1 : (M : ℤ) - s - ((M : ℤ) - u) = (u : ℤ) - s := by ring
  have a2 : (M : ℤ) - s - ((M : ℤ) - k3) = (k3 : ℤ) - s := by ring
  have a3 : (M : ℤ) - s - ((M : ℤ) - v) = (v : ℤ) - s := by ring
  have a4 : (M : ℤ) - s - ((M : ℤ) - k1) = (k1 : ℤ) - s := by ring
  have a5 : (M : ℤ) - ((M : ℤ) - s) = ((s : ℕ) : ℤ) := by ring
  have a6 : (M : ℤ) + z - ((M : ℤ) - s) = ((z + s : ℕ) : ℤ) := by push_cast; ring
  have a7 : (M : ℤ) + w - ((M : ℤ) - s) = ((w + s : ℕ) : ℤ) := by push_cast; ring
  have a8 : (M : ℤ) - s + 1 = ((M + 1 - s : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : s ≤ M + 1)]; ring
  have a9 : -((u : ℝ) + v + w + z + k1 + k3 + 1) = -(((M + 1 : ℕ)) : ℝ) := by push_cast; rw [hMN]
  rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, rf_neg_inv k3, rf_neg_inv k1, rf_neg_inv u, rf_neg_inv v,
    rf_neg_inv (M + 1), rf_pos_dec w, rf_pos_dec z, invFact_natCast, invFact_natCast, invFact_natCast,
    Collapse.factZ_natCast,
    show (((M + 1 : ℕ) : ℤ) - s) = ((M + 1 - s : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : s ≤ M + 1)]; ring,
    invFact_natCast]
  simp only [Cr, hM]
  have hpw : (-1 : ℝ) ^ ((M : ℤ) - s) = (-1) ^ (M - s) := by
    rw [show ((M : ℤ) - s) = ((M - s : ℕ) : ℤ) by push_cast [Nat.cast_sub hsM]; ring, zpow_natCast]
  rw [hpw]
  have hM2 : (-1 : ℝ) ^ M = (-1) ^ (M - s) * (-1) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hsM]
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  rcases neg_one_pow_eq_or ℝ s with h | h
  · have e : (-1 : ℝ) ^ (M - s) = (-1) ^ M := by rw [h, mul_one] at hM2; exact hM2.symm
    rw [e, h]; field_simp
  · have e : (-1 : ℝ) ^ (M - s) = -(-1) ^ M := by rw [h] at hM2; linarith
    rw [e, h]; field_simp


theorem racahSum6_eq_RS (k1 k3 u v w z : ℕ) :
    racahSum6 (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - u) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k3)
      (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - v) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k1)
      ((u + v + w + z + k1 + k3 : ℕ) : ℤ) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + z)
      (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + w) = Cr k1 k3 u v w z * RS k1 k3 u v w z := by
  unfold racahSum6
  rw [← finsum_comp_equiv (Equiv.subLeft (((u + v + w + z + k1 + k3 : ℕ) : ℤ)))]
  simp only [Equiv.subLeft_apply]
  rw [Collapse.finsum_eq_sum_range _ k3 (fun s hs => ?_)]
  · unfold RS
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact termR s k1 k3 u v w z (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
  · rcases hs with hs | hs
    · rw [show ((u + v + w + z + k1 + k3 : ℕ) : ℤ) - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s) = s by ring,
        invFact_of_neg hs]; ring
    · rw [show ((u + v + w + z + k1 + k3 : ℕ) : ℤ) - s - (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k3) = (k3 : ℤ) - s by ring,
        invFact_of_neg (u := (k3 : ℤ) - s) (by omega)]; ring


/-- The constant in the identity `Xs = ± CxF · racahSum6`. -/
def CxF (k1 k3 u v w z : ℕ) : ℝ :=
  ((v + w).factorial : ℝ) * ((z + k3).factorial : ℝ) * (v.factorial : ℝ) * (u.factorial : ℝ) *
    (k3.factorial : ℝ) * ((z + k1).factorial : ℝ) * ((u + w).factorial : ℝ) /
    ((u + v + w + z + k3 + 1).factorial : ℝ)

lemma const_id (k1 k3 u v w z : ℕ) :
    Cx1 k1 k3 u v w z = (-1) ^ (u + v + w + z + k1 + k3) * CxF k1 k3 u v w z * Cr k1 k3 u v w z *
      prefS k1 k3 u v w z := by
  have h1 : (z : ℝ) + 1 + k1 = ((z + k1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have h2 : -((u : ℝ) + v + w + z + k1 + k3 + 1) + k1 = -(((k3 + (u + v + w + z + 1) : ℕ)) : ℝ) := by
    push_cast; ring
  have h3 : -((u : ℝ) + v + w + z + k1 + k3 + 1) = -(((k3 + (u + v + w + z + k1 + 1) : ℕ)) : ℝ) := by
    push_cast; ring
  unfold prefS
  rw [h1, h2, h3, rf_pos_dec (z + k1) k3, rf_pos_dec z k3, rf_neg_dec k3 (u + v + w + z + 1),
    rf_neg_dec k3 (u + v + w + z + k1 + 1)]
  simp only [Cx1, CxF, Cr]
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast Nat.factorial_ne_zero n
  have e1 : z + k1 + k3 = z + (k1 + k3) := by ring
  have e2 : k3 + (u + v + w + z + 1) = u + v + w + z + k3 + 1 := by ring
  have e3 : k3 + (u + v + w + z + k1 + 1) = u + v + w + z + k1 + k3 + 1 := by ring
  rw [e2, e3]
  rcases neg_one_pow_eq_or ℝ (u + v + w + z + k1 + k3) with h | h <;>
  rcases neg_one_pow_eq_or ℝ k3 with h' | h' <;> rw [h, h'] <;> field_simp


/-- **The Xs → Racah identity**, in the six free natural parameters `k₁ k₃ u v w z`
(`a = v + w + k₁`, `b = z + k₁ + k₃`, `c = u + w + k₃`, `K = w + k₁ + k₃`). -/
theorem Xs_eq_racah_six (k1 k3 u v w z : ℕ) :
    Xs ((v + w + k1 : ℕ) : ℤ) ((z + k1 + k3 : ℕ) : ℤ) ((u + w + k3 : ℕ) : ℤ) ((w + k1 + k3 : ℕ) : ℤ)
      k1 k3 = (-1) ^ (u + v + w + z + k1 + k3) * CxF k1 k3 u v w z *
        racahSum6 (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - u) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k3)
          (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - v) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) - k1)
          ((u + v + w + z + k1 + k3 : ℕ) : ℤ) (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + z)
          (((u + v + w + z + k1 + k3 : ℕ) : ℤ) + w) := by
  rw [Xs_eq_XsS, const_id, racahSum6_eq_RS, ← sears_instance]
  ring

end PhyslibAlpha.Sl2.Hyper
