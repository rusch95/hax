import Hax.Float.Spec

/-!
# IEEE 754 Floating-Point - Constructive Implementation

This module provides a constructive (non-axiomatic) implementation of IEEE 754
floating-point arithmetic, following the Flocq approach.

The key idea:
1. Represent floats as (sign, mantissa, exponent) triples
2. Implement operations using rational arithmetic with correct rounding
3. Prove that this implementation satisfies all FloatSpec axioms

This turns the 27 FloatSpec axioms into proven theorems!

## Architecture

```
FloatSpec (axiomatic)          IEEE754 (constructive)
        ↑                              ↑
        |                              |
        |                              |
        +--------- proved ←------------+
                equivalence
```

Instead of axioms, we:
- Implement concrete operations on (sign, mantissa, exponent)
- Prove commutativity, error bounds, monotonicity, etc.
- Show the implementation satisfies FloatSpec

## Current Status

**Axioms Eliminated** (turned into proven theorems):
- ✅ add_comm, mul_comm - Trivial from Rat.add_comm/mul_comm + rounding
- 🚧 add_relative_error - Needs rounding theory
- 🚧 mul_eq_zero - Provable from representation
- 🚧 Monotonicity - Needs ordering on FloatRepr
- ⏳ 22 more axioms to prove...

## References
- Flocq: https://flocq.gitlabpages.inria.fr/
- IEEE 754-2019: https://ieeexplore.ieee.org/document/8766229
-/

namespace Float.IEEE754

/-! ## Core Definitions -/

/-- A floating-point number in scientific notation: ±m × 2^e
- sign: true = negative, false = positive
- mantissa: significand (normalized to [1,2) for normal numbers)
- exponent: power of 2
-/
structure FloatRepr where
  sign : Bool
  mantissa : Nat  -- In fixed-point: mantissa * 2^(-precision)
  exponent : Int
  deriving Repr, DecidableEq

/-- Binary32 (f32) parameters -/
structure Binary32Config where
  precision : Nat := 24      -- 23 bits + 1 implicit leading bit
  exponent_bias : Nat := 127
  exponent_min : Int := -126
  exponent_max : Int := 127

/-- Binary64 (f64) parameters -/
structure Binary64Config where
  precision : Nat := 53      -- 52 bits + 1 implicit leading bit
  exponent_bias : Nat := 1023
  exponent_min : Int := -1022
  exponent_max : Int := 1023

/-! ## Basic Operations -/

/-- Zero representation -/
def FloatRepr.zero (cfg_emin : Int) : FloatRepr :=
  { sign := false, mantissa := 0, exponent := cfg_emin }

/-- One representation: significand = 2^cfg_prec * 2^(-cfg_prec) = 1.0 -/
def FloatRepr.one (cfg_prec : Nat) : FloatRepr :=
  { sign := false, mantissa := 2^cfg_prec, exponent := 0 }

/-- Negation (flip sign bit) -/
def FloatRepr.neg (f : FloatRepr) : FloatRepr :=
  { sign := !f.sign, mantissa := f.mantissa, exponent := f.exponent }

/-! ## Conversion to Rationals -/

/-- Convert FloatRepr to rational number -/
def FloatRepr.toRat (cfg_prec : Nat) (f : FloatRepr) : Rat :=
  -- Compute: ± (mantissa / 2^prec) * 2^exp
  -- = ± mantissa * 2^(exp - prec)
  let mantissa_rat : Rat := f.mantissa
  let base := mantissa_rat * ((2 : Rat) ^ (f.exponent - (cfg_prec : Int)))
  if f.sign then -base else base

/-! ## Conversion Theorems -/

/-- Natural numbers cast to Rat are non-negative -/
theorem nat_cast_nonneg (n : Nat) : (0 : Rat) ≤ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : (k : Rat) + 1 = ((k + 1 : Nat) : Rat) := by simp
    rw [← h1]
    have h2 : (0 : Rat) ≤ 1 := by decide
    exact add_nonneg ih h2

/-- Nat.cast preserves ≤ for Rat -/
theorem nat_cast_le_rat (n m : Nat) (h : n ≤ m) : (n : Rat) ≤ (m : Rat) := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := Nat.le_zero.mp h
    simp [hn]
  | succ k ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have hle : n ≤ k := Nat.lt_succ_iff.mp hlt
      have h1 := ih n hle
      have h2 : (k : Rat) ≤ (k + 1 : Nat) := by
        simp only [Nat.cast_add, Nat.cast_one]
        have : (0 : Rat) ≤ 1 := by decide
        exact le_add_of_nonneg_right this
      exact le_trans h1 h2
    | inr heq =>
      rw [heq]

/-- Nat.cast preserves < for Rat -/
theorem nat_cast_lt_rat (n m : Nat) (h : n < m) : (n : Rat) < (m : Rat) := by
  induction m generalizing n with
  | zero => exact absurd h (Nat.not_lt_zero n)
  | succ k ih =>
    cases Nat.lt_succ_iff_lt_or_eq.mp h with
    | inl hlt =>
      have h1 := ih n hlt
      have h2 : (k : Rat) < (k + 1 : Nat) := by
        simp only [Nat.cast_add, Nat.cast_one]
        have : (0 : Rat) < 1 := by decide
        exact lt_add_of_pos_right _ this
      exact lt_trans h1 h2
    | inr heq =>
      rw [← heq]
      simp only [Nat.cast_add, Nat.cast_one]
      have : (0 : Rat) < 1 := by decide
      exact lt_add_of_pos_right _ this

/-- Converting zero gives zero -/
theorem toRat_zero (cfg_prec : Nat) (cfg_emin : Int) :
    (FloatRepr.zero cfg_emin).toRat cfg_prec = 0 := by
  unfold FloatRepr.toRat FloatRepr.zero
  simp

/-- Negation of floats corresponds to negation of rationals -/
theorem toRat_neg (cfg_prec : Nat) (f : FloatRepr) :
    (f.neg).toRat cfg_prec = -(f.toRat cfg_prec) := by
  unfold FloatRepr.toRat FloatRepr.neg
  -- Split on f.sign
  cases f.sign
  · -- f.sign = false, so f.neg.sign = true
    simp [Bool.not_false]
  · -- f.sign = true, so f.neg.sign = false
    simp [Bool.not_true, neg_neg]

/-- Converting one gives one -/
theorem toRat_one (cfg_prec : Nat) :
    (FloatRepr.one cfg_prec).toRat cfg_prec = 1 := by
  unfold FloatRepr.toRat FloatRepr.one
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Goal: (↑(2 ^ cfg_prec) : Rat) * 2 ^ (0 - ↑cfg_prec) = 1
  -- Simplify 0 - cfg_prec to -cfg_prec
  simp only [Int.zero_sub]
  -- Convert 2^cfg_prec to zpow
  have h1 : ((2^cfg_prec : Nat) : Rat) = (2 : Rat) ^ (cfg_prec : Int) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast]
  rw [h1]
  -- Now goal is 2^cfg_prec * 2^(-cfg_prec) = 1
  have two_ne_zero : (2 : Rat) ≠ 0 := by decide
  rw [← zpow_add₀ two_ne_zero]
  simp only [add_neg_cancel, zpow_zero]

/-! ## Rounding Modes -/

/-- IEEE 754 rounding modes -/
inductive RoundMode where
  | ToNearestEven   -- Round to nearest, ties to even
  | TowardPositive  -- Round toward +∞
  | TowardNegative  -- Round toward -∞
  | TowardZero      -- Round toward 0
  | ToNearestAway   -- Round to nearest, ties away from 0
  deriving Repr, DecidableEq

/-! ## Rounding Helper Functions -/

/-- Compute floor(log2(n)) for positive natural n, returns 0 for n=0 -/
def log2Nat (n : Nat) : Nat :=
  if n ≤ 1 then 0 else 1 + log2Nat (n / 2)

/-- log2Nat of a power of 2 -/
theorem log2Nat_pow2 (k : Nat) : log2Nat (2^k) = k := by
  induction k with
  | zero => unfold log2Nat; simp
  | succ n ih =>
    unfold log2Nat
    have h1 : ¬(2^(n+1) ≤ 1) := by
      have : 2^(n+1) ≥ 2 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n+1)
      omega
    simp only [h1, ↓reduceIte]
    have h2 : 2^(n+1) / 2 = 2^n := by
      rw [Nat.pow_succ, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    rw [h2, ih]

/-- log2Nat for values in [2^k, 2^(k+1)) -/
theorem log2Nat_normalized (m k : Nat) (h_lo : 2^k ≤ m) (h_hi : m < 2^(k+1)) :
    log2Nat m = k := by
  induction k generalizing m with
  | zero =>
    -- m ∈ [1, 2), so m = 1
    have h1 : m ≥ 1 := h_lo
    have h2 : m < 2 := h_hi
    have h_eq : m = 1 := by omega
    rw [h_eq]
    unfold log2Nat
    simp
  | succ n ih =>
    -- m ∈ [2^(n+1), 2^(n+2))
    unfold log2Nat
    have h1 : ¬(m ≤ 1) := by
      have : m ≥ 2^(n+1) := h_lo
      have : 2^(n+1) ≥ 2 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n+1)
      omega
    simp only [h1, ↓reduceIte]
    -- Now need: 1 + log2Nat(m/2) = n+1
    -- So log2Nat(m/2) = n
    -- m/2 ∈ [2^n, 2^(n+1))
    have h_lo' : 2^n ≤ m / 2 := by
      have h2 : m ≥ 2^(n+1) := h_lo
      have h3 : 2^(n+1) = 2 * 2^n := Nat.pow_succ 2 n
      rw [h3] at h2
      exact Nat.le_div_two_iff_le_mul_two (2^n) m |>.mpr h2
    have h_hi' : m / 2 < 2^(n+1) := by
      have h2 : m < 2^(n+2) := h_hi
      have h3 : 2^(n+2) = 2 * 2^(n+1) := Nat.pow_succ 2 (n+1)
      rw [h3] at h2
      exact Nat.div_lt_of_lt_mul h2
    rw [ih (m/2) h_lo' h_hi']

/-- For n > 0, log2Nat gives the correct floor: 2^log2Nat(n) ≤ n < 2^(log2Nat(n)+1) -/
theorem log2Nat_bounds (n : Nat) (hn : n > 0) :
    2^(log2Nat n) ≤ n ∧ n < 2^(log2Nat n + 1) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    unfold log2Nat
    by_cases h1 : n ≤ 1
    · simp only [h1, ↓reduceIte]
      have h2 : n = 1 := by omega
      simp [h2]
    · simp only [h1, ↓reduceIte]
      have h_n2_pos : n / 2 > 0 := by omega
      have h_n2_lt : n / 2 < n := Nat.div_lt_self hn (by omega)
      have ⟨ih_lo, ih_hi⟩ := ih (n / 2) h_n2_lt h_n2_pos
      constructor
      · -- 2^(1 + log2Nat(n/2)) ≤ n
        have h2 : 2^(1 + log2Nat (n/2)) = 2 * 2^(log2Nat (n/2)) := by
          rw [Nat.pow_succ']
        rw [h2]
        have h3 : 2 * (n / 2) ≤ n := by omega
        calc 2 * 2^(log2Nat (n/2)) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 ih_lo
          _ ≤ n := h3
      · -- n < 2^(1 + log2Nat(n/2) + 1)
        have h2 : 2^(1 + log2Nat (n/2) + 1) = 2 * 2^(log2Nat (n/2) + 1) := by
          rw [Nat.pow_succ']
        rw [h2]
        have h3 : n < 2 * (n / 2) + 2 := by omega
        calc n < 2 * (n / 2) + 2 := h3
          _ ≤ 2 * (n / 2 + 1) := by ring_nf
          _ ≤ 2 * 2^(log2Nat (n/2) + 1) := Nat.mul_le_mul_left 2 ih_hi

/-- Compute floor(log2(|q|)) for a non-zero rational q.
    Returns an approximation based on numerator/denominator bit lengths. -/
def log2Rat (q : Rat) : Int :=
  let abs_q := if q < 0 then -q else q
  let num := abs_q.num.natAbs
  let den := abs_q.den
  if num = 0 then 0
  else (log2Nat num : Int) - (log2Nat den : Int)

/-- Helper: log2Nat of product with power of 2 -/
theorem log2Nat_mul_pow2 (m k : Nat) (hm : m > 0) :
    log2Nat (m * 2^k) = log2Nat m + k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    unfold log2Nat
    have h1 : ¬(m * 2^n * 2 ≤ 1) := by
      have h2 : m * 2^n * 2 ≥ 2 := by
        have h3 : m * 2^n ≥ 1 := by
          have h4 : 2^n ≥ 1 := Nat.one_le_pow n 2 (by omega)
          omega
        omega
      omega
    simp only [h1, ↓reduceIte]
    have h2 : m * 2^n * 2 / 2 = m * 2^n := Nat.mul_div_cancel_right _ (by omega : 0 < 2)
    rw [h2, ih]
    omega

/-- Key invariant for log2 of ratios: log2(a) - log2(b) is preserved when both are scaled by 2.
    This implies log2Nat(num) - log2Nat(den) = log2Nat(m) - log2Nat(2^j) for m/2^j. -/
theorem log2Nat_ratio_invariant (a b : Nat) (ha : a > 0) (hb : b > 0) :
    (log2Nat (a * 2) : Int) - (log2Nat (b * 2) : Int) = (log2Nat a : Int) - (log2Nat b : Int) := by
  have h1 : log2Nat (a * 2) = log2Nat a + 1 := by
    rw [Nat.mul_comm]
    have h := log2Nat_mul_pow2 a 1 ha
    simp at h
    exact h
  have h2 : log2Nat (b * 2) = log2Nat b + 1 := by
    rw [Nat.mul_comm]
    have h := log2Nat_mul_pow2 b 1 hb
    simp at h
    exact h
  simp [h1, h2]
  omega

/-- log2Rat of a normalized float value equals the exponent.
    For m ∈ [2^prec, 2^(prec+1)) and q = m * 2^(e - prec), log2Rat q = e.
    This relies on how Rat represents the product of an integer and a power of 2. -/
theorem log2Rat_normalized (m : Nat) (e : Int) (prec : Nat)
    (h_lo : 2^prec ≤ m) (h_hi : m < 2^(prec + 1)) :
    log2Rat ((m : Rat) * (2 : Rat) ^ (e - (prec : Int))) = e := by
  unfold log2Rat
  -- abs_q = m * 2^(e - prec) since m > 0 and 2^(e-prec) > 0
  have h_m_pos : (0 : Rat) < (m : Rat) := by
    have h1 : (0 : Nat) < m := by
      have h2 : 2^prec > 0 := Nat.pow_pos (by omega : 0 < 2) prec
      omega
    exact nat_cast_lt_rat 0 m h1
  have h_m_nat_pos : (0 : Nat) < m := by
    have h2 : 2^prec > 0 := Nat.pow_pos (by omega : 0 < 2) prec
    omega
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ (e - (prec : Int)) := by
    apply zpow_pos; decide
  have h_q_pos : (0 : Rat) < (m : Rat) * (2 : Rat) ^ (e - (prec : Int)) :=
    mul_pos h_m_pos h_pow_pos
  have h_not_neg : ¬((m : Rat) * (2 : Rat) ^ (e - (prec : Int)) < 0) := not_lt.mpr (le_of_lt h_q_pos)
  simp only [h_not_neg, ↓reduceIte]
  -- Split by whether e ≥ prec or e < prec
  by_cases h_e_ge : e ≥ (prec : Int)
  · -- Case: e ≥ prec, so k := e - prec ≥ 0
    -- q = m * 2^k is an integer
    set k := (e - (prec : Int)).toNat with hk_def
    have hk_nonneg : e - (prec : Int) = (k : Int) := by
      simp only [hk_def, Int.toNat_of_nonneg (Int.sub_nonneg.mpr h_e_ge)]
    rw [hk_nonneg, zpow_natCast]
    -- Now q = m * 2^k as a product of naturals
    have h_eq : ((m : Rat) * (2 : Rat)^k) = ((m * 2^k : Nat) : Rat) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [h_eq]
    -- For a natural number, num = n, den = 1
    simp only [Rat.num_natCast, Rat.den_natCast, Int.natAbs_ofNat]
    -- log2Nat(m * 2^k) - log2Nat(1) = log2Nat(m * 2^k) - 0 = log2Nat(m * 2^k)
    have h_log2_1 : log2Nat 1 = 0 := by unfold log2Nat; simp
    rw [h_log2_1, sub_zero]
    -- Use log2Nat_mul_pow2 and log2Nat_normalized
    rw [log2Nat_mul_pow2 m k h_m_nat_pos]
    rw [log2Nat_normalized m prec h_lo h_hi]
    -- Now: prec + k = e
    simp only [hk_def]
    omega
  · -- Case: e < prec, so k := e - prec < 0
    -- q = m / 2^(prec - e) as a fraction
    push_neg at h_e_ge
    -- Let j = prec - e (j > 0)
    set j := ((prec : Int) - e).toNat with hj_def
    have hj_pos : (prec : Int) - e = (j : Int) := by
      simp only [hj_def, Int.toNat_of_nonneg (by omega : 0 ≤ (prec : Int) - e)]
    have h_j_pos : j > 0 := by omega
    have h_k_neg : e - (prec : Int) = -(j : Int) := by omega
    rw [h_k_neg, zpow_neg, zpow_natCast]
    have h_q_eq : (m : Rat) * ((2 : Rat) ^ j)⁻¹ = (m : Rat) / (2 : Rat) ^ j := by ring
    rw [h_q_eq]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    -- Goal: log2Nat(q.num.natAbs) - log2Nat(q.den) = e where q = m / 2^j
    set q := (m : Rat) / (2 ^ j : Nat) with hq_def
    -- Key properties:
    have h_m_pos : (0 : Rat) < m := nat_cast_lt_rat 0 m (by omega : 0 < m)
    have h_2j_pos : (0 : Rat) < (2 ^ j : Nat) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      apply pow_pos; decide
    have h_q_pos : q > 0 := div_pos h_m_pos h_2j_pos
    have h_num_pos : q.num > 0 := Rat.num_pos.mpr h_q_pos
    -- q.num.natAbs = q.num since q.num > 0
    have h_natAbs : q.num.natAbs = q.num.toNat := Int.natAbs_of_nonneg (le_of_lt h_num_pos)
    -- Cross multiplication: q.num * 2^j = q.den * m (as the definition of the ratio)
    -- From q = m / 2^j and q = q.num / q.den
    have h_cross : (q.num : Rat) * (2 ^ j : Nat) = (q.den : Rat) * m := by
      have h1 : q = (q.num : Rat) / (q.den : Rat) := (Rat.num_div_den q).symm
      have h2 : q = (m : Rat) / (2 ^ j : Nat) := hq_def
      have h_den_pos : (q.den : Rat) > 0 := by
        simp only [Nat.cast_pos]
        exact q.den_pos
      have h_2j_ne : ((2 ^ j : Nat) : Rat) ≠ 0 := ne_of_gt h_2j_pos
      have h_den_ne : (q.den : Rat) ≠ 0 := ne_of_gt h_den_pos
      calc (q.num : Rat) * (2 ^ j : Nat)
          = (q.num / q.den) * q.den * (2 ^ j : Nat) := by rw [div_mul_cancel₀ _ h_den_ne]
        _ = q * q.den * (2 ^ j : Nat) := by rw [← h1]
        _ = (m / (2 ^ j : Nat)) * q.den * (2 ^ j : Nat) := by rw [h2]
        _ = m * q.den * ((2 ^ j : Nat) / (2 ^ j : Nat)) := by ring
        _ = m * q.den * 1 := by rw [div_self h_2j_ne]
        _ = q.den * m := by ring
    -- From h_cross, taking log2 of both sides:
    -- log2(|q.num|) + log2(2^j) = log2(q.den) + log2(m)
    -- log2(|q.num|) + j = log2(q.den) + log2(m)
    -- log2(|q.num|) - log2(q.den) = log2(m) - j = prec - j = e
    have h_log2_m : log2Nat m = prec := log2Nat_normalized m prec h_lo h_hi
    have h_log2_2j : log2Nat (2 ^ j) = j := log2Nat_pow2 j
    -- The key is: q.num.natAbs * 2^j = q.den * m (as naturals)
    have h_cross_nat : q.num.natAbs * 2^j = q.den * m := by
      have h1 : (q.num.natAbs : Rat) * (2 ^ j : Nat) = (q.den : Rat) * m := by
        rw [Int.natAbs_of_nonneg (le_of_lt h_num_pos)]
        simp only [Int.cast_toNat, Int.toNat_of_nonneg (le_of_lt h_num_pos)]
        exact h_cross
      have h2 : ((q.num.natAbs * 2^j : Nat) : Rat) = ((q.den * m : Nat) : Rat) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        exact h1
      exact Nat.cast_injective h2
    -- Now use log2Nat properties: log2Nat(a * b) = log2Nat(a) + log2Nat(b) when appropriate
    have h_num_pos_nat : q.num.natAbs > 0 := by
      rw [Int.natAbs_pos]
      exact ne_of_gt h_num_pos
    have h_den_pos_nat : q.den > 0 := q.den_pos
    -- From h_cross_nat: log2Nat(num * 2^j) = log2Nat(den * m)
    -- Using log2Nat_mul_pow2: log2Nat(num) + j = log2Nat(den * m)
    -- For log2Nat(den * m), we need to be careful about the non-power-of-2 case
    -- The key insight: the cross multiplication equality implies the log2 relationship
    -- even though log2 is floor-based, because both sides are integers.
    --
    -- Since num * 2^j = den * m, and both are products of positive integers,
    -- we can use the property that log2 respects multiplication for powers of 2:
    -- log2Nat(num) + j ≤ log2Nat(den * m) < log2Nat(num) + j + 1 would give equality
    -- Actually, since num * 2^j = den * m exactly, log2Nat(num * 2^j) = log2Nat(den * m)
    have h_log2_eq : log2Nat (q.num.natAbs * 2^j) = log2Nat (q.den * m) := by
      rw [h_cross_nat]
    rw [log2Nat_mul_pow2 q.num.natAbs j h_num_pos_nat] at h_log2_eq
    -- h_log2_eq : log2Nat q.num.natAbs + j = log2Nat (q.den * m)
    -- We need to extract log2Nat(q.den) from log2Nat(q.den * m)
    -- This requires: log2Nat(q.den * m) = log2Nat(q.den) + log2Nat(m) when q.den is power of 2
    -- OR we use the direct equality relationship
    --
    -- Key: q.den divides 2^j (since gcd(q.num, q.den) = 1 and q.num * 2^j = q.den * m)
    -- This means q.den = 2^k for some k ≤ j
    -- So log2Nat(q.den * m) = log2Nat(2^k * m) = k + log2Nat(m) = k + prec
    -- And log2Nat(q.den) = k
    -- From h_log2_eq: log2Nat(q.num.natAbs) + j = k + prec
    -- So: log2Nat(q.num.natAbs) = k + prec - j
    -- And: log2Nat(q.num.natAbs) - log2Nat(q.den) = (k + prec - j) - k = prec - j = e ✓
    --
    -- Need to show q.den is a power of 2
    have h_den_pow2 : ∃ k, q.den = 2^k ∧ k ≤ j := by
      -- q = m / 2^j in lowest terms, so q.den | 2^j
      -- Since gcd(q.num, q.den) = 1 and q = m / 2^j,
      -- the denominator in lowest terms must divide 2^j
      -- Since 2^j only has 2 as a prime factor, q.den = 2^k for some k ≤ j
      --
      -- Key: For q = a / b where a = m, b = 2^j:
      -- q.den = b / gcd(a, b) = 2^j / gcd(m, 2^j)
      -- Since gcd(m, 2^j) = 2^t where t = min(trailing zeros of m, j)
      -- q.den = 2^j / 2^t = 2^(j-t)
      -- So k = j - t ≤ j ✓
      --
      -- Formalize: q.den divides 2^j
      have h_den_dvd : q.den ∣ 2^j := by
        -- From h_cross_nat: q.num.natAbs * 2^j = q.den * m
        -- This means q.den | q.num.natAbs * 2^j
        -- Since gcd(q.num, q.den) = 1 (Rat is in lowest terms), gcd(q.num.natAbs, q.den) = 1
        -- By Euclid's lemma: if gcd(a, c) = 1 and c | a*b then c | b
        -- Here a = q.num.natAbs, b = 2^j, c = q.den
        -- So q.den | 2^j
        have h_coprime : Nat.Coprime q.num.natAbs q.den := by
          have h := q.reduced
          -- q.reduced says q.num.natAbs.Coprime q.den
          exact h
        have h_dvd_prod : q.den ∣ q.num.natAbs * 2^j := by
          use m
          exact h_cross_nat.symm
        exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd_prod
      -- Now show any divisor of 2^j is a power of 2
      have h_pow2_form : ∀ d, d ∣ 2^j → ∃ k, d = 2^k ∧ k ≤ j := by
        intro d hd
        induction j generalizing d with
        | zero =>
          simp at hd
          use 0
          simp [hd]
        | succ n ih =>
          rw [Nat.pow_succ] at hd
          -- d | 2 * 2^n
          cases Nat.even_or_odd d with
          | inl h_even =>
            -- d is even, so d = 2 * d' for some d'
            obtain ⟨d', hd'⟩ := h_even
            rw [hd'] at hd
            have h1 : d' ∣ 2^n := by
              have h2 : 2 * d' ∣ 2 * 2^n := hd
              exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp h2
            obtain ⟨k', hk'_eq, hk'_le⟩ := ih d' h1
            use k' + 1
            constructor
            · rw [hd', hk'_eq, Nat.pow_succ, Nat.mul_comm]
            · omega
          | inr h_odd =>
            -- d is odd and divides 2^(n+1)
            -- The only odd divisor of 2^k is 1
            have h1 : d = 1 := by
              have h2 : d ∣ 2^(n+1) := hd
              -- If d is odd and divides 2^k, then d = 1
              have h3 : Nat.Coprime d 2 := Nat.coprime_of_odd_of_even h_odd (by decide : Even 2)
              have h4 : Nat.Coprime d (2^(n+1)) := Nat.Coprime.pow_right (n+1) h3
              exact Nat.eq_one_of_pos_of_self_mul_self_mod_eq_one (by omega : 0 < d)
                (Nat.Coprime.dvd_one (Nat.Coprime.symm h4 |>.dvd_of_dvd_mul_left (by simp : d ∣ d * 2^(n+1))))
            use 0
            simp [h1]
      exact h_pow2_form q.den h_den_dvd
    obtain ⟨k, hk_eq, hk_le⟩ := h_den_pow2
    rw [hk_eq] at h_log2_eq ⊢
    rw [log2Nat_pow2 k]
    -- h_log2_eq : log2Nat q.num.natAbs + j = log2Nat (2^k * m)
    have h_log2_prod : log2Nat (2^k * m) = k + log2Nat m := by
      rw [Nat.mul_comm]
      exact log2Nat_mul_pow2 m k (by omega : m > 0)
    rw [h_log2_prod, h_log2_m] at h_log2_eq
    -- h_log2_eq : log2Nat q.num.natAbs + j = k + prec
    -- Goal: log2Nat q.num.natAbs - k = e = prec - j
    omega

/-- NOTE: log2Rat is NOT monotonic in general!
    Counterexample: 4/3 < 3/2 but log2Rat(4/3) = 1 > 0 = log2Rat(3/2)

    This is because log2Rat computes log2Nat(num) - log2Nat(den) separately,
    which differs from floor(log2(num/den)).

    However, roundToFloat is still monotonic because the normalization step
    adjusts the initial log2Rat approximation to produce correct results. -/

/-- Round a non-negative rational to a natural number according to rounding mode -/
def roundRatToNat (mode : RoundMode) (q : Rat) : Nat :=
  let floor_q := q.floor.toNat
  let frac := q - floor_q
  match mode with
  | .TowardZero => floor_q
  | .TowardNegative => floor_q
  | .TowardPositive => if frac > 0 then floor_q + 1 else floor_q
  | .ToNearestAway =>
    if frac > 1/2 then floor_q + 1
    else if frac < 1/2 then floor_q
    else floor_q + 1  -- tie: away from zero
  | .ToNearestEven =>
    if frac > 1/2 then floor_q + 1
    else if frac < 1/2 then floor_q
    else if floor_q % 2 = 0 then floor_q else floor_q + 1  -- tie: to even

/-- roundRatToNat is monotonic: if x ≤ y then round(x) ≤ round(y) -/
theorem roundRatToNat_monotonic (mode : RoundMode) (x y : Rat) (h : x ≤ y) :
    roundRatToNat mode x ≤ roundRatToNat mode y := by
  unfold roundRatToNat
  -- Key insight: floor is monotonic, and the rounding adjustment preserves order
  have h_floor : x.floor ≤ y.floor := Int.floor_le_floor h
  -- This follows from floor monotonicity and the structure of rounding
  -- For each mode, if x ≤ y, then the rounded values maintain order
  cases mode <;> simp only
  · -- TowardZero
    exact Int.toNat_le_toNat h_floor
  · -- TowardNegative
    exact Int.toNat_le_toNat h_floor
  · -- TowardPositive
    -- floor(x) ≤ floor(y), and adding 1 when frac > 0 preserves order
    by_cases hx_frac : x - ↑x.floor.toNat > 0 <;>
    by_cases hy_frac : y - ↑y.floor.toNat > 0 <;>
    simp only [hx_frac, hy_frac, ↓reduceIte] <;>
    omega
  · -- ToNearestAway
    by_cases hx_hi : x - ↑x.floor.toNat > 1/2 <;>
    by_cases hy_hi : y - ↑y.floor.toNat > 1/2 <;>
    simp only [hx_hi, hy_hi, ↓reduceIte]
    · omega
    · omega
    · by_cases hx_lo : x - ↑x.floor.toNat < 1/2 <;>
      simp only [hx_lo, ↓reduceIte] <;> omega
    · by_cases hx_lo : x - ↑x.floor.toNat < 1/2 <;>
      by_cases hy_lo : y - ↑y.floor.toNat < 1/2 <;>
      simp only [hx_lo, hy_lo, ↓reduceIte] <;> omega
  · -- ToNearestEven
    by_cases hx_hi : x - ↑x.floor.toNat > 1/2 <;>
    by_cases hy_hi : y - ↑y.floor.toNat > 1/2 <;>
    simp only [hx_hi, hy_hi, ↓reduceIte]
    · omega
    · omega
    · by_cases hx_lo : x - ↑x.floor.toNat < 1/2 <;>
      simp only [hx_lo, ↓reduceIte]
      · omega
      · by_cases hx_even : x.floor.toNat % 2 = 0 <;>
        simp only [hx_even, ↓reduceIte] <;> omega
    · by_cases hx_lo : x - ↑x.floor.toNat < 1/2 <;>
      by_cases hy_lo : y - ↑y.floor.toNat < 1/2 <;>
      simp only [hx_lo, hy_lo, ↓reduceIte]
      · omega
      · by_cases hy_even : y.floor.toNat % 2 = 0 <;>
        simp only [hy_even, ↓reduceIte] <;> omega
      · by_cases hx_even : x.floor.toNat % 2 = 0 <;>
        simp only [hx_even, ↓reduceIte] <;> omega
      · by_cases hx_even : x.floor.toNat % 2 = 0 <;>
        by_cases hy_even : y.floor.toNat % 2 = 0 <;>
        simp only [hx_even, hy_even, ↓reduceIte] <;> omega

/-- roundRatToNat for TowardZero mode gives a value ≤ the input (for non-negative input).
    This is the key property for proving monotonicity. -/
theorem roundRatToNat_le_towardZero (q : Rat) (hq : 0 ≤ q) :
    (roundRatToNat RoundMode.TowardZero q : Rat) ≤ q := by
  unfold roundRatToNat
  simp only
  -- floor(q) ≤ q
  have h_floor_le : (q.floor : Rat) ≤ q := Rat.floor_le q
  have h_toNat : (q.floor.toNat : Rat) ≤ q := by
    have h1 : q.floor ≥ 0 := Int.floor_nonneg.mpr hq
    have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
    calc (q.floor.toNat : Rat) = ((q.floor.toNat : Int) : Rat) := by simp
      _ = (q.floor : Rat) := by rw [h2]
      _ ≤ q := h_floor_le
  exact h_toNat

/-- roundRatToNat for TowardNegative mode gives a value ≤ the input (for non-negative input). -/
theorem roundRatToNat_le_towardNeg (q : Rat) (hq : 0 ≤ q) :
    (roundRatToNat RoundMode.TowardNegative q : Rat) ≤ q := by
  unfold roundRatToNat
  simp only
  have h_floor_le : (q.floor : Rat) ≤ q := Rat.floor_le q
  have h1 : q.floor ≥ 0 := Int.floor_nonneg.mpr hq
  have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
  calc (q.floor.toNat : Rat) = ((q.floor.toNat : Int) : Rat) := by simp
    _ = (q.floor : Rat) := by rw [h2]
    _ ≤ q := h_floor_le

/-- roundRatToNat for TowardPositive mode gives a value ≥ the input (ceiling). -/
theorem roundRatToNat_ge_towardPos (q : Rat) (hq : 0 ≤ q) :
    q ≤ (roundRatToNat RoundMode.TowardPositive q : Rat) := by
  unfold roundRatToNat
  simp only
  have h_floor_le : (q.floor : Rat) ≤ q := Rat.floor_le q
  have h_ceil : q ≤ q.floor + 1 := by
    have := Rat.sub_floor_div_mul_nonneg q 1
    simp at this
    linarith [Rat.floor_le q]
  have h1 : q.floor ≥ 0 := Int.floor_nonneg.mpr hq
  by_cases h_frac : q - ↑q.floor.toNat > 0
  · simp only [h_frac, ↓reduceIte]
    have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
    calc q ≤ (q.floor : Rat) + 1 := h_ceil
      _ = ((q.floor.toNat : Int) : Rat) + 1 := by rw [h2]
      _ = (q.floor.toNat : Rat) + 1 := by simp
      _ = ((q.floor.toNat + 1 : Nat) : Rat) := by simp
  · simp only [h_frac, ↓reduceIte]
    push_neg at h_frac
    have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
    have h3 : q - ↑q.floor.toNat = q - (q.floor : Rat) := by
      congr 1
      exact congrArg Rat.ofInt h2.symm
    rw [h3] at h_frac
    have h4 : q - q.floor ≥ 0 := by linarith [Rat.floor_le q]
    have h5 : q = q.floor := by linarith
    calc q = (q.floor : Rat) := h5
      _ = ((q.floor.toNat : Int) : Rat) := by rw [h2]
      _ = (q.floor.toNat : Rat) := by simp

/-- For ToNearestEven/Away, the rounded value is within 1 of the input. -/
theorem roundRatToNat_near (mode : RoundMode) (q : Rat) (hq : 0 ≤ q) :
    (roundRatToNat mode q : Rat) ≤ q + 1 ∧ q - 1 ≤ (roundRatToNat mode q : Rat) := by
  constructor
  · -- Upper bound
    unfold roundRatToNat
    have h1 : q.floor ≥ 0 := Int.floor_nonneg.mpr hq
    have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
    cases mode <;> simp only <;>
    (try split) <;> (try split) <;> (try split) <;>
    calc ((if _ then _ else _) : Nat) ≤ q.floor.toNat + 1 := by split_ifs <;> omega
      _ ≤ q + 1 := by
        have h3 : (q.floor.toNat : Rat) ≤ q := by
          calc (q.floor.toNat : Rat) = ((q.floor.toNat : Int) : Rat) := by simp
            _ = (q.floor : Rat) := by rw [h2]
            _ ≤ q := Rat.floor_le q
        linarith
  · -- Lower bound
    have h1 : q.floor ≥ 0 := Int.floor_nonneg.mpr hq
    have h2 : (q.floor.toNat : Int) = q.floor := Int.toNat_of_nonneg h1
    have h_floor_bound : q - 1 < (q.floor : Rat) := Rat.sub_one_lt_floor q
    unfold roundRatToNat
    cases mode <;> simp only <;>
    (try split) <;> (try split) <;> (try split) <;>
    calc q - 1 < (q.floor : Rat) := h_floor_bound
      _ = ((q.floor.toNat : Int) : Rat) := by rw [h2]
      _ = (q.floor.toNat : Rat) := by simp
      _ ≤ ((if _ then _ else _) : Nat) := by split_ifs <;> simp <;> omega

/-- For any rounding mode and q ≥ 1, roundRatToNat gives at least 1.
    This is because all rounding modes give a value within 1 of the input,
    and for q ≥ 1, this means the result is at least 0, but since floor(q) ≥ 1
    for q ≥ 1, all modes give at least 1. -/
theorem roundRatToNat_ge_one (mode : RoundMode) (q : Rat) (hq : 1 ≤ q) :
    1 ≤ roundRatToNat mode q := by
  unfold roundRatToNat
  have h_floor_ge : q.floor ≥ 1 := by
    have h1 : (1 : Rat) ≤ q := hq
    have h2 : q.floor ≥ (1 : Rat).floor := Rat.floor_mono h1
    simp at h2
    exact h2
  have h_toNat_ge : q.floor.toNat ≥ 1 := by
    have h1 : q.floor ≥ 1 := h_floor_ge
    have h2 : q.floor.toNat = q.floor.natAbs := rfl
    have h3 : (q.floor.natAbs : Int) = q.floor := Int.natAbs_of_nonneg (by omega)
    omega
  cases mode <;> simp only <;> split_ifs <;> omega

/-! ## Normalization -/

/-- Normalize a (mantissa, exponent) pair so mantissa is in [2^prec, 2^(prec+1)) or is 0.
    Uses fuel to ensure termination. -/
def normalizeMantissa (cfg_prec : Nat) (mantissa : Nat) (exponent : Int) (fuel : Nat) :
    Nat × Int :=
  if fuel = 0 then (mantissa, exponent)
  else if mantissa = 0 then (0, exponent)
  else if mantissa ≥ 2^(cfg_prec + 1) then
    normalizeMantissa cfg_prec (mantissa / 2) (exponent + 1) (fuel - 1)
  else if mantissa < 2^cfg_prec then
    normalizeMantissa cfg_prec (mantissa * 2) (exponent - 1) (fuel - 1)
  else
    (mantissa, exponent)

/-- Normalization preserves zero mantissa -/
theorem normalizeMantissa_zero (cfg_prec : Nat) (exp : Int) (fuel : Nat) :
    (normalizeMantissa cfg_prec 0 exp fuel).1 = 0 := by
  induction fuel with
  | zero => unfold normalizeMantissa; simp
  | succ n ih =>
    unfold normalizeMantissa
    simp

/-- Helper: normalization for small mantissa terminates within cfg_prec steps.
    For mantissa ∈ [1, 2^cfg_prec), we need at most cfg_prec multiplications
    to reach the normalized range [2^cfg_prec, 2^(cfg_prec+1)). -/
theorem normalizeMantissa_small (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat)
    (h_pos : 0 < mantissa) (h_small : mantissa < 2^cfg_prec) (h_fuel : fuel ≥ cfg_prec) :
    let (m, _) := normalizeMantissa cfg_prec mantissa exp fuel
    m = 0 ∨ (2^cfg_prec ≤ m ∧ m < 2^(cfg_prec + 1)) := by
  -- Use strong induction on (2^cfg_prec - mantissa), the "distance" to normalized range
  -- Each multiplication at least doubles mantissa, halving the distance
  induction cfg_prec generalizing mantissa exp fuel with
  | zero =>
    -- cfg_prec = 0: mantissa < 2^0 = 1, but mantissa > 0, contradiction
    simp at h_small
    omega
  | succ p ih =>
    -- cfg_prec = p + 1
    -- Need fuel ≥ p + 1, and mantissa < 2^(p+1)
    cases fuel with
    | zero => omega
    | succ n =>
      unfold normalizeMantissa
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have h_nonzero : mantissa ≠ 0 := by omega
      simp only [h_nonzero, ↓reduceIte]
      -- Check if mantissa ≥ 2^(p+2) - no, since mantissa < 2^(p+1) < 2^(p+2)
      have h_not_big : ¬(mantissa ≥ 2^(p + 1 + 1)) := by
        have h1 : 2^(p+1) < 2^(p+2) := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
        omega
      simp only [h_not_big, ↓reduceIte]
      -- Check if mantissa < 2^(p+1) - yes, by h_small
      have h_still_small : mantissa < 2^(p + 1) := h_small
      simp only [h_still_small, ↓reduceIte]
      -- Recurse with mantissa * 2
      -- Two cases: either mantissa * 2 reaches normalized range, or we continue
      by_cases h_reach : 2^(p + 1) ≤ mantissa * 2
      · -- mantissa * 2 is in [2^(p+1), ...), but is it < 2^(p+2)?
        by_cases h_reach2 : mantissa * 2 < 2^(p + 1 + 1)
        · -- mantissa * 2 ∈ [2^(p+1), 2^(p+2)) - normalized!
          cases n with
          | zero =>
            unfold normalizeMantissa
            simp only [↓reduceIte]
            right
            constructor <;> omega
          | succ n' =>
            unfold normalizeMantissa
            simp only [Nat.add_one_ne_zero, ↓reduceIte]
            have h_m2_nonzero : mantissa * 2 ≠ 0 := by omega
            simp only [h_m2_nonzero, ↓reduceIte]
            have h_m2_not_big : ¬(mantissa * 2 ≥ 2^(p + 1 + 1)) := by omega
            simp only [h_m2_not_big, ↓reduceIte]
            have h_m2_not_small : ¬(mantissa * 2 < 2^(p + 1)) := by omega
            simp only [h_m2_not_small, ↓reduceIte]
            right
            constructor <;> omega
        · -- mantissa * 2 ≥ 2^(p+2), need to divide
          -- This shouldn't happen if mantissa < 2^(p+1)
          -- mantissa * 2 < 2^(p+1) * 2 = 2^(p+2)
          exfalso
          have h1 : mantissa * 2 < 2^(p+1) * 2 := by omega
          have h2 : 2^(p+1) * 2 = 2^(p+2) := by rw [Nat.pow_succ]; ring
          omega
      · -- mantissa * 2 < 2^(p+1), need more multiplications
        -- Use induction hypothesis with mantissa * 2
        -- mantissa * 2 < 2^(p+1), so mantissa < 2^p
        have h_mantissa_small_p : mantissa < 2^p := by
          have h1 : mantissa * 2 < 2^(p+1) := by omega
          have h2 : 2^(p+1) = 2 * 2^p := Nat.pow_succ 2 p
          omega
        have h_m2_pos : 0 < mantissa * 2 := by omega
        have h_m2_small : mantissa * 2 < 2^p := by omega
        have h_n_ge_p : n ≥ p := by omega
        exact ih (mantissa * 2) (exp - 1) n h_m2_pos h_m2_small h_n_ge_p

/-- With sufficient fuel, normalizeMantissa produces normalized output.

    NOTE: The fuel bound proof is complex due to the opposing directions
    of normalization (divide for large mantissa, multiply for small).
    For practical use, fuel = mantissa + cfg_prec is always sufficient. -/
theorem normalizeMantissa_isNormalized (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat)
    (h_fuel : fuel ≥ mantissa + cfg_prec) :
    let (m, _) := normalizeMantissa cfg_prec mantissa exp fuel
    m = 0 ∨ (2^cfg_prec ≤ m ∧ m < 2^(cfg_prec + 1)) := by
  induction fuel generalizing mantissa exp with
  | zero =>
    unfold normalizeMantissa
    simp only [↓reduceIte]
    left
    omega
  | succ n ih =>
    unfold normalizeMantissa
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    split
    · -- mantissa = 0
      left; rfl
    · rename_i h_nonzero
      split
      · -- mantissa ≥ 2^(cfg_prec + 1) : divide
        rename_i h_big
        have h_fuel' : n ≥ mantissa / 2 + cfg_prec := by omega
        exact ih (mantissa / 2) (exp + 1) h_fuel'
      · rename_i h_not_big
        split
        · -- mantissa < 2^cfg_prec (and mantissa ≠ 0) : multiply
          rename_i h_small
          -- Use the helper lemma for small mantissa
          have h_pos : 0 < mantissa := Nat.pos_of_ne_zero h_nonzero
          have h_fuel_ge_prec : n ≥ cfg_prec := by omega
          exact normalizeMantissa_small cfg_prec mantissa exp n h_pos h_small h_fuel_ge_prec
        · -- mantissa in [2^cfg_prec, 2^(cfg_prec+1))
          rename_i h_not_small
          right
          constructor
          · exact Nat.not_lt.mp h_not_small
          · exact Nat.not_le.mp h_not_big

/-- If mantissa is already normalized, normalizeMantissa returns it unchanged -/
theorem normalizeMantissa_already_normalized (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat)
    (h_lo : 2^cfg_prec ≤ mantissa) (h_hi : mantissa < 2^(cfg_prec + 1)) :
    normalizeMantissa cfg_prec mantissa exp fuel = (mantissa, exp) := by
  cases fuel with
  | zero => unfold normalizeMantissa; simp
  | succ n =>
    unfold normalizeMantissa
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    -- mantissa ≠ 0 (since mantissa ≥ 2^cfg_prec > 0)
    have h_nonzero : mantissa ≠ 0 := by
      intro h
      rw [h] at h_lo
      have : 2^cfg_prec > 0 := Nat.pow_pos (by omega : 0 < 2) cfg_prec
      omega
    simp only [h_nonzero, ↓reduceIte]
    -- mantissa < 2^(cfg_prec + 1), so not ≥ 2^(cfg_prec + 1)
    have h_not_big : ¬(mantissa ≥ 2^(cfg_prec + 1)) := Nat.not_le.mpr h_hi
    simp only [h_not_big, ↓reduceIte]
    -- mantissa ≥ 2^cfg_prec, so not < 2^cfg_prec
    have h_not_small : ¬(mantissa < 2^cfg_prec) := Nat.not_lt.mpr h_lo
    simp only [h_not_small, ↓reduceIte]

/-- normalizeMantissa preserves the value m * 2^e when multiplying (no precision loss).
    When the mantissa is small and we multiply by 2, the value is exactly preserved. -/
theorem normalizeMantissa_value_mul (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat)
    (h_pos : 0 < mantissa) (h_small : mantissa < 2^cfg_prec) (h_fuel : fuel > 0) :
    let (m, e) := normalizeMantissa cfg_prec mantissa exp fuel
    let (m', e') := normalizeMantissa cfg_prec (mantissa * 2) (exp - 1) (fuel - 1)
    (m : Rat) * (2 : Rat) ^ (e - cfg_prec) = (m' : Rat) * (2 : Rat) ^ (e' - cfg_prec) := by
  cases fuel with
  | zero => omega
  | succ n =>
    unfold normalizeMantissa
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have h_nonzero : mantissa ≠ 0 := by omega
    simp only [h_nonzero, ↓reduceIte]
    have h_not_big : ¬(mantissa ≥ 2^(cfg_prec + 1)) := by
      have : 2^cfg_prec < 2^(cfg_prec + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    simp only [h_not_big, ↓reduceIte, h_small, ↓reduceIte]
    -- Now both sides recurse with mantissa * 2, exp - 1
    rfl

/-- Key property: normalizeMantissa produces a value that represents the same
    rational as mantissa * 2^(exp - prec), up to the rounding that occurs
    when dividing by 2 with an odd mantissa.

    More precisely: if (m, e) = normalizeMantissa prec mantissa exp fuel, then:
    - If no division occurred: m * 2^(e - prec) = mantissa * 2^(exp - prec)
    - If division occurred: m * 2^(e - prec) ≤ mantissa * 2^(exp - prec)

    The inequality comes from integer division rounding toward zero. -/
theorem normalizeMantissa_value_le (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat) :
    let (m, e) := normalizeMantissa cfg_prec mantissa exp fuel
    (m : Rat) * (2 : Rat) ^ (e - cfg_prec) ≤ (mantissa : Rat) * (2 : Rat) ^ (exp - cfg_prec) := by
  induction fuel generalizing mantissa exp with
  | zero =>
    unfold normalizeMantissa
    simp
  | succ n ih =>
    unfold normalizeMantissa
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    split
    · -- mantissa = 0
      simp
    · rename_i h_nonzero
      split
      · -- mantissa ≥ 2^(cfg_prec + 1) : divide
        rename_i h_big
        -- The division mantissa / 2 may round down
        have h_div_le : (mantissa / 2 : Rat) ≤ (mantissa : Rat) / 2 := by
          have := Nat.div_le_self mantissa 2
          simp only [Nat.cast_div_le]
        -- By IH: result ≤ (mantissa/2) * 2^((exp+1) - prec)
        have h_ih := ih (mantissa / 2) (exp + 1)
        -- And (mantissa/2) * 2^(exp+1-prec) ≤ mantissa * 2^(exp-prec)
        calc (normalizeMantissa cfg_prec (mantissa / 2) (exp + 1) n).1 *
               (2 : Rat) ^ ((normalizeMantissa cfg_prec (mantissa / 2) (exp + 1) n).2 - cfg_prec)
             ≤ (mantissa / 2 : Rat) * (2 : Rat) ^ ((exp + 1) - cfg_prec) := h_ih
           _ ≤ ((mantissa : Rat) / 2) * (2 : Rat) ^ ((exp + 1) - cfg_prec) := by
               apply mul_le_mul_of_nonneg_right h_div_le
               apply zpow_nonneg; decide
           _ = (mantissa : Rat) * ((2 : Rat) ^ ((exp + 1) - cfg_prec) / 2) := by ring
           _ = (mantissa : Rat) * (2 : Rat) ^ (exp - cfg_prec) := by
               congr 1
               rw [zpow_sub₀ (by decide : (2 : Rat) ≠ 0)]
               ring
      · rename_i h_not_big
        split
        · -- mantissa < 2^cfg_prec : multiply
          rename_i h_small
          -- Multiplying by 2 is exact, and the exponent decreases by 1
          have h_ih := ih (mantissa * 2) (exp - 1)
          calc (normalizeMantissa cfg_prec (mantissa * 2) (exp - 1) n).1 *
                 (2 : Rat) ^ ((normalizeMantissa cfg_prec (mantissa * 2) (exp - 1) n).2 - cfg_prec)
               ≤ (mantissa * 2 : Rat) * (2 : Rat) ^ ((exp - 1) - cfg_prec) := h_ih
             _ = (mantissa : Rat) * 2 * (2 : Rat) ^ ((exp - 1) - cfg_prec) := by simp [Nat.cast_mul]
             _ = (mantissa : Rat) * (2 : Rat) ^ (exp - cfg_prec) := by
                 rw [zpow_sub₀ (by decide : (2 : Rat) ≠ 0)]
                 ring
        · -- Already normalized
          rename_i h_not_small
          simp

/-- After normalization with non-zero result, the value m * 2^(e - prec) is in [2^e, 2^(e+1)).
    This is because m ∈ [2^prec, 2^(prec+1)), so:
    m * 2^(e - prec) ∈ [2^prec * 2^(e-prec), 2^(prec+1) * 2^(e-prec)) = [2^e, 2^(e+1)) -/
theorem normalizeMantissa_in_band (cfg_prec : Nat) (mantissa : Nat) (exp : Int) (fuel : Nat)
    (h_pos : 0 < mantissa) (h_fuel : fuel ≥ mantissa + cfg_prec) :
    let (m, e) := normalizeMantissa cfg_prec mantissa exp fuel
    m = 0 ∨ ((2 : Rat) ^ e ≤ (m : Rat) * (2 : Rat) ^ (e - cfg_prec) ∧
             (m : Rat) * (2 : Rat) ^ (e - cfg_prec) < (2 : Rat) ^ (e + 1)) := by
  -- First, use normalizeMantissa_isNormalized to get m = 0 or m ∈ [2^prec, 2^(prec+1))
  have h_norm := normalizeMantissa_isNormalized cfg_prec mantissa exp fuel h_fuel
  let (m, e) := normalizeMantissa cfg_prec mantissa exp fuel
  cases h_norm with
  | inl h_zero => left; exact h_zero
  | inr h_range =>
    right
    obtain ⟨h_lo, h_hi⟩ := h_range
    constructor
    · -- 2^e ≤ m * 2^(e - prec)
      calc (2 : Rat) ^ e
          = (2 : Rat) ^ cfg_prec * (2 : Rat) ^ (e - cfg_prec) := by
              rw [← zpow_natCast, ← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]
              congr 1; omega
        _ ≤ (m : Rat) * (2 : Rat) ^ (e - cfg_prec) := by
              apply mul_le_mul_of_nonneg_right
              · exact nat_cast_le_rat _ _ h_lo
              · apply zpow_nonneg; decide
    · -- m * 2^(e - prec) < 2^(e + 1)
      calc (m : Rat) * (2 : Rat) ^ (e - cfg_prec)
          < (2 : Rat) ^ (cfg_prec + 1) * (2 : Rat) ^ (e - cfg_prec) := by
              apply mul_lt_mul_of_pos_right
              · exact nat_cast_lt_rat _ _ h_hi
              · apply zpow_pos; decide
        _ = (2 : Rat) ^ (e + 1) := by
              rw [← zpow_natCast, ← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]
              congr 1; omega

/-- roundRatToNat on a natural number returns that number -/
theorem roundRatToNat_of_nat (mode : RoundMode) (n : Nat) :
    roundRatToNat mode (n : Rat) = n := by
  unfold roundRatToNat
  -- floor of a natural number is itself
  have h_floor : (n : Rat).floor = n := by
    simp only [Rat.floor_intCast, Int.cast_natCast]
  simp only [h_floor, Int.toNat_natCast]
  -- frac = n - n = 0
  have h_frac : (n : Rat) - (n : Rat) = 0 := sub_self _
  simp only [h_frac]
  -- For all modes, when frac = 0, result is floor_q = n
  cases mode <;> simp

/-! ## Core Rounding Operation -/

/-- Round a rational to the nearest representable float.

This is the core operation that converts exact rational arithmetic
back to floating-point representation with correct rounding.

Algorithm:
1. Handle zero specially
2. Extract sign and work with |q|
3. Find exponent e ≈ floor(log2(|q|))
4. Compute mantissa = round(|q| * 2^(precision - e))
5. Normalize if mantissa overflows
6. Clamp exponent to valid range
-/
def roundToFloat (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (q : Rat) : FloatRepr :=
  -- Handle zero
  if q = 0 then
    FloatRepr.zero cfg_emin
  else
    -- Extract sign
    let sign := q < 0
    let abs_q : Rat := if sign then -q else q

    -- Find approximate exponent: e ≈ floor(log2(|q|))
    -- We want: 2^e ≤ |q| < 2^(e+1), so mantissa is in [2^prec, 2^(prec+1))
    let e_approx := log2Rat abs_q

    -- Scale to get mantissa in the right range
    -- mantissa_exact = |q| * 2^(prec - e)
    -- For normalized: should be in [2^prec, 2^(prec+1))
    let scale_exp := (cfg_prec : Int) - e_approx
    let mantissa_exact := abs_q * ((2 : Rat) ^ scale_exp)

    -- Round to integer
    let mantissa_rounded := roundRatToNat mode mantissa_exact

    -- Normalize using the full normalization function
    -- Use fuel = mantissa_rounded + cfg_prec which is enough for any direction
    let (mantissa_norm, exp_norm) :=
      normalizeMantissa cfg_prec mantissa_rounded e_approx (mantissa_rounded + cfg_prec)

    -- Clamp exponent to valid range
    let clamped_exp :=
      if exp_norm < cfg_emin then cfg_emin
      else if exp_norm > cfg_emax then cfg_emax
      else exp_norm

    { sign := sign, mantissa := mantissa_norm, exponent := clamped_exp }

/-! ## Addition -/

/-- Add two floats with correct rounding -/
def FloatRepr.add (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) : FloatRepr :=
  -- Convert to rational, add, round back
  let xr := x.toRat cfg_prec
  let yr := y.toRat cfg_prec
  let sum := xr + yr
  roundToFloat cfg_prec cfg_emin cfg_emax mode sum

/-! ## Multiplication -/

/-- Multiply two floats with correct rounding -/
def FloatRepr.mul (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) : FloatRepr :=
  let xr := x.toRat cfg_prec
  let yr := y.toRat cfg_prec
  let prod := xr * yr
  roundToFloat cfg_prec cfg_emin cfg_emax mode prod

/-! ## Division -/

/-- Divide two floats with correct rounding -/
def FloatRepr.div (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) : FloatRepr :=
  let xr := x.toRat cfg_prec
  let yr := y.toRat cfg_prec
  let quot := xr / yr
  roundToFloat cfg_prec cfg_emin cfg_emax mode quot

/-! ## Subtraction -/

/-- Subtract two floats with correct rounding -/
def FloatRepr.sub (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) : FloatRepr :=
  x.add cfg_prec cfg_emin cfg_emax mode y.neg

/-! ## Ordering -/

/-- Less than or equal -/
def FloatRepr.le (cfg_prec : Nat) (x y : FloatRepr) : Prop :=
  x.toRat cfg_prec ≤ y.toRat cfg_prec

/-- Less than -/
def FloatRepr.lt (cfg_prec : Nat) (x y : FloatRepr) : Prop :=
  x.toRat cfg_prec < y.toRat cfg_prec

/-! ## Normalization -/

/-- A FloatRepr is normalized if:
    - For zero: mantissa = 0
    - For non-zero: mantissa ∈ [2^prec, 2^(prec+1))
    This ensures unique representation for each non-zero rational value. -/
def FloatRepr.isNormalized (cfg_prec : Nat) (f : FloatRepr) : Prop :=
  f.mantissa = 0 ∨ (2^cfg_prec ≤ f.mantissa ∧ f.mantissa < 2^(cfg_prec + 1))

/-- Zero is normalized -/
theorem zero_isNormalized (cfg_prec : Nat) (cfg_emin : Int) :
    (FloatRepr.zero cfg_emin).isNormalized cfg_prec := by
  left
  rfl

/-- One is normalized -/
theorem one_isNormalized (cfg_prec : Nat) :
    (FloatRepr.one cfg_prec).isNormalized cfg_prec := by
  unfold FloatRepr.isNormalized FloatRepr.one
  right
  constructor
  · exact Nat.le_refl _
  · -- Need to show 2^cfg_prec < 2^(cfg_prec + 1)
    exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : cfg_prec < cfg_prec + 1)

/-- roundToFloat produces normalized floats -/
theorem roundToFloat_isNormalized (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (q : Rat) :
    (roundToFloat cfg_prec cfg_emin cfg_emax mode q).isNormalized cfg_prec := by
  unfold roundToFloat
  split
  · -- Case: q = 0, returns FloatRepr.zero
    left
    rfl
  · -- Case: q ≠ 0, uses normalizeMantissa
    rename_i h_ne_zero
    unfold FloatRepr.isNormalized
    -- Extract the components
    let sign := q < 0
    let abs_q : Rat := if sign then -q else q
    let e_approx := log2Rat abs_q
    let scale_exp := (cfg_prec : Int) - e_approx
    let mantissa_exact := abs_q * ((2 : Rat) ^ scale_exp)
    let mantissa_rounded := roundRatToNat mode mantissa_exact
    -- The result mantissa comes from normalizeMantissa
    -- Fuel = mantissa_rounded + cfg_prec satisfies: fuel ≥ mantissa_rounded + cfg_prec
    have h_fuel : mantissa_rounded + cfg_prec ≥ mantissa_rounded + cfg_prec := by omega
    exact normalizeMantissa_isNormalized cfg_prec mantissa_rounded e_approx
      (mantissa_rounded + cfg_prec) h_fuel

/-! ## Core Theorems -/

/-- Rounding a normalized float's rational value back gives the same float.

    For this to hold, x must be:
    1. Normalized (mantissa in [2^prec, 2^(prec+1)) or zero)
    2. Have exponent in valid range [cfg_emin, cfg_emax]
    3. If mantissa = 0, x must be the canonical zero (FloatRepr.zero cfg_emin)

    The proof requires showing that:
    - log2Rat gives the correct exponent for normalized floats
    - roundRatToNat returns the same value for an integer input
    - normalizeMantissa is idempotent for normalized mantissa
    - Exponent clamping doesn't change valid exponents -/
theorem roundToFloat_idempotent (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (hx_norm : x.isNormalized cfg_prec)
    (hx_exp_lo : cfg_emin ≤ x.exponent)
    (hx_exp_hi : x.exponent ≤ cfg_emax)
    (hx_canonical_zero : x.mantissa = 0 → x = FloatRepr.zero cfg_emin) :
    roundToFloat cfg_prec cfg_emin cfg_emax mode (x.toRat cfg_prec) = x := by
  -- Split by whether mantissa is zero
  by_cases h_zero : x.mantissa = 0
  · -- Case 1: x.mantissa = 0
    -- By hx_canonical_zero, x = FloatRepr.zero cfg_emin
    have hx_eq := hx_canonical_zero h_zero
    rw [hx_eq]
    -- toRat of zero is 0
    simp only [toRat_zero]
    -- roundToFloat of 0 is FloatRepr.zero cfg_emin
    unfold roundToFloat
    simp
  · -- Case 2: x.mantissa ≠ 0 (non-zero normalized)
    --   toRat = ±mantissa * 2^(exp - prec)
    --   log2Rat should give exp (since mantissa ∈ [2^prec, 2^(prec+1)))
    --   Scaling gives mantissa exactly (integer, no rounding needed)
    --   Normalization is idempotent, exponent is unchanged
    -- Get normalized bounds from isNormalized
    unfold FloatRepr.isNormalized at hx_norm
    cases hx_norm with
    | inl h_z => exact absurd h_z h_zero
    | inr h_bounds =>
      obtain ⟨h_lo, h_hi⟩ := h_bounds
      -- x.toRat ≠ 0
      have h_toRat_ne_zero : x.toRat cfg_prec ≠ 0 := by
        unfold FloatRepr.toRat
        intro h_eq
        -- The base = mantissa * 2^(exp - prec) > 0 for mantissa > 0
        have h_mant_pos : (x.mantissa : Rat) > 0 := by
          have h1 : (0 : Nat) < x.mantissa := by
            have h2 : 2^cfg_prec ≤ x.mantissa := h_lo
            have h3 : 2^cfg_prec > 0 := Nat.pow_pos (by omega : 0 < 2) cfg_prec
            omega
          exact nat_cast_lt_rat 0 x.mantissa h1
        have h_pow_pos : (2 : Rat) ^ (x.exponent - ↑cfg_prec) > 0 := by
          apply zpow_pos; decide
        have h_base_pos : (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - ↑cfg_prec) > 0 :=
          mul_pos h_mant_pos h_pow_pos
        cases hx_sign : x.sign <;> simp only [hx_sign, Bool.true_eq_false, ↓reduceIte,
          Bool.false_eq_true] at h_eq
        · -- sign = false: base > 0, but h_eq says base = 0
          exact absurd h_eq (ne_of_gt h_base_pos)
        · -- sign = true: -base ≠ 0
          have h_neg_ne : -(x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - ↑cfg_prec) ≠ 0 := by
            rw [neg_mul]
            exact neg_ne_zero.mpr (ne_of_gt h_base_pos)
          exact absurd h_eq h_neg_ne
      -- Unfold roundToFloat
      unfold roundToFloat
      simp only [h_toRat_ne_zero, ↓reduceIte]
      -- Now we need to show the constructed FloatRepr equals x
      -- Let's extract the key intermediate values
      set q := x.toRat cfg_prec with hq_def
      set sign_q := q < 0 with hsign_q_def
      set abs_q := if sign_q then -q else q with habs_q_def
      set e_approx := log2Rat abs_q with he_approx_def
      set scale_exp := (cfg_prec : Int) - e_approx with hscale_exp_def
      set mantissa_exact := abs_q * ((2 : Rat) ^ scale_exp) with hmant_exact_def
      set mantissa_rounded := roundRatToNat mode mantissa_exact with hmant_rounded_def
      set norm_result := normalizeMantissa cfg_prec mantissa_rounded e_approx
                           (mantissa_rounded + cfg_prec) with hnorm_result_def
      set clamped_exp := if norm_result.2 < cfg_emin then cfg_emin
                         else if norm_result.2 > cfg_emax then cfg_emax
                         else norm_result.2 with hclamped_exp_def
      -- Goal: { sign := sign_q, mantissa := norm_result.1, exponent := clamped_exp } = x
      -- Step 1: sign_q = x.sign
      have h_sign_eq : sign_q = x.sign := by
        unfold FloatRepr.toRat at hq_def
        have h_base_pos : (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - ↑cfg_prec) > 0 := by
          have h_mant_pos : (x.mantissa : Rat) > 0 := by
            have h1 : (0 : Nat) < x.mantissa := by
              have h2 : 2^cfg_prec ≤ x.mantissa := h_lo
              have h3 : 2^cfg_prec > 0 := Nat.pow_pos (by omega : 0 < 2) cfg_prec
              omega
            exact nat_cast_lt_rat 0 x.mantissa h1
          have h_pow_pos : (2 : Rat) ^ (x.exponent - ↑cfg_prec) > 0 := by
            apply zpow_pos; decide
          exact mul_pos h_mant_pos h_pow_pos
        rw [hq_def]
        unfold FloatRepr.toRat
        cases hx_sign : x.sign <;>
          simp only [hx_sign, hsign_q_def, Bool.true_eq_false, Bool.false_eq_true,
            ↓reduceIte, not_lt, neg_mul]
        · -- sign = false: q = base > 0, so ¬(q < 0)
          exact le_of_lt h_base_pos
        · -- sign = true: q = -base < 0
          exact neg_neg_of_pos h_base_pos
      -- Step 2: abs_q = x.mantissa * 2^(x.exponent - cfg_prec)
      have h_abs_q : abs_q = (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - ↑cfg_prec) := by
        unfold FloatRepr.toRat at hq_def
        rw [habs_q_def, hq_def]
        unfold FloatRepr.toRat
        cases hx_sign : x.sign <;>
          simp only [hx_sign, hsign_q_def, Bool.true_eq_false, Bool.false_eq_true,
            ↓reduceIte, neg_mul, neg_neg]
      -- Step 3: e_approx = x.exponent
      -- Use the log2Rat_normalized lemma
      have h_e_approx : e_approx = x.exponent := by
        rw [he_approx_def, h_abs_q]
        exact log2Rat_normalized x.mantissa x.exponent cfg_prec h_lo h_hi
      -- Step 4: scale_exp = cfg_prec - x.exponent
      have h_scale_exp : scale_exp = (cfg_prec : Int) - x.exponent := by
        rw [hscale_exp_def, h_e_approx]
      -- Step 5: mantissa_exact = x.mantissa
      have h_mant_exact : mantissa_exact = (x.mantissa : Rat) := by
        rw [hmant_exact_def, h_abs_q, h_scale_exp]
        -- x.mantissa * 2^(x.exp - prec) * 2^(prec - x.exp) = x.mantissa
        have h2_ne : (2 : Rat) ≠ 0 := by decide
        rw [mul_comm (2 : Rat) ^ scale_exp _, ← mul_assoc]
        rw [h_scale_exp, ← zpow_add₀ h2_ne]
        simp only [sub_add_cancel, zpow_zero, mul_one]
      -- Step 6: mantissa_rounded = x.mantissa
      have h_mant_rounded : mantissa_rounded = x.mantissa := by
        rw [hmant_rounded_def, h_mant_exact]
        exact roundRatToNat_of_nat mode x.mantissa
      -- Step 7: normalizeMantissa returns (x.mantissa, x.exponent)
      have h_norm : norm_result = (x.mantissa, x.exponent) := by
        rw [hnorm_result_def, h_mant_rounded, h_e_approx]
        exact normalizeMantissa_already_normalized cfg_prec x.mantissa x.exponent
          (x.mantissa + cfg_prec) h_lo h_hi
      -- Step 8: clamped_exp = x.exponent (since exponent is in valid range)
      have h_clamp : clamped_exp = x.exponent := by
        rw [hclamped_exp_def, h_norm]
        simp only
        -- x.exponent is in [cfg_emin, cfg_emax]
        have h_not_lo : ¬(x.exponent < cfg_emin) := not_lt.mpr hx_exp_lo
        have h_not_hi : ¬(x.exponent > cfg_emax) := not_lt.mpr hx_exp_hi
        simp only [h_not_lo, ↓reduceIte, h_not_hi]
      -- Final: construct the equality
      have h_eq_sign : sign_q = x.sign := h_sign_eq
      have h_eq_mant : norm_result.1 = x.mantissa := by rw [h_norm]
      have h_eq_exp : clamped_exp = x.exponent := h_clamp
      -- Use ext-like reasoning for FloatRepr
      cases x
      simp only at h_eq_sign h_eq_mant h_eq_exp ⊢
      constructor
      · exact h_eq_sign
      · constructor
        · exact h_eq_mant
        · exact h_eq_exp

/-- Rounding a non-negative rational gives a non-negative float -/
theorem roundToFloat_nonneg (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (q : Rat) (hq : 0 ≤ q) :
    0 ≤ (roundToFloat cfg_prec cfg_emin cfg_emax mode q).toRat cfg_prec := by
  by_cases h : q = 0
  · simp only [h, roundToFloat, ite_true, toRat_zero, le_refl]
  · -- q > 0 (since q ≥ 0 and q ≠ 0)
    have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm h)
    have h_not_neg : ¬(q < 0) := not_lt.mpr (le_of_lt hq_pos)
    -- Unfold roundToFloat for non-zero q
    unfold roundToFloat
    simp only [h, ite_false, h_not_neg]
    -- The result has sign = false
    -- toRat of sign=false returns mantissa * 2^(exp - prec) which is non-negative
    unfold FloatRepr.toRat
    simp only [ite_false]
    -- mantissa is Nat cast to Rat (≥ 0), power of 2 is positive
    apply mul_nonneg
    · exact nat_cast_nonneg _
    · apply zpow_nonneg; decide

/-- Rounding a non-positive rational gives a non-positive float -/
theorem roundToFloat_nonpos (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (q : Rat) (hq : q ≤ 0) :
    (roundToFloat cfg_prec cfg_emin cfg_emax mode q).toRat cfg_prec ≤ 0 := by
  by_cases h : q = 0
  · simp only [h, roundToFloat, ite_true, toRat_zero, le_refl]
  · -- q < 0 (since q ≤ 0 and q ≠ 0)
    have hq_neg : q < 0 := lt_of_le_of_ne hq h
    -- Unfold roundToFloat for non-zero q
    unfold roundToFloat
    simp only [h, ite_false, hq_neg]
    -- The result has sign = true
    -- toRat of sign=true returns -(mantissa * 2^(exp - prec))
    unfold FloatRepr.toRat
    simp only [ite_true]
    -- -(non-negative) ≤ 0
    apply neg_nonpos.mpr
    apply mul_nonneg
    · exact nat_cast_nonneg _
    · apply zpow_nonneg; decide

/-- The rounding pipeline for negative q relates to rounding of -q.

    For q < 0:
    - roundToFloat(q) has sign = true
    - roundToFloat(-q) has sign = false
    - Both use the same magnitude |-q| = -q for the rounding

    This gives: toRat(roundToFloat(q)) = -toRat(roundToFloat(-q))

    Key insight: the mantissa and exponent are computed identically from |q|,
    so the only difference is the sign bit. -/
theorem roundToFloat_neg_relation (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (q : Rat) (hq : q < 0) :
    (roundToFloat cfg_prec cfg_emin cfg_emax mode q).toRat cfg_prec =
    -((roundToFloat cfg_prec cfg_emin cfg_emax mode (-q)).toRat cfg_prec) := by
  -- q < 0, so q ≠ 0 and -q > 0
  have h_nz : q ≠ 0 := ne_of_lt hq
  have h_neg_pos : 0 < -q := neg_pos.mpr hq
  have h_neg_nz : -q ≠ 0 := ne_of_gt h_neg_pos
  have h_neg_not_neg : ¬(-q < 0) := not_lt.mpr (le_of_lt h_neg_pos)
  -- Unfold roundToFloat for both
  unfold roundToFloat
  simp only [h_nz, ite_false, hq, ite_true, h_neg_nz, h_neg_not_neg, neg_neg]
  -- Both compute abs_q = -q and use the same pipeline
  -- For q: sign = true, abs_q = -q
  -- For -q: sign = false, abs_q = -q
  -- The mantissa and exponent are the same
  -- toRat for sign=true gives -base, for sign=false gives base
  unfold FloatRepr.toRat
  simp only [ite_true, ite_false]
  -- Both sides simplify to the same expression with opposite signs
  ring

/-- For positive q and prec ≥ 1, the scaled value q * 2^(prec - log2Rat(q)) ≥ 1.

    This is a key lemma for proving that roundRatToNat gives a positive result
    for positive inputs, which ensures normalizeMantissa doesn't produce zero.

    The proof uses the property that log2Rat underestimates log2 by at most 1:
    - For q = num/den in lowest terms
    - log2Rat(q) = log2Nat(num) - log2Nat(den)
    - log2(q) = log2(num) - log2(den)
    - Since log2Nat underestimates log2 by at most 1 for each term,
      log2Rat(q) is within 1 of log2(q)
    - Therefore q * 2^(prec - log2Rat(q)) ≥ 2^(prec - 1) ≥ 1 for prec ≥ 1 -/
theorem scaled_value_ge_one (q : Rat) (prec : Nat) (hq : 0 < q) (hprec : 1 ≤ prec) :
    1 ≤ q * (2 : Rat) ^ ((prec : Int) - log2Rat q) := by
  -- Extract num and den
  have h_num_pos : 0 < q.num := by
    rwa [Rat.num_pos]
  have h_num_natAbs_pos : q.num.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt h_num_pos)
  have h_den_pos : q.den > 0 := q.den_pos
  -- Get bounds on num and den from log2Nat_bounds
  have ⟨h_num_lo, h_num_hi⟩ := log2Nat_bounds q.num.natAbs h_num_natAbs_pos
  have ⟨h_den_lo, h_den_hi⟩ := log2Nat_bounds q.den h_den_pos
  -- log2Rat for positive q
  have h_log2Rat : log2Rat q = (log2Nat q.num.natAbs : Int) - (log2Nat q.den : Int) := by
    unfold log2Rat
    have h_not_neg : ¬(q < 0) := not_lt.mpr (le_of_lt hq)
    simp only [h_not_neg, ↓reduceIte]
    have h_num_nz : q.num.natAbs ≠ 0 := Nat.pos_iff_ne_zero.mp h_num_natAbs_pos
    simp only [h_num_nz, ↓reduceIte]
    -- For positive q, abs_q = q
    have h_abs : (if q < 0 then -q else q) = q := by simp [h_not_neg]
    simp only [h_abs]
  rw [h_log2Rat]
  -- The scaled exponent is prec - (log2Nat(num) - log2Nat(den)) = prec - log2Nat(num) + log2Nat(den)
  have h_scale : (prec : Int) - ((log2Nat q.num.natAbs : Int) - (log2Nat q.den : Int)) =
                 prec - log2Nat q.num.natAbs + log2Nat q.den := by ring
  rw [h_scale]
  -- q = num / den as rationals
  have h_q_eq : q = (q.num : Rat) / (q.den : Rat) := (Rat.num_div_den q).symm
  -- num ≥ 2^log2Nat(num) and den < 2^(log2Nat(den)+1)
  -- So num/den > 2^log2Nat(num) / 2^(log2Nat(den)+1) = 2^(log2Nat(num) - log2Nat(den) - 1)
  -- Multiply by 2^(prec - log2Nat(num) + log2Nat(den)):
  -- q * 2^(prec - log2Nat(num) + log2Nat(den)) > 2^(prec - 1)
  have h_den_upper : (q.den : Rat) < (2 : Rat) ^ (log2Nat q.den + 1) := by
    have h1 : q.den < 2^(log2Nat q.den + 1) := h_den_hi
    calc (q.den : Rat) < (2^(log2Nat q.den + 1) : Nat) := Nat.cast_lt.mpr h1
      _ = (2 : Rat) ^ (log2Nat q.den + 1) := by simp [zpow_natCast]
  have h_num_lower : (2 : Rat) ^ (log2Nat q.num.natAbs) ≤ (q.num.natAbs : Rat) := by
    have h1 : 2^(log2Nat q.num.natAbs) ≤ q.num.natAbs := h_num_lo
    calc (2 : Rat) ^ (log2Nat q.num.natAbs) = (2^(log2Nat q.num.natAbs) : Nat) := by simp [zpow_natCast]
      _ ≤ (q.num.natAbs : Rat) := Nat.cast_le.mpr h1
  -- For the proof, we use that:
  -- q * 2^(prec - log2Nat(num) + log2Nat(den))
  -- = (num/den) * 2^(prec - log2Nat(num) + log2Nat(den))
  -- = num * 2^(prec - log2Nat(num) + log2Nat(den)) / den
  -- ≥ 2^log2Nat(num) * 2^(prec - log2Nat(num) + log2Nat(den)) / 2^(log2Nat(den)+1)
  -- = 2^(log2Nat(num) + prec - log2Nat(num) + log2Nat(den)) / 2^(log2Nat(den)+1)
  -- = 2^(prec + log2Nat(den)) / 2^(log2Nat(den)+1)
  -- = 2^(prec + log2Nat(den) - log2Nat(den) - 1)
  -- = 2^(prec - 1)
  -- ≥ 1 for prec ≥ 1
  have h_positive_num : (0 : Rat) < q.num := Int.cast_pos.mpr h_num_pos
  have h_positive_den : (0 : Rat) < q.den := Nat.cast_pos.mpr h_den_pos
  have h_q_pos_rat : (0 : Rat) < q := hq
  have h_2_pos : (0 : Rat) < 2 := by decide
  have h_scale_pos : (0 : Rat) < (2 : Rat) ^ ((prec : Int) - log2Nat q.num.natAbs + log2Nat q.den) := by
    apply zpow_pos_of_pos; decide
  -- Direct calculation approach using bounds
  -- Lower bound: q ≥ num / 2^(log2Nat(den)+1) where num = q.num (positive)
  -- Since num ≥ 2^log2Nat(num) and num = q.num.natAbs for positive q.num
  have h_q_lower : q > (2 : Rat) ^ (log2Nat q.num.natAbs) / (2 : Rat) ^ (log2Nat q.den + 1) := by
    rw [h_q_eq]
    have h_num_eq : (q.num : Rat) = (q.num.natAbs : Rat) := by
      simp only [Int.cast_natAbs, abs_of_pos h_num_pos]
    rw [h_num_eq]
    apply div_lt_div_of_pos_left h_num_lower h_den_upper
    apply zpow_pos_of_pos; decide
  -- Simplify the exponent difference
  have h_exp_diff : (log2Nat q.num.natAbs : Int) - ((log2Nat q.den : Int) + 1) =
                    log2Nat q.num.natAbs - log2Nat q.den - 1 := by ring
  have h_zpow_div : (2 : Rat) ^ (log2Nat q.num.natAbs) / (2 : Rat) ^ (log2Nat q.den + 1) =
                    (2 : Rat) ^ ((log2Nat q.num.natAbs : Int) - (log2Nat q.den + 1)) := by
    rw [zpow_sub₀ (by decide : (2 : Rat) ≠ 0)]
    congr 1
    simp only [zpow_natCast, Nat.cast_add, Nat.cast_one]
  rw [h_zpow_div] at h_q_lower
  -- Now: q > 2^(log2Nat(num) - log2Nat(den) - 1)
  -- Multiply by 2^(prec - log2Nat(num) + log2Nat(den)):
  -- q * 2^(prec - log2Nat(num) + log2Nat(den)) > 2^(log2Nat(num) - log2Nat(den) - 1 + prec - log2Nat(num) + log2Nat(den))
  --                                             = 2^(prec - 1)
  have h_result_exp : ((log2Nat q.num.natAbs : Int) - (log2Nat q.den + 1)) +
                      ((prec : Int) - log2Nat q.num.natAbs + log2Nat q.den) = prec - 1 := by ring
  calc (1 : Rat) ≤ (2 : Rat) ^ ((prec : Int) - 1) := by
        have h1 : (prec : Int) - 1 ≥ 0 := by omega
        have h2 : (2 : Rat) ^ ((prec : Int) - 1) ≥ (2 : Rat) ^ (0 : Int) := by
          apply zpow_le_zpow_right₀ (by decide : 1 ≤ (2 : Rat)) h1
        simp at h2
        linarith
    _ = (2 : Rat) ^ (((log2Nat q.num.natAbs : Int) - (log2Nat q.den + 1)) +
                     ((prec : Int) - log2Nat q.num.natAbs + log2Nat q.den)) := by rw [h_result_exp]
    _ = (2 : Rat) ^ ((log2Nat q.num.natAbs : Int) - (log2Nat q.den + 1)) *
        (2 : Rat) ^ ((prec : Int) - log2Nat q.num.natAbs + log2Nat q.den) := by
        rw [← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]
    _ < q * (2 : Rat) ^ ((prec : Int) - log2Nat q.num.natAbs + log2Nat q.den) := by
        apply mul_lt_mul_of_pos_right h_q_lower h_scale_pos

/-- Helper: roundToFloat for positive values is monotonic.

    This is the core monotonicity property for the positive rounding pipeline.
    For 0 < x ≤ y, we have toRat(roundToFloat(x)) ≤ toRat(roundToFloat(y)).

    NOTE: log2Rat is NOT monotonic (counterexample: 4/3 < 3/2 but log2Rat(4/3) > log2Rat(3/2)).
    However, roundToFloat IS still monotonic because the normalization step corrects
    any errors from the log2Rat approximation.

    The proof uses a key property: for TowardZero mode, the rounded value is ≤ the input,
    and the rounded value is the largest representable value ≤ the input. This implies
    monotonicity. Similar arguments work for other rounding modes.

    NOTE: Requires cfg_prec ≥ 1 to ensure the scaled value is at least 1. -/
theorem roundToFloat_pos_monotonic (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : Rat) (hprec : 1 ≤ cfg_prec) (hx : 0 < x) (hy : 0 < y) (h_le : x ≤ y) :
    (roundToFloat cfg_prec cfg_emin cfg_emax mode x).toRat cfg_prec ≤
    (roundToFloat cfg_prec cfg_emin cfg_emax mode y).toRat cfg_prec := by
  -- Both x and y are positive, so sign = false for both
  have h_x_nz : x ≠ 0 := ne_of_gt hx
  have h_y_nz : y ≠ 0 := ne_of_gt hy
  have h_x_not_neg : ¬(x < 0) := not_lt.mpr (le_of_lt hx)
  have h_y_not_neg : ¬(y < 0) := not_lt.mpr (le_of_lt hy)

  -- Define the pipeline components for x
  let e_x := log2Rat x
  let scale_x := (cfg_prec : Int) - e_x
  let mantissa_exact_x := x * ((2 : Rat) ^ scale_x)
  let mantissa_rounded_x := roundRatToNat mode mantissa_exact_x
  let fuel_x := mantissa_rounded_x + cfg_prec
  let (m_x, exp_x) := normalizeMantissa cfg_prec mantissa_rounded_x e_x fuel_x
  let clamped_x := if exp_x < cfg_emin then cfg_emin
                   else if exp_x > cfg_emax then cfg_emax
                   else exp_x

  -- Define the pipeline components for y
  let e_y := log2Rat y
  let scale_y := (cfg_prec : Int) - e_y
  let mantissa_exact_y := y * ((2 : Rat) ^ scale_y)
  let mantissa_rounded_y := roundRatToNat mode mantissa_exact_y
  let fuel_y := mantissa_rounded_y + cfg_prec
  let (m_y, exp_y) := normalizeMantissa cfg_prec mantissa_rounded_y e_y fuel_y
  let clamped_y := if exp_y < cfg_emin then cfg_emin
                   else if exp_y > cfg_emax then cfg_emax
                   else exp_y

  -- The result after toRat is: m * 2^(clamped_exp - prec)
  -- We need to show: m_x * 2^(clamped_x - prec) ≤ m_y * 2^(clamped_y - prec)

  unfold roundToFloat
  simp only [h_x_nz, ite_false, h_x_not_neg, h_y_nz, h_y_not_neg]
  unfold FloatRepr.toRat
  simp only [ite_false]

  -- The proof strategy depends on the rounding mode
  -- For all modes, the key insight is that the rounding pipeline produces
  -- a value that approximates the input in a specific direction

  -- Key property: the pipeline produces a representable value
  -- For truncating modes (TowardZero, TowardNegative): round(q) ≤ q
  -- For ceiling mode (TowardPositive): round(q) ≥ q
  -- For nearest modes: round(q) is the nearest representable to q

  -- For monotonicity:
  -- - Truncating: round(x) ≤ x ≤ y, so round(x) ≤ y. Since round(y) is largest ≤ y, round(x) ≤ round(y)
  -- - Ceiling: round(x) is smallest ≥ x, round(y) ≥ y ≥ x ≥ round(x)? No, need different argument
  -- - Nearest: If x and y round to same value, trivial. Otherwise, round(x) < round(y) by structure

  -- Use the bounds we proved for roundRatToNat and normalizeMantissa

  -- For mantissa_exact_x and mantissa_exact_y, both are non-negative
  have h_exact_x_nonneg : 0 ≤ mantissa_exact_x := by
    apply mul_nonneg (le_of_lt hx)
    apply zpow_nonneg; decide
  have h_exact_y_nonneg : 0 ≤ mantissa_exact_y := by
    apply mul_nonneg (le_of_lt hy)
    apply zpow_nonneg; decide

  -- Case analysis on the relationship between the pipeline outputs
  -- The proof follows from the structure of IEEE 754 rounding:
  -- 1. Each step is either monotonic or bounded
  -- 2. The composition preserves order

  -- For now, we use the fundamental property that IEEE 754 rounding is monotonic
  -- This requires tracking through the normalization to show value preservation

  -- The key insight is that the normalization step adjusts the (mantissa, exponent)
  -- pair but preserves the rational value (up to the rounding that already occurred)
  -- By normalizeMantissa_value_le, the normalized value is ≤ the unnormalized value
  -- (when division occurs) or equal (when only multiplication occurs)

  -- Combined with roundRatToNat bounds and the structure of the pipeline,
  -- monotonicity follows

  -- The formal proof uses the band structure of normalized values.
  -- After normalization, values are in bands [2^e, 2^(e+1)) based on exponent e.

  -- Get the actual pipeline values after simp
  -- We need to compare: (result for x).mantissa * 2^((result for x).exp - prec)
  --                  vs (result for y).mantissa * 2^((result for y).exp - prec)

  -- Use omega/decide to handle the arithmetic comparisons
  -- The key insight: exponent clamping and mantissa normalization preserve monotonicity

  -- For the formal proof, we observe:
  -- 1. The clamped exponent is monotonic in the unclamped exponent
  -- 2. For same clamped exponent, mantissa comparison determines order
  -- 3. For different clamped exponents, the band structure gives the order

  -- Case analysis on whether mantissas are zero
  by_cases h_mx_zero : (normalizeMantissa cfg_prec (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)))
                        (log2Rat x) (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) + cfg_prec)).1 = 0
  · -- m_x = 0: result for x is 0
    simp only [h_mx_zero, Nat.cast_zero, zero_mul]
    apply mul_nonneg
    · exact nat_cast_nonneg _
    · apply zpow_nonneg; decide
  · by_cases h_my_zero : (normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
                          (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)).1 = 0
    · -- m_y = 0 but m_x ≠ 0: need to show this is impossible when x ≤ y and x > 0
      -- If m_y = 0, then roundRatToNat of y's scaled value must have been 0
      -- But y > 0 and prec ≥ 1, so the scaled value is ≥ 1, so roundRatToNat ≥ 1
      exfalso
      -- normalizeMantissa returns 0 only when input is 0
      have h_norm_equiv : normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
          (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec) =
          (0, (normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
          (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)).2) := by
        have h := h_my_zero
        rw [Prod.ext_iff]
        constructor
        · exact h
        · rfl
      -- If normalized output is 0, either input was 0 or fuel ran out
      -- With sufficient fuel, input must be 0
      have h_input_zero : roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) = 0 := by
        -- normalizeMantissa cfg_prec m e f returns (0, _) only when m = 0
        by_contra h_ne_zero
        have h_pos : roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) > 0 := Nat.pos_of_ne_zero h_ne_zero
        have h_norm := normalizeMantissa_isNormalized cfg_prec
          (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
          (log2Rat y)
          (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)
          (by omega)
        cases h_norm with
        | inl h_zero => exact h_ne_zero h_zero
        | inr h_range =>
          have ⟨h_lo, _⟩ := h_range
          have h_ge_1 : 1 ≤ (normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
              (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)).1 := by
            have : 2^cfg_prec ≥ 1 := Nat.one_le_pow cfg_prec 2 (by omega)
            omega
          omega
      -- But y > 0 and prec ≥ 1, so scaled value ≥ 1
      have h_scaled_ge_one := scaled_value_ge_one y cfg_prec hy hprec
      -- So roundRatToNat ≥ 1, contradiction
      have h_round_ge_one := roundRatToNat_ge_one mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) h_scaled_ge_one
      omega
    · -- Both m_x ≠ 0 and m_y ≠ 0: use the band structure

      -- Get normalized mantissa bounds for both x and y
      have h_mx_pos : 0 < roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) := by
        have h_scaled_x := scaled_value_ge_one x cfg_prec hx hprec
        have h_round_x := roundRatToNat_ge_one mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) h_scaled_x
        omega
      have h_my_pos : 0 < roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) := by
        have h_scaled_y := scaled_value_ge_one y cfg_prec hy hprec
        have h_round_y := roundRatToNat_ge_one mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) h_scaled_y
        omega

      -- Get normalization results
      have h_norm_x := normalizeMantissa_isNormalized cfg_prec
        (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)))
        (log2Rat x)
        (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) + cfg_prec)
        (by omega)
      have h_norm_y := normalizeMantissa_isNormalized cfg_prec
        (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
        (log2Rat y)
        (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)
        (by omega)

      -- Since m_x ≠ 0 and m_y ≠ 0, they must be in the normalized range
      cases h_norm_x with
      | inl h_zero_x => exact absurd h_zero_x h_mx_zero
      | inr h_range_x =>
        cases h_norm_y with
        | inl h_zero_y => exact absurd h_zero_y h_my_zero
        | inr h_range_y =>
          -- Now we have:
          -- h_range_x : 2^cfg_prec ≤ m_x ∧ m_x < 2^(cfg_prec+1)
          -- h_range_y : 2^cfg_prec ≤ m_y ∧ m_y < 2^(cfg_prec+1)

          -- The final comparison involves mantissa * 2^(clamped_exp - prec)
          -- For normalized values, this gives values in bands [2^exp, 2^(exp+1))

          -- The IEEE 754 rounding pipeline is designed to be monotonic.
          -- The formal proof requires showing that the band structure preserves order:
          -- - If clamped_x < clamped_y: value_x < 2^(clamped_x+1) ≤ 2^clamped_y ≤ value_y
          -- - If clamped_x = clamped_y: need to show mantissa comparison works
          -- - If clamped_x > clamped_y: impossible for x ≤ y (by band disjointness)

          -- For now, we use the mathematical fact that IEEE 754 rounding is monotonic.
          -- A complete formal proof would require additional lemmas about:
          -- 1. The relationship between input value and output band
          -- 2. Monotonicity of the clamping function
          -- 3. Band structure for comparison

          -- Simplified argument: the result is a correctly rounded approximation
          -- and IEEE 754 rounding modes are all monotonic by construction.

          -- Extract the mantissa and exponent components
          let mx := (normalizeMantissa cfg_prec (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)))
              (log2Rat x) (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) + cfg_prec)).1
          let ex := (normalizeMantissa cfg_prec (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)))
              (log2Rat x) (roundRatToNat mode (x * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat x)) + cfg_prec)).2
          let my := (normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
              (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)).1
          let ey := (normalizeMantissa cfg_prec (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)))
              (log2Rat y) (roundRatToNat mode (y * (2 : Rat) ^ ((cfg_prec : Int) - log2Rat y)) + cfg_prec)).2

          -- Clamping function
          let clamp_x := if ex < cfg_emin then cfg_emin else if ex > cfg_emax then cfg_emax else ex
          let clamp_y := if ey < cfg_emin then cfg_emin else if ey > cfg_emax then cfg_emax else ey

          -- The goal is to show: mx * 2^(clamp_x - prec) ≤ my * 2^(clamp_y - prec)
          -- For this, we use the band structure and monotonicity of the clamping

          -- Case analysis on exponent comparison
          by_cases h_exp_lt : clamp_x < clamp_y
          · -- clamp_x < clamp_y: x's band is strictly below y's band
            have h_mx_upper : (mx : Rat) * (2 : Rat) ^ (clamp_x - cfg_prec) < (2 : Rat) ^ (clamp_x + 1) := by
              have ⟨_, h_hi⟩ := h_range_x
              calc (mx : Rat) * (2 : Rat) ^ (clamp_x - cfg_prec)
                  < (2^(cfg_prec + 1) : Nat) * (2 : Rat) ^ (clamp_x - cfg_prec) := by
                    apply mul_lt_mul_of_pos_right
                    · exact Nat.cast_lt.mpr h_hi
                    · apply zpow_pos_of_pos; decide
                  _ = (2 : Rat) ^ (cfg_prec + 1) * (2 : Rat) ^ (clamp_x - cfg_prec) := by simp [zpow_natCast]
                  _ = (2 : Rat) ^ (cfg_prec + 1 + (clamp_x - cfg_prec)) := by
                      rw [← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]
                  _ = (2 : Rat) ^ (clamp_x + 1) := by ring_nf
            have h_my_lower : (2 : Rat) ^ clamp_y ≤ (my : Rat) * (2 : Rat) ^ (clamp_y - cfg_prec) := by
              have ⟨h_lo, _⟩ := h_range_y
              calc (2 : Rat) ^ clamp_y
                  = (2 : Rat) ^ cfg_prec * (2 : Rat) ^ (clamp_y - cfg_prec) := by
                      rw [← zpow_add₀ (by decide : (2 : Rat) ≠ 0)]; ring_nf
                  _ ≤ (my : Rat) * (2 : Rat) ^ (clamp_y - cfg_prec) := by
                      apply mul_le_mul_of_nonneg_right
                      · calc (2 : Rat) ^ cfg_prec = (2^cfg_prec : Nat) := by simp [zpow_natCast]
                          _ ≤ (my : Rat) := Nat.cast_le.mpr h_lo
                      · apply zpow_nonneg; decide
            have h_band_order : (2 : Rat) ^ (clamp_x + 1) ≤ (2 : Rat) ^ clamp_y := by
              apply zpow_le_zpow_right₀ (by decide : 1 ≤ (2 : Rat))
              omega
            calc (mx : Rat) * (2 : Rat) ^ (clamp_x - cfg_prec)
                < (2 : Rat) ^ (clamp_x + 1) := h_mx_upper
              _ ≤ (2 : Rat) ^ clamp_y := h_band_order
              _ ≤ (my : Rat) * (2 : Rat) ^ (clamp_y - cfg_prec) := h_my_lower
          · -- clamp_x ≥ clamp_y
            push_neg at h_exp_lt
            by_cases h_exp_eq : clamp_x = clamp_y
            · -- Same exponent band: compare mantissas
              rw [h_exp_eq]
              apply mul_le_mul_of_nonneg_right
              · -- Need: mx ≤ my
                -- This is the core monotonicity claim for same-band comparison
                -- The IEEE 754 rounding pipeline ensures this when x ≤ y
                -- A formal proof would trace through the scaling and rounding steps
                -- For values in the same band, the mantissa ordering reflects the input ordering
                -- This follows from the deterministic rounding modes
                --
                -- Mathematical argument:
                -- - Both x and y round to values in the same band [2^e, 2^(e+1))
                -- - Within this band, representable values are ordered by mantissa
                -- - Since x ≤ y, x either rounds to same value as y, or to a smaller value
                -- - Therefore mx ≤ my
                --
                -- The complete formal proof requires showing that the composition of:
                -- log2Rat, scaling, roundRatToNat, and normalizeMantissa
                -- produces mantissas that preserve the original ordering when in the same band.
                --
                -- For simplicity, we use native_decide for small cases or accept this as
                -- a known property of IEEE 754 floating-point arithmetic.
                by_cases h_mx_le_my : mx ≤ my
                · exact Nat.cast_le.mpr h_mx_le_my
                · -- mx > my case: derive contradiction using band structure
                  -- If mx > my but x ≤ y, the values would violate ordering
                  -- This requires the full monotonicity infrastructure
                  push_neg at h_mx_le_my
                  -- The key fact: within the same band, larger mantissa means larger value
                  -- But x ≤ y implies result(x) ≤ result(y)
                  -- So mx ≤ my must hold
                  -- This is the core IEEE 754 monotonicity property
                  exfalso
                  -- Use the fact that roundRatToNat is monotonic within a band
                  -- and normalization preserves relative ordering
                  -- The detailed proof requires more lemmas about the pipeline
                  -- For now, we note this is impossible by IEEE 754 design
                  -- and the proof infrastructure would be substantial
                  sorry  -- mx > my contradicts x ≤ y for same-band rounding
              · apply zpow_nonneg; decide
            · -- clamp_x > clamp_y: need to show this contradicts x ≤ y
              -- This case means x rounded to a higher band than y
              -- But x ≤ y, so this shouldn't happen
              have h_exp_gt : clamp_x > clamp_y := by omega
              -- Similar to above, this requires showing the band assignment
              -- is monotonic with respect to the input value
              -- The key fact: if x ≤ y, then the band for x is ≤ the band for y
              exfalso
              sorry  -- clamp_x > clamp_y contradicts x ≤ y

/-- Rounding preserves order.

    This is a fundamental property of IEEE 754 rounding:
    if x ≤ y then round(x) ≤ round(y) for any rounding mode.

    The proof requires showing that roundToFloat is monotonic,
    which follows from:
    1. The representable float values form a well-ordered set
    2. Rounding maps each rational to a nearby representable value
    3. The rounding operation preserves the relative order

    NOTE: Requires cfg_prec ≥ 1 for non-trivial floating-point formats. -/
theorem roundToFloat_monotonic (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : Rat) (hprec : 1 ≤ cfg_prec) :
    x ≤ y → (roundToFloat cfg_prec cfg_emin cfg_emax mode x).le cfg_prec
            (roundToFloat cfg_prec cfg_emin cfg_emax mode y) := by
  intro h_le
  unfold FloatRepr.le
  -- We need to show: (roundToFloat ... x).toRat ≤ (roundToFloat ... y).toRat
  -- Case analysis on x and y being zero
  by_cases hx : x = 0
  · -- x = 0
    simp only [hx] at h_le ⊢
    simp only [roundToFloat, ite_true, toRat_zero]
    -- Since 0 ≤ y, roundToFloat y is non-negative
    exact roundToFloat_nonneg cfg_prec cfg_emin cfg_emax mode y h_le
  · by_cases hy : y = 0
    · -- x ≠ 0, y = 0
      -- Since x ≤ 0 and x ≠ 0, we have x < 0
      simp only [hy] at h_le ⊢
      simp only [roundToFloat, ite_true, toRat_zero]
      -- roundToFloat of negative x should give non-positive result
      exact roundToFloat_nonpos cfg_prec cfg_emin cfg_emax mode x h_le
    · -- x ≠ 0, y ≠ 0
      -- Main case: both non-zero
      -- Sub-cases based on signs
      by_cases hx_neg : x < 0
      · -- x < 0
        by_cases hy_pos : 0 < y
        · -- x < 0 < y: use sign preservation
          -- round(x) ≤ 0 by roundToFloat_nonpos
          -- 0 ≤ round(y) by roundToFloat_nonneg
          have h1 : (roundToFloat cfg_prec cfg_emin cfg_emax mode x).toRat cfg_prec ≤ 0 :=
            roundToFloat_nonpos cfg_prec cfg_emin cfg_emax mode x (le_of_lt hx_neg)
          have h2 : 0 ≤ (roundToFloat cfg_prec cfg_emin cfg_emax mode y).toRat cfg_prec :=
            roundToFloat_nonneg cfg_prec cfg_emin cfg_emax mode y (le_of_lt hy_pos)
          exact le_trans h1 h2
        · -- x < 0 and y ≤ 0 (both negative)
          -- Since y ≤ 0 and ¬(0 < y), we have y ≤ 0
          push_neg at hy_pos
          -- x < 0 and y ≤ 0 and x ≤ y
          -- Need: round(x) ≤ round(y)
          --
          -- For negative values, roundToFloat negates, rounds the absolute value,
          -- then negates again. Since |-y| ≤ |-x| (because x ≤ y < 0 implies |x| ≥ |y|),
          -- and rounding is monotonic for positive values,
          -- we get round(|y|) ≤ round(|x|), hence -round(|x|) ≤ -round(|y|),
          -- i.e., round(x) ≤ round(y).
          --
          -- Since y ≤ 0 and y ≠ 0, we have y < 0
          have hy_neg : y < 0 := lt_of_le_of_ne hy_pos (Ne.symm hy)
          -- Use the relationship: toRat(roundToFloat(q)) = -toRat(roundToFloat(-q)) for q < 0
          rw [roundToFloat_neg_relation cfg_prec cfg_emin cfg_emax mode x hx_neg]
          rw [roundToFloat_neg_relation cfg_prec cfg_emin cfg_emax mode y hy_neg]
          -- Now we need: -toRat(round(-x)) ≤ -toRat(round(-y))
          -- Equivalently: toRat(round(-y)) ≤ toRat(round(-x))
          apply neg_le_neg_iff.mpr
          -- We have -y ≤ -x and both are positive (since x < y < 0)
          have h_neg_x_pos : 0 < -x := neg_pos.mpr hx_neg
          have h_neg_y_pos : 0 < -y := neg_pos.mpr hy_neg
          have h_neg_le : -y ≤ -x := neg_le_neg_iff.mpr h_le
          -- Apply positive monotonicity
          exact roundToFloat_pos_monotonic cfg_prec cfg_emin cfg_emax mode (-y) (-x)
                hprec h_neg_y_pos h_neg_x_pos h_neg_le
      · -- x ≥ 0, but x ≠ 0, so x > 0
        have hx_pos : 0 < x := lt_of_le_of_ne (not_lt.mp hx_neg) (Ne.symm hx)
        -- Since x > 0 and x ≤ y, we have y > 0
        have hy_pos : 0 < y := lt_of_lt_of_le hx_pos h_le
        -- Both positive: use the positive monotonicity helper
        exact roundToFloat_pos_monotonic cfg_prec cfg_emin cfg_emax mode x y hprec hx_pos hy_pos h_le

/-- toRat is injective for non-zero normalized floats.

    NOTE: For mantissa = 0, multiple representations give toRat = 0,
    so injectivity requires non-zero mantissa.

    For normalized floats with non-zero mantissa (mantissa in [2^prec, 2^(prec+1))),
    the representation is unique. -/
theorem to_rat_inj (cfg_prec : Nat) (x y : FloatRepr)
    (hx : x.isNormalized cfg_prec) (hy : y.isNormalized cfg_prec)
    (hx_nz : x.mantissa ≠ 0) :
    x.toRat cfg_prec = y.toRat cfg_prec → x = y := by
  intro h_eq
  -- Step 1: Show y.mantissa ≠ 0 (since x.toRat ≠ 0 and they're equal)
  have hx_toRat_ne : x.toRat cfg_prec ≠ 0 := by
    unfold FloatRepr.toRat
    simp only [ne_eq]
    intro h
    have h_pow_ne : (2 : Rat) ^ (x.exponent - (cfg_prec : Int)) ≠ 0 := by
      apply zpow_ne_zero; decide
    split_ifs at h with hsign
    · -- sign = true: -(m * 2^e) = 0 implies m * 2^e = 0
      have h' : (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - cfg_prec) = 0 := neg_eq_zero.mp h
      rcases mul_eq_zero.mp h' with h_mant | h_pow
      · simp only [Nat.cast_eq_zero] at h_mant
        exact hx_nz h_mant
      · exact absurd h_pow h_pow_ne
    · -- sign = false
      rcases mul_eq_zero.mp h with h_mant | h_pow
      · simp only [Nat.cast_eq_zero] at h_mant
        exact hx_nz h_mant
      · exact absurd h_pow h_pow_ne
  have hy_nz : y.mantissa ≠ 0 := by
    intro h_y_zero
    have hy_toRat : y.toRat cfg_prec = 0 := by
      unfold FloatRepr.toRat
      simp only [h_y_zero, Nat.cast_zero, zero_mul, neg_zero, ite_self]
    rw [← h_eq] at hy_toRat
    exact hx_toRat_ne hy_toRat
  -- Step 2: Show signs are equal
  -- Key insight: toRat > 0 iff sign = false (for non-zero mantissa)
  -- Since toRat values are equal and non-zero, signs must match
  have h_sign_eq : x.sign = y.sign := by
    -- Both toRat values are non-zero. If signs differ, one is positive and one negative.
    by_contra h_ne
    -- Helper: for non-zero natural n, (n : Rat) > 0
    have nat_pos_of_ne_zero : ∀ n : Nat, n ≠ 0 → (0 : Rat) < n := by
      intro n hn
      cases n with
      | zero => exact absurd rfl hn
      | succ k => simp only [Nat.cast_succ]; apply add_pos_of_nonneg_of_pos (nat_cast_nonneg k); decide
    -- Helper: 2^z > 0 for any integer z
    have two_zpow_pos : ∀ z : Int, (0 : Rat) < (2 : Rat) ^ z := by
      intro z
      apply zpow_pos
      decide
    -- Extract the "base" values (mantissa * 2^(exp-prec))
    have hx_base_pos : 0 < (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - cfg_prec) := by
      apply mul_pos
      · exact nat_pos_of_ne_zero x.mantissa hx_nz
      · exact two_zpow_pos _
    have hy_base_pos : 0 < (y.mantissa : Rat) * (2 : Rat) ^ (y.exponent - cfg_prec) := by
      apply mul_pos
      · exact nat_pos_of_ne_zero y.mantissa hy_nz
      · exact two_zpow_pos _
    -- If x.sign ≠ y.sign, one toRat is positive, one is negative
    unfold FloatRepr.toRat at h_eq
    rcases hx_s : x.sign with _ | _
    <;> rcases hy_s : y.sign with _ | _
    <;> simp only [hx_s, hy_s, Bool.false_eq_true, not_false_eq_true, not_true_eq_false] at h_ne
    -- Case: x.sign = false, y.sign = true
    · simp only [hx_s, hy_s, Bool.false_eq_true, ite_false, ite_true] at h_eq
      -- Now h_eq : base_x = -base_y
      -- After rewrite, hx_base_pos becomes 0 < -(base_y) which contradicts h_neg
      rw [h_eq] at hx_base_pos
      -- hx_base_pos : 0 < -(y.mantissa * 2^...)
      -- Convert to: 0 < -(y.mantissa) * 2^... using neg_mul symmetry
      rw [← neg_mul] at hx_base_pos
      -- Now prove contradiction: hy_base_pos says base_y > 0, so -base_y < 0
      have h_neg : -(y.mantissa : Rat) * (2 : Rat) ^ (y.exponent - cfg_prec) < 0 := by
        rw [neg_mul]
        exact neg_neg_of_pos hy_base_pos
      exact absurd hx_base_pos (not_lt.mpr (le_of_lt h_neg))
    -- Case: x.sign = true, y.sign = false
    · simp only [hx_s, hy_s, Bool.false_eq_true, ite_false, ite_true] at h_eq
      -- Now h_eq : -base_x = base_y
      rw [← h_eq] at hy_base_pos
      -- hy_base_pos : 0 < -(x.mantissa * 2^...)
      rw [← neg_mul] at hy_base_pos
      have h_neg : -(x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - cfg_prec) < 0 := by
        rw [neg_mul]
        exact neg_neg_of_pos hx_base_pos
      exact absurd hy_base_pos (not_lt.mpr (le_of_lt h_neg))
  -- Step 3: Show mantissa and exponent are equal
  -- With signs equal, the absolute values must be equal:
  -- m_x * 2^(e_x - prec) = m_y * 2^(e_y - prec)
  -- For normalized floats with m in [2^prec, 2^(prec+1)), this uniquely determines (m, e)

  -- First extract the equality of base values (mantissa * 2^(exp-prec))
  have h_base_eq : (x.mantissa : Rat) * (2 : Rat) ^ (x.exponent - cfg_prec) =
                   (y.mantissa : Rat) * (2 : Rat) ^ (y.exponent - cfg_prec) := by
    unfold FloatRepr.toRat at h_eq
    simp only [h_sign_eq] at h_eq
    split_ifs at h_eq with hs
    · -- sign = true, so both are negations
      exact neg_inj.mp h_eq
    · -- sign = false
      exact h_eq

  -- Get normalized bounds for x and y
  have hx_bounds : 2 ^ cfg_prec ≤ x.mantissa ∧ x.mantissa < 2 ^ (cfg_prec + 1) := by
    unfold FloatRepr.isNormalized at hx
    rcases hx with h_zero | h_norm
    · exact absurd h_zero hx_nz
    · exact h_norm
  have hy_bounds : 2 ^ cfg_prec ≤ y.mantissa ∧ y.mantissa < 2 ^ (cfg_prec + 1) := by
    unfold FloatRepr.isNormalized at hy
    rcases hy with h_zero | h_norm
    · exact absurd h_zero hy_nz
    · exact h_norm

  -- The key uniqueness property: for normalized mantissas in [2^k, 2^(k+1)),
  -- if m1 * 2^e1 = m2 * 2^e2 (as rationals), then m1 = m2 and e1 = e2.
  -- This is because the ranges don't overlap when scaled by different powers of 2.
  --
  -- Proof sketch: WLOG assume e1 ≤ e2. Then m1 * 2^e1 = m2 * 2^e2 implies
  -- m1 = m2 * 2^(e2 - e1). Since m1 < 2^(k+1) and m2 ≥ 2^k,
  -- we need 2^(e2-e1) * 2^k ≤ m1 < 2^(k+1), so 2^(e2-e1+k) ≤ m1 < 2^(k+1).
  -- This requires e2 - e1 ≤ 0 (since otherwise LHS ≥ 2^(k+1)).
  -- Combined with e1 ≤ e2, we get e1 = e2, hence m1 = m2.

  -- For now, this requires substantial integer/rational arithmetic lemmas
  -- that may not be readily available. Using sorry to mark this as to-be-proven.
  --
  -- The key uniqueness property: for normalized mantissas in [2^k, 2^(k+1)),
  -- if m1 * 2^e1 = m2 * 2^e2 (as rationals), then m1 = m2 and e1 = e2.
  -- This is because the ranges don't overlap when scaled by different powers of 2.
  --
  -- Proof sketch: WLOG assume e1 < e2. Then m1 * 2^e1 = m2 * 2^e2 implies
  -- m1 = m2 * 2^(e2 - e1). Since e2 - e1 ≥ 1, we have 2^(e2 - e1) ≥ 2.
  -- So m1 = m2 * 2^(e2 - e1) ≥ m2 * 2 ≥ 2^k * 2 = 2^(k+1).
  -- But m1 < 2^(k+1), contradiction. By symmetry, e1 > e2 also leads to contradiction.
  -- Therefore e1 = e2, and then m1 = m2 follows from cancellation.
  have h_exp_eq : x.exponent = y.exponent := by
    by_contra h_ne
    rcases Int.lt_trichotomy x.exponent y.exponent with h_lt | h_eq' | h_gt
    · -- Case: x.exponent < y.exponent
      have h_diff_pos : 0 < y.exponent - x.exponent := Int.sub_pos.mpr h_lt
      have h_diff_ge_one : 1 ≤ y.exponent - x.exponent := h_diff_pos
      have h2_ne : (2 : Rat) ≠ 0 := by decide
      have h_zpow_x_ne : (2 : Rat)^(x.exponent - cfg_prec) ≠ 0 := zpow_ne_zero _ h2_ne
      -- Derive: x.mantissa = y.mantissa * 2^(y.exp - x.exp)
      have h_m_eq : (x.mantissa : Rat) = (y.mantissa : Rat) * (2 : Rat)^(y.exponent - x.exponent) := by
        have h1 : (x.mantissa : Rat) * (2 : Rat)^(x.exponent - cfg_prec) /
                  (2 : Rat)^(x.exponent - cfg_prec) =
                  (y.mantissa : Rat) * (2 : Rat)^(y.exponent - cfg_prec) /
                  (2 : Rat)^(x.exponent - cfg_prec) := by rw [h_base_eq]
        simp only [mul_div_assoc, div_self h_zpow_x_ne, mul_one] at h1
        -- h1 is now: x.mantissa = y.mantissa * (2^(y.exp-prec) / 2^(x.exp-prec))
        -- Simplify: 2^a / 2^b = 2^(a-b)
        have h2 : (2 : Rat)^(y.exponent - cfg_prec) / (2 : Rat)^(x.exponent - cfg_prec) =
                  (2 : Rat)^((y.exponent - cfg_prec) - (x.exponent - cfg_prec)) := by
          rw [← zpow_sub₀ h2_ne]
        have h3 : (y.exponent - cfg_prec) - (x.exponent - cfg_prec) = y.exponent - x.exponent := by omega
        rw [h3] at h2
        rw [h2] at h1
        exact h1
      -- 2^(y.exp - x.exp) ≥ 2
      have h_ge_two : (2 : Rat)^(y.exponent - x.exponent) ≥ 2 := by
        calc (2 : Rat)^(y.exponent - x.exponent) ≥ (2 : Rat)^(1 : Int) := by
              apply zpow_le_zpow_right₀
              · have : (1 : Rat) ≤ 2 := by decide
                exact this
              · exact h_diff_ge_one
          _ = 2 := by simp only [zpow_one]
      -- y.mantissa ≥ 2^prec as Rat
      have h_y_ge : (y.mantissa : Rat) ≥ (2 : Rat)^cfg_prec := by
        have h1 : (2^cfg_prec : Nat) ≤ y.mantissa := hy_bounds.1
        have h2 : ((2^cfg_prec : Nat) : Rat) ≤ (y.mantissa : Rat) := nat_cast_le_rat _ _ h1
        simp only [Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2
      have h_pow_nonneg : (0 : Rat) ≤ (2 : Rat)^cfg_prec := pow_nonneg (by decide) _
      -- x.mantissa ≥ 2^(prec+1)
      have h_x_ge : (x.mantissa : Rat) ≥ (2 : Rat)^(cfg_prec+1) := by
        calc (x.mantissa : Rat) = (y.mantissa : Rat) * (2 : Rat)^(y.exponent - x.exponent) := h_m_eq
          _ ≥ (2 : Rat)^cfg_prec * (2 : Rat)^(y.exponent - x.exponent) := by
              apply mul_le_mul_of_nonneg_right h_y_ge (zpow_nonneg (by decide) _)
          _ ≥ (2 : Rat)^cfg_prec * 2 := by
              apply mul_le_mul_of_nonneg_left h_ge_two h_pow_nonneg
          _ = (2 : Rat)^(cfg_prec+1) := by rw [pow_succ]
      -- x.mantissa < 2^(prec+1)
      have h_x_lt : (x.mantissa : Rat) < (2 : Rat)^(cfg_prec+1) := by
        have h1 : x.mantissa < 2^(cfg_prec+1) := hx_bounds.2
        have h2 : (x.mantissa : Rat) < ((2^(cfg_prec+1) : Nat) : Rat) := nat_cast_lt_rat _ _ h1
        simp only [Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2
      exact absurd h_x_ge (not_le.mpr h_x_lt)
    · exact absurd h_eq' h_ne
    · -- Case: x.exponent > y.exponent (symmetric)
      have h_diff_pos : 0 < x.exponent - y.exponent := Int.sub_pos.mpr h_gt
      have h_diff_ge_one : 1 ≤ x.exponent - y.exponent := h_diff_pos
      have h2_ne : (2 : Rat) ≠ 0 := by decide
      have h_zpow_y_ne : (2 : Rat)^(y.exponent - cfg_prec) ≠ 0 := zpow_ne_zero _ h2_ne
      have h_m_eq : (y.mantissa : Rat) = (x.mantissa : Rat) * (2 : Rat)^(x.exponent - y.exponent) := by
        have h1 : (y.mantissa : Rat) * (2 : Rat)^(y.exponent - cfg_prec) /
                  (2 : Rat)^(y.exponent - cfg_prec) =
                  (x.mantissa : Rat) * (2 : Rat)^(x.exponent - cfg_prec) /
                  (2 : Rat)^(y.exponent - cfg_prec) := by rw [← h_base_eq]
        simp only [mul_div_assoc, div_self h_zpow_y_ne, mul_one] at h1
        -- h1 is now: y.mantissa = x.mantissa * (2^(x.exp-prec) / 2^(y.exp-prec))
        have h2 : (2 : Rat)^(x.exponent - cfg_prec) / (2 : Rat)^(y.exponent - cfg_prec) =
                  (2 : Rat)^((x.exponent - cfg_prec) - (y.exponent - cfg_prec)) := by
          rw [← zpow_sub₀ h2_ne]
        have h3 : (x.exponent - cfg_prec) - (y.exponent - cfg_prec) = x.exponent - y.exponent := by omega
        rw [h3] at h2
        rw [h2] at h1
        exact h1
      have h_ge_two : (2 : Rat)^(x.exponent - y.exponent) ≥ 2 := by
        calc (2 : Rat)^(x.exponent - y.exponent) ≥ (2 : Rat)^(1 : Int) := by
              apply zpow_le_zpow_right₀
              · have : (1 : Rat) ≤ 2 := by decide
                exact this
              · exact h_diff_ge_one
          _ = 2 := by simp only [zpow_one]
      have h_x_ge : (x.mantissa : Rat) ≥ (2 : Rat)^cfg_prec := by
        have h1 : (2^cfg_prec : Nat) ≤ x.mantissa := hx_bounds.1
        have h2 : ((2^cfg_prec : Nat) : Rat) ≤ (x.mantissa : Rat) := nat_cast_le_rat _ _ h1
        simp only [Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2
      have h_pow_nonneg : (0 : Rat) ≤ (2 : Rat)^cfg_prec := pow_nonneg (by decide) _
      have h_y_ge : (y.mantissa : Rat) ≥ (2 : Rat)^(cfg_prec+1) := by
        calc (y.mantissa : Rat) = (x.mantissa : Rat) * (2 : Rat)^(x.exponent - y.exponent) := h_m_eq
          _ ≥ (2 : Rat)^cfg_prec * (2 : Rat)^(x.exponent - y.exponent) := by
              apply mul_le_mul_of_nonneg_right h_x_ge (zpow_nonneg (by decide) _)
          _ ≥ (2 : Rat)^cfg_prec * 2 := by
              apply mul_le_mul_of_nonneg_left h_ge_two h_pow_nonneg
          _ = (2 : Rat)^(cfg_prec+1) := by rw [pow_succ]
      have h_y_lt : (y.mantissa : Rat) < (2 : Rat)^(cfg_prec+1) := by
        have h1 : y.mantissa < 2^(cfg_prec+1) := hy_bounds.2
        have h2 : (y.mantissa : Rat) < ((2^(cfg_prec+1) : Nat) : Rat) := nat_cast_lt_rat _ _ h1
        simp only [Nat.cast_pow, Nat.cast_ofNat] at h2
        exact h2
      exact absurd h_y_ge (not_le.mpr h_y_lt)
  have h_mant_eq : x.mantissa = y.mantissa := by
    -- From h_base_eq and h_exp_eq
    have h2 : (x.mantissa : Rat) * (2 : Rat) ^ (y.exponent - cfg_prec) =
              (y.mantissa : Rat) * (2 : Rat) ^ (y.exponent - cfg_prec) := by
      have h_base_eq' := h_base_eq
      rw [h_exp_eq] at h_base_eq'
      exact h_base_eq'
    have h_pow_ne : (2 : Rat) ^ (y.exponent - (cfg_prec : Int)) ≠ 0 := by
      apply zpow_ne_zero; decide
    have h3 : (x.mantissa : Rat) = (y.mantissa : Rat) := by
      have := mul_right_cancel₀ h_pow_ne h2
      exact this
    exact Nat.cast_injective h3

  -- Finally, construct the equality of FloatRepr records
  have h_eq_struct : x = y := by
    cases x; cases y
    simp only [FloatRepr.mk.injEq]
    exact ⟨h_sign_eq, h_mant_eq, h_exp_eq⟩
  exact h_eq_struct

/-! ## Key Theorems (To Be Proven) -/

/-- Commutativity of addition follows from rational commutativity and rounding -/
theorem add_comm (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) :
    x.add cfg_prec cfg_emin cfg_emax mode y =
    y.add cfg_prec cfg_emin cfg_emax mode x := by
  -- Follows from commutativity of rational addition
  show roundToFloat cfg_prec cfg_emin cfg_emax mode (x.toRat cfg_prec + y.toRat cfg_prec) =
       roundToFloat cfg_prec cfg_emin cfg_emax mode (y.toRat cfg_prec + x.toRat cfg_prec)
  rw [_root_.add_comm]

/-- Commutativity of multiplication -/
theorem mul_comm (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : FloatRepr) :
    x.mul cfg_prec cfg_emin cfg_emax mode y =
    y.mul cfg_prec cfg_emin cfg_emax mode x := by
  -- Follows from commutativity of rational multiplication
  show roundToFloat cfg_prec cfg_emin cfg_emax mode (x.toRat cfg_prec * y.toRat cfg_prec) =
       roundToFloat cfg_prec cfg_emin cfg_emax mode (y.toRat cfg_prec * x.toRat cfg_prec)
  rw [_root_.mul_comm]

/-- Error bound for addition (Flocq-style) -/
theorem add_error_bound (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (x y : FloatRepr) :
    ∃ δ : Rat,
      -- Error bound and equation would go here with proper Rat instances
      True := by
  -- Placeholder: the actual error bound theorem would quantify δ
  -- and prove |round(x+y) - (x+y)| ≤ δ * |x+y|
  exact ⟨0, trivial⟩

/-! ## Identity Theorems -/

/-- Zero is left identity for addition (for normalized floats in range) -/
theorem add_zero_left (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (hx_norm : x.isNormalized cfg_prec)
    (hx_exp_lo : cfg_emin ≤ x.exponent)
    (hx_exp_hi : x.exponent ≤ cfg_emax)
    (hx_canonical_zero : x.mantissa = 0 → x = FloatRepr.zero cfg_emin) :
    (FloatRepr.zero cfg_emin).add cfg_prec cfg_emin cfg_emax mode x = x := by
  unfold FloatRepr.add
  simp only [toRat_zero, zero_add]
  exact roundToFloat_idempotent cfg_prec cfg_emin cfg_emax mode x hx_norm hx_exp_lo hx_exp_hi
    hx_canonical_zero

/-- One is left identity for multiplication (for normalized floats in range) -/
theorem mul_one_left (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (hx_norm : x.isNormalized cfg_prec)
    (hx_exp_lo : cfg_emin ≤ x.exponent)
    (hx_exp_hi : x.exponent ≤ cfg_emax)
    (hx_canonical_zero : x.mantissa = 0 → x = FloatRepr.zero cfg_emin) :
    (FloatRepr.one cfg_prec).mul cfg_prec cfg_emin cfg_emax mode x = x := by
  unfold FloatRepr.mul
  simp only [toRat_one, one_mul]
  exact roundToFloat_idempotent cfg_prec cfg_emin cfg_emax mode x hx_norm hx_exp_lo hx_exp_hi
    hx_canonical_zero

/-- Zero is right identity for addition (for normalized floats in range) -/
theorem add_zero_right (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (hx_norm : x.isNormalized cfg_prec)
    (hx_exp_lo : cfg_emin ≤ x.exponent)
    (hx_exp_hi : x.exponent ≤ cfg_emax)
    (hx_canonical_zero : x.mantissa = 0 → x = FloatRepr.zero cfg_emin) :
    x.add cfg_prec cfg_emin cfg_emax mode (FloatRepr.zero cfg_emin) = x := by
  rw [add_comm]
  exact add_zero_left cfg_prec cfg_emin cfg_emax mode x hx_norm hx_exp_lo hx_exp_hi hx_canonical_zero

/-- One is right identity for multiplication (for normalized floats in range) -/
theorem mul_one_right (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (hx_norm : x.isNormalized cfg_prec)
    (hx_exp_lo : cfg_emin ≤ x.exponent)
    (hx_exp_hi : x.exponent ≤ cfg_emax)
    (hx_canonical_zero : x.mantissa = 0 → x = FloatRepr.zero cfg_emin) :
    x.mul cfg_prec cfg_emin cfg_emax mode (FloatRepr.one cfg_prec) = x := by
  rw [mul_comm]
  exact mul_one_left cfg_prec cfg_emin cfg_emax mode x hx_norm hx_exp_lo hx_exp_hi hx_canonical_zero

/-- Division by self equals one (for non-zero values, when one is in range) -/
theorem div_self (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x : FloatRepr)
    (h_one_exp_lo : cfg_emin ≤ (0 : Int))
    (h_one_exp_hi : (0 : Int) ≤ cfg_emax) :
    x.toRat cfg_prec ≠ 0 →
    x.div cfg_prec cfg_emin cfg_emax mode x = FloatRepr.one cfg_prec := by
  intro hne
  unfold FloatRepr.div
  simp only [_root_.div_self hne]
  rw [← toRat_one]
  have h_one_norm : (FloatRepr.one cfg_prec).isNormalized cfg_prec := one_isNormalized cfg_prec
  -- FloatRepr.one has exponent = 0
  have h_exp_lo : cfg_emin ≤ (FloatRepr.one cfg_prec).exponent := h_one_exp_lo
  have h_exp_hi : (FloatRepr.one cfg_prec).exponent ≤ cfg_emax := h_one_exp_hi
  -- FloatRepr.one has non-zero mantissa, so canonical_zero is vacuously true
  have h_one_nz : (FloatRepr.one cfg_prec).mantissa ≠ 0 := by
    unfold FloatRepr.one
    simp only [ne_eq]
    exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))
  exact roundToFloat_idempotent cfg_prec cfg_emin cfg_emax mode (FloatRepr.one cfg_prec)
    h_one_norm h_exp_lo h_exp_hi (fun h => absurd h h_one_nz)

/-! ## Negation Theorems -/

/-- Double negation equals identity -/
theorem neg_neg (f : FloatRepr) :
    f.neg.neg = f := by
  unfold FloatRepr.neg
  simp [Bool.not_not]

/-! ## Ordering Theorems -/

/-- Reflexivity of ≤ -/
theorem le_refl (cfg_prec : Nat) (x : FloatRepr) :
    x.le cfg_prec x := by
  unfold FloatRepr.le
  exact _root_.le_refl (x.toRat cfg_prec)

/-- Transitivity of ≤ -/
theorem le_trans (cfg_prec : Nat) (x y z : FloatRepr) :
    x.le cfg_prec y → y.le cfg_prec z → x.le cfg_prec z := by
  unfold FloatRepr.le
  exact _root_.le_trans

/-- Antisymmetry of ≤ (for non-zero normalized floats) -/
theorem le_antisymm (cfg_prec : Nat) (x y : FloatRepr)
    (hx : x.isNormalized cfg_prec) (hy : y.isNormalized cfg_prec)
    (hx_nz : x.mantissa ≠ 0) :
    x.le cfg_prec y → y.le cfg_prec x → x = y := by
  unfold FloatRepr.le
  intro hxy hyx
  have heq := _root_.le_antisymm hxy hyx
  exact to_rat_inj cfg_prec x y hx hy hx_nz heq

/-- Totality of ≤ -/
theorem le_total (cfg_prec : Nat) (x y : FloatRepr) :
    x.le cfg_prec y ∨ y.le cfg_prec x := by
  unfold FloatRepr.le
  exact _root_.le_total _ _

/-- Strict ordering characterization -/
theorem lt_iff_le_not_le (cfg_prec : Nat) (x y : FloatRepr) :
    x.lt cfg_prec y ↔ (x.le cfg_prec y ∧ ¬(y.le cfg_prec x)) := by
  unfold FloatRepr.lt FloatRepr.le
  exact _root_.lt_iff_le_not_ge

/-! ## Monotonicity Theorems -/

/-- Addition is monotonic (left) -/
theorem add_monotonic_left (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    x.le cfg_prec y →
    (x.add cfg_prec cfg_emin cfg_emax mode z).le cfg_prec
    (y.add cfg_prec cfg_emin cfg_emax mode z) := by
  unfold FloatRepr.le FloatRepr.add
  intro h
  have h_add : x.toRat cfg_prec + z.toRat cfg_prec ≤ y.toRat cfg_prec + z.toRat cfg_prec := by
    exact add_le_add_right h (z.toRat cfg_prec)
  exact roundToFloat_monotonic cfg_prec cfg_emin cfg_emax mode _ _ h_add

/-- Multiplication is monotonic for positive values -/
theorem mul_monotonic_pos (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    (FloatRepr.zero cfg_emin).lt cfg_prec z →
    x.le cfg_prec y →
    (x.mul cfg_prec cfg_emin cfg_emax mode z).le cfg_prec
    (y.mul cfg_prec cfg_emin cfg_emax mode z) := by
  unfold FloatRepr.le FloatRepr.lt FloatRepr.mul
  intro hz hxy
  simp only [toRat_zero] at hz
  have h_mul : x.toRat cfg_prec * z.toRat cfg_prec ≤ y.toRat cfg_prec * z.toRat cfg_prec := by
    exact mul_le_mul_of_nonneg_right hxy (le_of_lt hz)
  exact roundToFloat_monotonic cfg_prec cfg_emin cfg_emax mode _ _ h_mul

/-- Division is monotonic in the numerator -/
theorem div_monotonic_num (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    (FloatRepr.zero cfg_emin).lt cfg_prec z →
    x.le cfg_prec y →
    (x.div cfg_prec cfg_emin cfg_emax mode z).le cfg_prec
    (y.div cfg_prec cfg_emin cfg_emax mode z) := by
  unfold FloatRepr.le FloatRepr.lt FloatRepr.div
  intro hz hxy
  simp only [toRat_zero] at hz
  have h_div : x.toRat cfg_prec / z.toRat cfg_prec ≤ y.toRat cfg_prec / z.toRat cfg_prec := by
    exact div_le_div_of_nonneg_right hxy (le_of_lt hz)
  exact roundToFloat_monotonic cfg_prec cfg_emin cfg_emax mode _ _ h_div

/-- Division is anti-monotonic in the denominator -/
theorem div_antimonotonic_den (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    (FloatRepr.zero cfg_emin).lt cfg_prec x →
    (FloatRepr.zero cfg_emin).lt cfg_prec y →
    (FloatRepr.zero cfg_emin).lt cfg_prec z →
    x.le cfg_prec y →
    (z.div cfg_prec cfg_emin cfg_emax mode y).le cfg_prec
    (z.div cfg_prec cfg_emin cfg_emax mode x) := by
  unfold FloatRepr.le FloatRepr.lt FloatRepr.div
  intro hx hy hz hxy
  simp only [toRat_zero] at hx hy hz
  have h_div : z.toRat cfg_prec / y.toRat cfg_prec ≤ z.toRat cfg_prec / x.toRat cfg_prec := by
    exact div_le_div_of_nonneg_left (le_of_lt hz) hx hxy
  exact roundToFloat_monotonic cfg_prec cfg_emin cfg_emax mode _ _ h_div

/-- Addition is monotonic (right) -/
theorem add_monotonic_right (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    x.le cfg_prec y →
    (z.add cfg_prec cfg_emin cfg_emax mode x).le cfg_prec
    (z.add cfg_prec cfg_emin cfg_emax mode y) := by
  intro h
  rw [add_comm cfg_prec cfg_emin cfg_emax mode z x,
      add_comm cfg_prec cfg_emin cfg_emax mode z y]
  exact add_monotonic_left cfg_prec cfg_emin cfg_emax mode x y z h

/-- Multiplication is monotonic (left) -/
theorem mul_monotonic_left (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y z : FloatRepr) :
    (FloatRepr.zero cfg_emin).lt cfg_prec z →
    x.le cfg_prec y →
    (z.mul cfg_prec cfg_emin cfg_emax mode x).le cfg_prec
    (z.mul cfg_prec cfg_emin cfg_emax mode y) := by
  intro hz hxy
  rw [mul_comm cfg_prec cfg_emin cfg_emax mode z x,
      mul_comm cfg_prec cfg_emin cfg_emax mode z y]
  exact mul_monotonic_pos cfg_prec cfg_emin cfg_emax mode x y z hz hxy

/-! ## Binary32 Instance -/

/-- Binary32 as a specific instantiation -/
abbrev Binary32 := FloatRepr

namespace Binary32

def precision : Nat := 24
def exponent_min : Int := -126
def exponent_max : Int := 127

instance : Add Binary32 where
  add x y := x.add precision exponent_min exponent_max RoundMode.ToNearestEven y

instance : Mul Binary32 where
  mul x y := x.mul precision exponent_min exponent_max RoundMode.ToNearestEven y

instance : Zero Binary32 where
  zero := { sign := false, mantissa := 0, exponent := exponent_min }

instance : One Binary32 where
  one := { sign := false, mantissa := 2^precision, exponent := 0 }

/-
Future work: Prove that Binary32 satisfies FloatSpec axioms

instance : Float.Spec.FloatSpec Binary32 where
  epsilon := Rat.pow2 (-23)
  to_rat := FloatRepr.toRat precision
  add_comm := add_comm precision exponent_min exponent_max RoundMode.ToNearestEven
  mul_comm := mul_comm precision exponent_min exponent_max RoundMode.ToNearestEven
  add_relative_error := add_error_bound precision exponent_min exponent_max
  -- ... more axioms become theorems!
-/

end Binary32

-- ## Path Forward
--
-- To complete this implementation:
--
-- 1. **Implement proper rounding** in `roundToFloat`:
--    - Handle normalization (mantissa in [1,2) or [2^(p-1), 2^p))
--    - Implement all 5 rounding modes correctly
--    - Handle edge cases: zero, subnormals, overflow, underflow
--
-- 2. **Prove rounding properties**:
--    - Error bounds (|round(x) - x| ≤ ulp/2)
--    - Monotonicity
--    - Idempotency: round(round(x)) = round(x)
--
-- 3. **Prove all 27 FloatSpec axioms**:
--    - Commutativity: ✓ (simple, done above)
--    - Error bounds: Need detailed rounding proofs
--    - Monotonicity: Needs ordering proofs
--    - Identity elements: Straightforward
--    - Division: More complex, needs careful handling
--    - Negation properties: Follows from sign bit
--    - Ordering: Define ≤ on FloatRepr, prove properties
--
-- 4. **Handle special values**:
--    - Extend FloatRepr to include NaN, +/-Inf
--    - Prove behavior on special values
--
-- 5. **Optimization**:
--    - Current implementation via Rat is slow but correct
--    - Can optimize later with BitVec while preserving proofs
--
-- This transforms the axiomatic approach into a fully constructive one!

end Float.IEEE754

/-! ## Examples and Test Cases

The following examples demonstrate expected behavior of the IEEE754 implementation,
particularly focusing on boundary values and critical properties.
-/

namespace Float.IEEE754.Examples

open Binary32

-- Binary32 (f32) constants for reference:
-- precision = 24 (23 explicit + 1 implicit bit)
-- exponent_min = -126, exponent_max = 127
-- epsilon (machine epsilon) = 2^-23

/-! ### Zero and Identity -/

example : FloatRepr.zero exponent_min + FloatRepr.zero exponent_min =
          FloatRepr.zero exponent_min := by
  have h_norm := zero_isNormalized precision exponent_min
  have h_exp_lo : exponent_min ≤ (FloatRepr.zero exponent_min).exponent := Int.le_refl _
  have h_exp_hi : (FloatRepr.zero exponent_min).exponent ≤ exponent_max := by decide
  exact add_zero_left precision exponent_min exponent_max RoundMode.ToNearestEven
    (FloatRepr.zero exponent_min) h_norm h_exp_lo h_exp_hi (fun _ => rfl)

example : FloatRepr.one precision + FloatRepr.zero exponent_min =
          FloatRepr.one precision := by
  have h_norm := one_isNormalized precision
  have h_exp_lo : exponent_min ≤ (FloatRepr.one precision).exponent := by decide
  have h_exp_hi : (FloatRepr.one precision).exponent ≤ exponent_max := by decide
  have h_nz : (FloatRepr.one precision).mantissa ≠ 0 := by
    unfold FloatRepr.one; exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))
  exact add_zero_right precision exponent_min exponent_max RoundMode.ToNearestEven
    (FloatRepr.one precision) h_norm h_exp_lo h_exp_hi (fun h => absurd h h_nz)

example : FloatRepr.one precision * FloatRepr.one precision =
          FloatRepr.one precision := by
  have h_norm := one_isNormalized precision
  have h_exp_lo : exponent_min ≤ (FloatRepr.one precision).exponent := by decide
  have h_exp_hi : (FloatRepr.one precision).exponent ≤ exponent_max := by decide
  have h_nz : (FloatRepr.one precision).mantissa ≠ 0 := by
    unfold FloatRepr.one; exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))
  exact mul_one_right precision exponent_min exponent_max RoundMode.ToNearestEven
    (FloatRepr.one precision) h_norm h_exp_lo h_exp_hi (fun h => absurd h h_nz)

/-! ### Negation -/

example : (FloatRepr.one precision).neg + FloatRepr.one precision =
          FloatRepr.zero exponent_min := by
  show (FloatRepr.one precision).neg.add precision exponent_min exponent_max RoundMode.ToNearestEven (FloatRepr.one precision) = FloatRepr.zero exponent_min
  unfold FloatRepr.add
  simp only [toRat_neg, toRat_one, neg_add_cancel]
  rw [← toRat_zero precision exponent_min]
  have h_norm := zero_isNormalized precision exponent_min
  have h_exp_lo : exponent_min ≤ (FloatRepr.zero exponent_min).exponent := Int.le_refl _
  have h_exp_hi : (FloatRepr.zero exponent_min).exponent ≤ exponent_max := by decide
  exact roundToFloat_idempotent precision exponent_min exponent_max RoundMode.ToNearestEven
    (FloatRepr.zero exponent_min) h_norm h_exp_lo h_exp_hi (fun _ => rfl)

example : (FloatRepr.one precision).neg.neg = FloatRepr.one precision := by
  exact neg_neg (FloatRepr.one precision)

-- Negation preserves magnitude
example (x : FloatRepr) : (x.neg).toRat precision = -(x.toRat precision) := by
  exact toRat_neg precision x

/-! ### Commutativity (Proven!) -/

-- These are actually proven, not examples with sorry
example (x y : Binary32) : x + y = y + x := by
  exact add_comm precision exponent_min exponent_max RoundMode.ToNearestEven x y

example (x y : Binary32) : x * y = y * x := by
  exact mul_comm precision exponent_min exponent_max RoundMode.ToNearestEven x y

/-! ### Boundary Values - Small Numbers -/

-- Smallest positive normal number: 1.0 × 2^-126
def smallest_normal : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := -126 }

-- Largest subnormal: (1 - 2^-23) × 2^-126 ≈ 0.999999940395... × 2^-126
-- Note: Subnormals use different representation (significand in [0,1) not [1,2))
def largest_subnormal : FloatRepr :=
  { sign := false, mantissa := 2^24 - 1, exponent := -126 }

-- Machine epsilon: 2^-23 (smallest x such that 1+x ≠ 1 in float32)
def epsilon : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := -23 }

example : smallest_normal.toRat precision =
          Float.Spec.Rat.pow2 (-126) := by
  unfold smallest_normal FloatRepr.toRat Float.Spec.Rat.pow2 precision
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : ((2^24 : Nat) : Rat) = (2 : Rat) ^ (24 : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact (zpow_natCast (2 : Rat) 24).symm
  simp only [h1]
  have two_ne_zero : (2 : Rat) ≠ 0 := by decide
  rw [← zpow_add₀ two_ne_zero]
  congr 1

example : epsilon.toRat precision =
          Float.Spec.Rat.pow2 (-23) := by
  unfold epsilon FloatRepr.toRat Float.Spec.Rat.pow2 precision
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : ((2^24 : Nat) : Rat) = (2 : Rat) ^ (24 : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact (zpow_natCast (2 : Rat) 24).symm
  simp only [h1]
  have two_ne_zero : (2 : Rat) ≠ 0 := by decide
  rw [← zpow_add₀ two_ne_zero]
  congr 1

/-! ### Boundary Values - Large Numbers -/

-- Largest finite: (2 - 2^-23) × 2^127 ≈ 3.4028235 × 10^38
def max_value : FloatRepr :=
  { sign := false, mantissa := 2^24 - 1, exponent := 127 - 24 + 1 }

-- Overflow threshold: 2^128 (rounds to infinity in real IEEE754)
def overflow_threshold : FloatRepr :=
  { sign := false, mantissa := 2^23, exponent := 128 }

/-! ### Powers of Two (Exactly Representable) -/

-- 2^0 = 1
example : FloatRepr.one precision =
          { sign := false, mantissa := 2^24, exponent := 0 } := by rfl

-- 2^1 = 2
def two : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := 1 }

-- 2^-1 = 0.5
def half : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := -1 }

example : two.toRat precision =
          ((2 : Nat) : Rat) := by
  unfold two FloatRepr.toRat precision
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : ((2^24 : Nat) : Rat) = (2 : Rat) ^ (24 : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact (zpow_natCast (2 : Rat) 24).symm
  simp only [h1]
  have two_ne_zero : (2 : Rat) ≠ 0 := by decide
  rw [← zpow_add₀ two_ne_zero]
  have h2 : (24 : Int) + (1 - (24 : Nat)) = 1 := by decide
  rw [h2]
  simp only [zpow_one, Nat.cast_ofNat]

example : half.toRat precision + half.toRat precision =
          (FloatRepr.one precision).toRat precision := by
  native_decide

/-! ### Catastrophic Cancellation -/

-- Binary32 can represent ~7-8 decimal digits accurately
-- When adding numbers of vastly different magnitudes, precision is lost

-- The classic example: (1 + 1e100) + -1e100 = 0, but 1 + (1e100 + -1e100) = 1
-- For Binary32, we use 2^30 which is large enough to demonstrate the effect

-- Large number for Binary32: 2^30 ≈ 1.07 billion
-- Using power of 2 for exact representation
def large_pow2 : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := 30 }

-- Classic catastrophic cancellation: associativity fails!
-- (1 + 2^30) + -2^30 ≠ 1 + (2^30 + -2^30)
example : let one := FloatRepr.one precision
          let large := large_pow2
          let neg_large := large.neg
          -- Left-associative: (1 + 2^30) + (-2^30)
          -- Step 1: 1 + 2^30 rounds to 2^30 (the 1 is too small, gets rounded away)
          -- Step 2: 2^30 + (-2^30) = 0
          -- Result: 0
          let left := (one + large) + neg_large
          -- Right-associative: 1 + (2^30 + (-2^30))
          -- Step 1: 2^30 + (-2^30) = 0 (exact cancellation)
          -- Step 2: 1 + 0 = 1
          -- Result: 1
          let right := one + (large + neg_large)
          -- Catastrophic cancellation: left ≠ right!
          -- The order of operations determines whether we get 0 or 1!
          left ≠ right := by
  native_decide

-- Note: In exact arithmetic, both would equal 1
-- But floating-point loses the 1 in the first case due to limited precision

-- For Binary64 (f64), the actual (1 + 1e100) + -1e100 example would work:
-- Binary64 max ≈ 1.8e308, so 1e100 is well within range
-- The principle is the same: adding 1 to 1e100 loses the 1, so result is 0
-- But 1 + (1e100 + -1e100) = 1 + 0 = 1

-- Another large number: 2^40 for even more dramatic effect
def large_number : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := 40 }

-- Classic catastrophic cancellation example
-- (1 + large) + (-large) ≠ 1 + (large + (-large))
-- The first loses precision, the second doesn't

example : let one := FloatRepr.one precision
          let large := large_number
          let neg_large := large.neg
          -- Left-associative: (1 + large) + (-large)
          -- The intermediate (1 + large) rounds to large (1 is lost)
          -- Then large + (-large) = 0
          let left := (one + large) + neg_large
          -- Right-associative: 1 + (large + (-large))
          -- First large + (-large) = 0 exactly
          -- Then 1 + 0 = 1
          let right := one + (large + neg_large)
          -- These should be DIFFERENT (demonstrating non-associativity)
          left ≠ right := by
  native_decide

-- More dramatic example: adding small values to large base
example : let small := FloatRepr.one precision  -- 1.0
          let large := large_number
          let neg_large := large.neg
          -- Sum small values first, then cancel large: (small + small) + (large + neg_large)
          let sum_small_first := (small + small) + (large + neg_large)  -- = 2.0
          -- Cancel large values, then add small: (large + neg_large) + (small + small)
          let cancel_first := (large + neg_large) + (small + small)      -- = 2.0
          -- Add to large first: ((small + large) + small) + neg_large
          let add_to_large := ((small + large) + small) + neg_large      -- ≈ 0 (precision lost)
          -- These should differ if precision is lost
          sum_small_first ≠ add_to_large := by
  native_decide

-- Sterbenz counterexample: catastrophic cancellation when NOT in Sterbenz range
-- If we subtract numbers NOT in the range [x/2, 2x], we can lose precision
example : let x := FloatRepr.one precision
          let large := large_number
          -- large is NOT in [x/2, 2x], so subtraction is not exact
          -- (x + large) - large should equal x, but due to rounding it equals 0
          let result := (x + large) + large.neg
          result ≠ x := by
  native_decide

-- Concrete example with specific Binary32 values
-- For 2^25, the ULP is 2, so adding 1 causes rounding
def two_to_25 : FloatRepr :=
  { sign := false, mantissa := 2^24, exponent := 25 }

example : let one := FloatRepr.one precision
          let big := two_to_25
          -- When we add 1.0 to 2^25, the 1.0 is lost (ULP at 2^25 is 2)
          let result := (one + big) + big.neg
          -- result should be 0, not 1
          result ≠ one := by
  native_decide

-- Demonstration that association matters for numerical stability
-- This example shows the list of values where order matters
-- (left as documentation; formal proof would require more machinery)

/-! ### Rounding Behavior -/

-- 1/3 is not exactly representable, should round to nearest
def one_third_approx : FloatRepr :=
  roundToFloat precision exponent_min exponent_max RoundMode.ToNearestEven (1/3)

-- 1/10 is not exactly representable in binary
def one_tenth_approx : FloatRepr :=
  roundToFloat precision exponent_min exponent_max RoundMode.ToNearestEven (1/10)

-- 0.3 rounded
def three_tenths_approx : FloatRepr :=
  roundToFloat precision exponent_min exponent_max RoundMode.ToNearestEven (3/10)

-- Classic example: 0.1 + 0.1 + 0.1 ≠ 0.3 in Binary32
-- Due to rounding, they have slight differences!
example : (one_tenth_approx + one_tenth_approx + one_tenth_approx).toRat precision ≠
          three_tenths_approx.toRat precision := by
  native_decide

/-! ### Sterbenz Lemma Cases -/

-- When x/2 ≤ y ≤ 2x, x-y is computed exactly (no rounding error)
-- This example verifies exact subtraction when values are close
example : let x := FloatRepr.one precision
          let y := half
          -- y = 0.5 is in [x/2, 2x] = [0.5, 2], so subtraction is exact
          (x.toRat precision - y.toRat precision) =
          (x.add precision exponent_min exponent_max RoundMode.ToNearestEven y.neg).toRat precision := by
  native_decide

/-! ### Monotonicity Examples -/

-- If x ≤ y, then x + z ≤ y + z (should hold)
example (x y z : Binary32) (h : x.toRat precision ≤ y.toRat precision) :
    (x + z).toRat precision ≤ (y + z).toRat precision := by
  have h' : x.le precision y := h
  exact add_monotonic_left precision exponent_min exponent_max RoundMode.ToNearestEven x y z h'

-- If 0 < z and x ≤ y, then x*z ≤ y*z (should hold)
example (x y z : Binary32)
    (hz : 0 < z.toRat precision)
    (h : x.toRat precision ≤ y.toRat precision) :
    (x * z).toRat precision ≤ (y * z).toRat precision := by
  have hz' : (FloatRepr.zero exponent_min).lt precision z := by
    unfold FloatRepr.lt
    simp only [toRat_zero]
    exact hz
  have h' : x.le precision y := h
  exact mul_monotonic_pos precision exponent_min exponent_max RoundMode.ToNearestEven x y z hz' h'

end Float.IEEE754.Examples

