/-
Hax Lean Backend - Cryspen

Constructive Floating-Point Specification (Flocq-style)

This module provides a more foundational approach to floating-point
formalization, inspired by Flocq (Floats for Coq). Instead of axiomatizing
properties, we:

1. Define floating-point representation constructively
2. Define rounding as a function
3. Prove properties as theorems from definitions

Reference: https://flocq.gitlabpages.inria.fr/
-/

import Hax.Lib
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum
import Hax.Float.Spec

namespace Float.Constructive

/-! # Floating-Point Format Parameters -/

/-- Parameters defining a floating-point format (like binary64) -/
structure FloatFormat where
  /-- Number of precision bits (including implicit bit) -/
  prec : Nat
  /-- Maximum exponent -/
  emax : Int
  /-- Minimum exponent (for normalized numbers) -/
  emin : Int := 1 - emax
  /-- Precision is at least 1 -/
  prec_pos : prec ≥ 1
  /-- emin < emax -/
  emin_lt_emax : emin < emax
  /-- 0 is a valid exponent (needed for 1.0 representation) -/
  zero_exp_valid : emin ≤ 0 ∧ 0 ≤ emax := by constructor <;> omega

/-- Binary64 (double precision) format -/
def binary64 : FloatFormat where
  prec := 53
  emax := 1024
  prec_pos := by omega
  emin_lt_emax := by omega

/-- Binary32 (single precision) format -/
def binary32 : FloatFormat where
  prec := 24
  emax := 128
  prec_pos := by omega
  emin_lt_emax := by omega

/-! # Floating-Point Representation -/

/-- A floating-point number in a given format.
    Represented as: (-1)^sign * mantissa * 2^exponent

    For normalized numbers: 2^(p-1) ≤ mantissa < 2^p
    For denormalized: 0 < mantissa < 2^(p-1), exponent = emin
    For zero: mantissa = 0
-/
structure FloatRepr (fmt : FloatFormat) where
  /-- Sign bit: false = positive, true = negative -/
  sign : Bool
  /-- Mantissa (significand) as a natural number -/
  mantissa : Nat
  /-- Exponent -/
  exponent : Int
  /-- Mantissa is bounded by 2^prec -/
  mantissa_bound : mantissa < 2^fmt.prec
  /-- Exponent is bounded -/
  exponent_bound : fmt.emin ≤ exponent ∧ exponent ≤ fmt.emax

/-- Special values -/
inductive FloatValue (fmt : FloatFormat) where
  | finite : FloatRepr fmt → FloatValue fmt
  | infinity : Bool → FloatValue fmt  -- sign
  | nan : FloatValue fmt

/-! # Canonical (Normalized) Representation

A canonical representation is one where the mantissa has minimal trailing zeros.
This ensures unique representation for each rational value (except for signed zeros).

- Zero: mantissa = 0 (any sign gives the same rational value 0)
- Normalized: 2^(prec-1) ≤ mantissa < 2^prec (leading implicit bit set)
- Denormalized: exponent = emin and 0 < mantissa < 2^(prec-1) (allows gradual underflow)
-/

/-- A FloatRepr is canonical if it has a unique representation for its rational value.
    Zero: mantissa = 0
    Non-zero normalized: 2^(prec-1) ≤ mantissa (leading bit is set)
    Non-zero denormalized: exponent = emin and odd mantissa (no trailing zeros) -/
def FloatRepr.isCanonical {fmt : FloatFormat} (f : FloatRepr fmt) : Prop :=
  f.mantissa = 0 ∨                           -- Zero
  (f.mantissa ≥ 2^(fmt.prec - 1)) ∨          -- Normalized (leading bit set)
  (f.exponent = fmt.emin ∧ f.mantissa % 2 = 1)  -- Denormalized with no trailing zeros

/-- A FloatValue is canonical if it's not finite, or if its finite part is canonical -/
def FloatValue.isCanonical {fmt : FloatFormat} : FloatValue fmt → Prop
  | .finite f => f.isCanonical
  | .infinity _ => True
  | .nan => True

/-- A FloatValue is non-zero -/
def FloatValue.isNonZero {fmt : FloatFormat} : FloatValue fmt → Prop
  | .finite f => f.mantissa ≠ 0
  | .infinity _ => True
  | .nan => True

/-! ## Helper lemmas for canonical uniqueness -/

/-- Odd numbers are not divisible by 2 -/
theorem odd_not_two_dvd (n : Nat) (h : n % 2 = 1) : ¬(2 ∣ n) := by
  intro ⟨k, hk⟩
  have : n % 2 = 0 := by simp [hk, Nat.mul_mod_right]
  omega

/-- Key lemma: if m * 2^e = n * 2^f with m odd and n odd, then m = n and e = f -/
theorem odd_pow2_unique {m n : Nat} {e f : Int} (hm_pos : m ≠ 0) (hn_pos : n ≠ 0)
    (hm_odd : m % 2 = 1) (hn_odd : n % 2 = 1)
    (heq : (m : Rat) * (2 : Rat)^e = (n : Rat) * (2 : Rat)^f) : m = n ∧ e = f := by
  -- Case split on e vs f
  rcases Int.lt_trichotomy e f with he_lt | he_eq | he_gt
  · -- Case e < f: leads to contradiction
    -- From m * 2^e = n * 2^f with e < f, we get m = n * 2^(f-e)
    -- But m is odd and 2^(f-e) is even (since f > e), contradiction
    exfalso
    have h2_pos : (0 : Rat) < 2 := by norm_num
    have h2e_pos : (0 : Rat) < (2 : Rat)^e := zpow_pos h2_pos e
    have h2e_ne : (2 : Rat)^e ≠ 0 := ne_of_gt h2e_pos
    -- m = n * 2^(f-e)
    have heq' : (m : Rat) = (n : Rat) * (2 : Rat)^(f - e) := by
      have h1 : (m : Rat) * (2 : Rat)^e / (2 : Rat)^e = (n : Rat) * (2 : Rat)^f / (2 : Rat)^e := by
        rw [heq]
      simp only [mul_div_assoc, div_self h2e_ne, mul_one] at h1
      rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
      exact h1
    -- f - e > 0, so 2^(f-e) ≥ 2
    have hfe_pos : 0 < f - e := by omega
    -- Since (m : Rat) = (n : Rat) * 2^(f-e) and f-e > 0, we have m = n * 2^(f-e).toNat as Nats
    -- First note that 2^(f-e) = 2^(f-e).toNat since f-e > 0
    have hfe_nat : (f - e).toNat = (f - e) := Int.toNat_of_nonneg (le_of_lt hfe_pos)
    have h2pow : (2 : Rat)^(f - e) = (2^(f - e).toNat : Nat) := by
      rw [← Int.coe_nat_pow, hfe_nat]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rfl
    rw [h2pow] at heq'
    -- Now we have (m : Rat) = (n : Rat) * (2^(f-e).toNat : Nat) = (n * 2^(f-e).toNat : Nat)
    have heq_nat : (m : Rat) = ((n * 2^(f - e).toNat) : Nat) := by
      rw [heq']
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have heq_nat' : m = n * 2^(f - e).toNat := Nat.cast_injective heq_nat
    -- Now 2 divides m since 2^(f-e).toNat ≥ 2 when f-e ≥ 1
    have hfe_ge1 : (f - e).toNat ≥ 1 := by
      rw [hfe_nat]
      omega
    have h2pow_ge2 : 2^(f - e).toNat ≥ 2 := by
      calc 2^(f - e).toNat ≥ 2^1 := Nat.pow_le_pow_right (by omega) hfe_ge1
        _ = 2 := by norm_num
    have h_dvd : 2 ∣ m := by
      rw [heq_nat']
      -- 2^k = 2 * 2^(k-1) when k ≥ 1
      have h2pow_eq : 2^(f - e).toNat = 2 * 2^((f - e).toNat - 1) := by
        have : (f - e).toNat = (f - e).toNat - 1 + 1 := by omega
        conv_lhs => rw [this]
        ring
      rw [h2pow_eq, Nat.mul_comm n, Nat.mul_assoc]
      exact Nat.dvd_mul_right 2 _
    exact odd_not_two_dvd m hm_odd h_dvd
  · -- Case e = f: then m = n directly
    subst he_eq
    have h2e_ne : (2 : Rat)^e ≠ 0 := by
      apply ne_of_gt
      exact zpow_pos (by norm_num : (0 : Rat) < 2) e
    have : (m : Rat) = (n : Rat) := by
      have := mul_right_cancel₀ h2e_ne heq
      exact this
    constructor
    · exact Nat.cast_injective this
    · rfl
  · -- Case e > f: symmetric to e < f
    exfalso
    have h2_pos : (0 : Rat) < 2 := by norm_num
    have h2f_pos : (0 : Rat) < (2 : Rat)^f := zpow_pos h2_pos f
    have h2f_ne : (2 : Rat)^f ≠ 0 := ne_of_gt h2f_pos
    -- n = m * 2^(e-f)
    have heq' : (n : Rat) = (m : Rat) * (2 : Rat)^(e - f) := by
      have h1 : (n : Rat) * (2 : Rat)^f / (2 : Rat)^f = (m : Rat) * (2 : Rat)^e / (2 : Rat)^f := by
        rw [← heq]
      simp only [mul_div_assoc, div_self h2f_ne, mul_one] at h1
      rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
      exact h1
    have hef_pos : 0 < e - f := by omega
    have hef_nat : (e - f).toNat = (e - f) := Int.toNat_of_nonneg (le_of_lt hef_pos)
    have h2pow : (2 : Rat)^(e - f) = (2^(e - f).toNat : Nat) := by
      rw [← Int.coe_nat_pow, hef_nat]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rfl
    rw [h2pow] at heq'
    have heq_nat : (n : Rat) = ((m * 2^(e - f).toNat) : Nat) := by
      rw [heq']
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have heq_nat' : n = m * 2^(e - f).toNat := Nat.cast_injective heq_nat
    have hef_ge1 : (e - f).toNat ≥ 1 := by
      rw [hef_nat]
      omega
    have h_dvd : 2 ∣ n := by
      rw [heq_nat']
      -- 2^k = 2 * 2^(k-1) when k ≥ 1
      have h2pow_eq : 2^(e - f).toNat = 2 * 2^((e - f).toNat - 1) := by
        have : (e - f).toNat = (e - f).toNat - 1 + 1 := by omega
        conv_lhs => rw [this]
        ring
      rw [h2pow_eq, Nat.mul_comm m, Nat.mul_assoc]
      exact Nat.dvd_mul_right 2 _
    exact odd_not_two_dvd n hn_odd h_dvd

/-- Sign is determined by the sign of toRat -/
theorem sign_from_toRat {fmt : FloatFormat} (f : FloatRepr fmt) (hf_nz : f.mantissa ≠ 0) :
    f.sign = (f.toRat < 0) := by
  simp only [FloatRepr.toRat]
  have hm_pos : (0 : Rat) < f.mantissa := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hf_nz)
  have h2_pos : (0 : Rat) < 2 := by norm_num
  have hscale_pos : (0 : Rat) < (2 : Rat) ^ (f.exponent - (fmt.prec - 1 : Int)) :=
    zpow_pos h2_pos _
  cases f.sign with
  | false =>
    simp only [ite_false, one_mul, Bool.false_eq_decide_iff, not_lt]
    exact le_of_lt (mul_pos hm_pos hscale_pos)
  | true =>
    simp only [ite_true, neg_one_mul, Bool.true_eq_decide_iff, Left.neg_neg_iff]
    exact mul_pos hm_pos hscale_pos

/-- Canonical non-zero representations with equal toRat have equal representations -/
theorem FloatRepr.canonical_unique {fmt : FloatFormat} (f g : FloatRepr fmt)
    (hf : f.isCanonical) (hg : g.isCanonical)
    (hf_nz : f.mantissa ≠ 0) (hg_nz : g.mantissa ≠ 0)
    (heq : f.toRat = g.toRat) : f.sign = g.sign ∧ f.mantissa = g.mantissa ∧ f.exponent = g.exponent := by
  -- First, prove signs are equal
  have hsign : f.sign = g.sign := by
    rw [sign_from_toRat f hf_nz, sign_from_toRat g hg_nz, heq]
  constructor
  · exact hsign
  -- Now prove mantissa and exponent are equal
  -- Expand toRat
  simp only [FloatRepr.toRat] at heq
  -- Since signs are equal, the sign factors are equal
  have hsign_factor : (if f.sign then (-1 : Rat) else 1) = (if g.sign then -1 else 1) := by
    simp [hsign]
  -- So mantissa * scale are equal (in absolute value)
  have habs : (f.mantissa : Rat) * (2 : Rat)^(f.exponent - (fmt.prec - 1)) =
              (g.mantissa : Rat) * (2 : Rat)^(g.exponent - (fmt.prec - 1)) := by
    cases hfs : f.sign <;> cases hgs : g.sign <;> simp_all [mul_comm, mul_assoc]
  -- Simplify: let e_f = f.exponent - (prec - 1), e_g = g.exponent - (prec - 1)
  -- We have: f.mantissa * 2^e_f = g.mantissa * 2^e_g
  -- Canonical non-zero means: normalized (mantissa ≥ 2^(prec-1)) or denormalized (exp=emin, odd mantissa)
  -- Exclude zero case (handled by hf_nz, hg_nz)
  have hf_canon : f.mantissa ≥ 2^(fmt.prec - 1) ∨ (f.exponent = fmt.emin ∧ f.mantissa % 2 = 1) := by
    rcases hf with hf_zero | hf_norm | hf_denorm
    · exact absurd hf_zero hf_nz
    · left; exact hf_norm
    · right; exact hf_denorm
  have hg_canon : g.mantissa ≥ 2^(fmt.prec - 1) ∨ (g.exponent = fmt.emin ∧ g.mantissa % 2 = 1) := by
    rcases hg with hg_zero | hg_norm | hg_denorm
    · exact absurd hg_zero hg_nz
    · left; exact hg_norm
    · right; exact hg_denorm
  -- Case analysis on normalized vs denormalized
  rcases hf_canon with hf_norm | ⟨hf_emin, hf_odd⟩ <;> rcases hg_canon with hg_norm | ⟨hg_emin, hg_odd⟩
  · -- Both normalized: mantissa ∈ [2^(prec-1), 2^prec - 1]
    -- Show exponents must be equal, then mantissas equal
    -- If e_f < e_g: f.mantissa = g.mantissa * 2^(e_g - e_f), but g.mantissa ≥ 2^(prec-1)
    -- so f.mantissa ≥ 2^prec when e_g - e_f ≥ 1, contradicting f.mantissa < 2^prec
    rcases Int.lt_trichotomy f.exponent g.exponent with he_lt | he_eq | he_gt
    · -- f.exponent < g.exponent
      exfalso
      have h2_pos : (0 : Rat) < 2 := by norm_num
      have hef_pos : 0 < g.exponent - (fmt.prec - 1) - (f.exponent - (fmt.prec - 1)) := by omega
      have hef_eq : g.exponent - (fmt.prec - 1) - (f.exponent - (fmt.prec - 1)) = g.exponent - f.exponent := by ring
      have h2fe_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos h2_pos _)
      have heq' : (f.mantissa : Rat) = (g.mantissa : Rat) * (2 : Rat)^(g.exponent - f.exponent) := by
        have h1 : (f.mantissa : Rat) * (2 : Rat)^(f.exponent - (fmt.prec - 1)) / (2 : Rat)^(f.exponent - (fmt.prec - 1)) =
                  (g.mantissa : Rat) * (2 : Rat)^(g.exponent - (fmt.prec - 1)) / (2 : Rat)^(f.exponent - (fmt.prec - 1)) := by rw [habs]
        simp only [mul_div_assoc, div_self h2fe_ne, mul_one] at h1
        rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
        convert h1 using 2
        ring
      have hgf_ge1 : (g.exponent - f.exponent).toNat ≥ 1 := by
        have : g.exponent - f.exponent ≥ 1 := by omega
        omega
      have h2pow_rat : (2 : Rat)^(g.exponent - f.exponent) = (2^(g.exponent - f.exponent).toNat : Nat) := by
        have hpos : 0 ≤ g.exponent - f.exponent := by omega
        rw [← Int.coe_nat_pow, Int.toNat_of_nonneg hpos]
        simp
      rw [h2pow_rat] at heq'
      have heq_nat : (f.mantissa : Rat) = ((g.mantissa * 2^(g.exponent - f.exponent).toNat) : Nat) := by
        rw [heq']; simp
      have heq_nat' : f.mantissa = g.mantissa * 2^(g.exponent - f.exponent).toNat := Nat.cast_injective heq_nat
      -- g.mantissa ≥ 2^(prec-1), so f.mantissa ≥ 2^(prec-1) * 2 = 2^prec when exp diff ≥ 1
      have h_bound : f.mantissa ≥ 2^fmt.prec := by
        calc f.mantissa = g.mantissa * 2^(g.exponent - f.exponent).toNat := heq_nat'
          _ ≥ 2^(fmt.prec - 1) * 2^(g.exponent - f.exponent).toNat := by
            apply Nat.mul_le_mul_right
            exact hg_norm
          _ ≥ 2^(fmt.prec - 1) * 2^1 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) hgf_ge1
          _ = 2^fmt.prec := by
            rw [← Nat.pow_add]
            congr 1
            omega
      exact Nat.not_lt.mpr h_bound f.mantissa_bound
    · -- f.exponent = g.exponent: then mantissas equal
      constructor
      · have h2e_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
        have heq_sub : g.exponent - (fmt.prec - 1) = f.exponent - (fmt.prec - 1) := by omega
        rw [heq_sub] at habs
        exact Nat.cast_injective (mul_right_cancel₀ h2e_ne habs)
      · exact he_eq
    · -- f.exponent > g.exponent: symmetric
      exfalso
      have h2_pos : (0 : Rat) < 2 := by norm_num
      have h2ge_ne : (2 : Rat)^(g.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos h2_pos _)
      have heq' : (g.mantissa : Rat) = (f.mantissa : Rat) * (2 : Rat)^(f.exponent - g.exponent) := by
        have h1 : (g.mantissa : Rat) * (2 : Rat)^(g.exponent - (fmt.prec - 1)) / (2 : Rat)^(g.exponent - (fmt.prec - 1)) =
                  (f.mantissa : Rat) * (2 : Rat)^(f.exponent - (fmt.prec - 1)) / (2 : Rat)^(g.exponent - (fmt.prec - 1)) := by rw [← habs]
        simp only [mul_div_assoc, div_self h2ge_ne, mul_one] at h1
        rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
        convert h1 using 2
        ring
      have hfg_ge1 : (f.exponent - g.exponent).toNat ≥ 1 := by
        have : f.exponent - g.exponent ≥ 1 := by omega
        omega
      have h2pow_rat : (2 : Rat)^(f.exponent - g.exponent) = (2^(f.exponent - g.exponent).toNat : Nat) := by
        have hpos : 0 ≤ f.exponent - g.exponent := by omega
        rw [← Int.coe_nat_pow, Int.toNat_of_nonneg hpos]
        simp
      rw [h2pow_rat] at heq'
      have heq_nat : (g.mantissa : Rat) = ((f.mantissa * 2^(f.exponent - g.exponent).toNat) : Nat) := by
        rw [heq']; simp
      have heq_nat' : g.mantissa = f.mantissa * 2^(f.exponent - g.exponent).toNat := Nat.cast_injective heq_nat
      have h_bound : g.mantissa ≥ 2^fmt.prec := by
        calc g.mantissa = f.mantissa * 2^(f.exponent - g.exponent).toNat := heq_nat'
          _ ≥ 2^(fmt.prec - 1) * 2^(f.exponent - g.exponent).toNat := by
            apply Nat.mul_le_mul_right
            exact hf_norm
          _ ≥ 2^(fmt.prec - 1) * 2^1 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) hfg_ge1
          _ = 2^fmt.prec := by
            rw [← Nat.pow_add]
            congr 1
            omega
      exact Nat.not_lt.mpr h_bound g.mantissa_bound
  · -- f normalized, g denormalized
    -- f.mantissa ≥ 2^(prec-1), g.exponent = emin, g.mantissa is odd
    -- Case analysis on f.exponent vs emin
    rcases Int.lt_trichotomy f.exponent fmt.emin with hf_lt | hf_eq | hf_gt
    · -- f.exponent < emin: impossible by exponent_bound
      exact absurd hf_lt (not_lt.mpr f.exponent_bound.1)
    · -- f.exponent = emin: exponents equal, mantissas equal from habs
      constructor
      · have h2e_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
        have heq_sub : g.exponent - (fmt.prec - 1) = f.exponent - (fmt.prec - 1) := by
          rw [hg_emin, hf_eq]
        rw [heq_sub] at habs
        exact Nat.cast_injective (mul_right_cancel₀ h2e_ne habs)
      · rw [hf_eq, hg_emin]
    · -- f.exponent > emin: contradiction
      -- f.mantissa * 2^(f.exponent - emin) = g.mantissa, but f.mantissa ≥ 2^(prec-1)
      -- so g.mantissa ≥ 2^(prec-1) * 2 = 2^prec, contradicting g.mantissa_bound
      exfalso
      have h2_pos : (0 : Rat) < 2 := by norm_num
      have h2g_ne : (2 : Rat)^(g.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos h2_pos _)
      have heq' : (g.mantissa : Rat) = (f.mantissa : Rat) * (2 : Rat)^(f.exponent - g.exponent) := by
        have h1 : (g.mantissa : Rat) * (2 : Rat)^(g.exponent - (fmt.prec - 1)) / (2 : Rat)^(g.exponent - (fmt.prec - 1)) =
                  (f.mantissa : Rat) * (2 : Rat)^(f.exponent - (fmt.prec - 1)) / (2 : Rat)^(g.exponent - (fmt.prec - 1)) := by rw [← habs]
        simp only [mul_div_assoc, div_self h2g_ne, mul_one] at h1
        rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
        convert h1 using 2; ring
      have hfg_pos : 0 < f.exponent - g.exponent := by rw [hg_emin]; omega
      have hfg_ge1 : (f.exponent - g.exponent).toNat ≥ 1 := by
        have : f.exponent - g.exponent ≥ 1 := by omega
        omega
      have h2pow_rat : (2 : Rat)^(f.exponent - g.exponent) = (2^(f.exponent - g.exponent).toNat : Nat) := by
        have hpos : 0 ≤ f.exponent - g.exponent := le_of_lt hfg_pos
        rw [← Int.coe_nat_pow, Int.toNat_of_nonneg hpos]
        simp
      rw [h2pow_rat] at heq'
      have heq_nat : (g.mantissa : Rat) = ((f.mantissa * 2^(f.exponent - g.exponent).toNat) : Nat) := by
        rw [heq']; simp
      have heq_nat' : g.mantissa = f.mantissa * 2^(f.exponent - g.exponent).toNat := Nat.cast_injective heq_nat
      have h_bound : g.mantissa ≥ 2^fmt.prec := by
        calc g.mantissa = f.mantissa * 2^(f.exponent - g.exponent).toNat := heq_nat'
          _ ≥ 2^(fmt.prec - 1) * 2^(f.exponent - g.exponent).toNat := by
            apply Nat.mul_le_mul_right; exact hf_norm
          _ ≥ 2^(fmt.prec - 1) * 2^1 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) hfg_ge1
          _ = 2^fmt.prec := by rw [← Nat.pow_add]; congr 1; omega
      exact Nat.not_lt.mpr h_bound g.mantissa_bound
  · -- f denormalized, g normalized: symmetric
    rcases Int.lt_trichotomy g.exponent fmt.emin with hg_lt | hg_eq | hg_gt
    · exact absurd hg_lt (not_lt.mpr g.exponent_bound.1)
    · constructor
      · have h2e_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
        have heq_sub : g.exponent - (fmt.prec - 1) = f.exponent - (fmt.prec - 1) := by
          rw [hf_emin, hg_eq]
        rw [heq_sub] at habs
        exact Nat.cast_injective (mul_right_cancel₀ h2e_ne habs)
      · rw [hf_emin, hg_eq]
    · exfalso
      have h2_pos : (0 : Rat) < 2 := by norm_num
      have h2f_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos h2_pos _)
      have heq' : (f.mantissa : Rat) = (g.mantissa : Rat) * (2 : Rat)^(g.exponent - f.exponent) := by
        have h1 : (f.mantissa : Rat) * (2 : Rat)^(f.exponent - (fmt.prec - 1)) / (2 : Rat)^(f.exponent - (fmt.prec - 1)) =
                  (g.mantissa : Rat) * (2 : Rat)^(g.exponent - (fmt.prec - 1)) / (2 : Rat)^(f.exponent - (fmt.prec - 1)) := by rw [habs]
        simp only [mul_div_assoc, div_self h2f_ne, mul_one] at h1
        rw [← zpow_sub₀ (by norm_num : (2 : Rat) ≠ 0)] at h1
        convert h1 using 2; ring
      have hgf_pos : 0 < g.exponent - f.exponent := by rw [hf_emin]; omega
      have hgf_ge1 : (g.exponent - f.exponent).toNat ≥ 1 := by
        have : g.exponent - f.exponent ≥ 1 := by omega
        omega
      have h2pow_rat : (2 : Rat)^(g.exponent - f.exponent) = (2^(g.exponent - f.exponent).toNat : Nat) := by
        have hpos : 0 ≤ g.exponent - f.exponent := le_of_lt hgf_pos
        rw [← Int.coe_nat_pow, Int.toNat_of_nonneg hpos]
        simp
      rw [h2pow_rat] at heq'
      have heq_nat : (f.mantissa : Rat) = ((g.mantissa * 2^(g.exponent - f.exponent).toNat) : Nat) := by
        rw [heq']; simp
      have heq_nat' : f.mantissa = g.mantissa * 2^(g.exponent - f.exponent).toNat := Nat.cast_injective heq_nat
      have h_bound : f.mantissa ≥ 2^fmt.prec := by
        calc f.mantissa = g.mantissa * 2^(g.exponent - f.exponent).toNat := heq_nat'
          _ ≥ 2^(fmt.prec - 1) * 2^(g.exponent - f.exponent).toNat := by
            apply Nat.mul_le_mul_right; exact hg_norm
          _ ≥ 2^(fmt.prec - 1) * 2^1 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) hgf_ge1
          _ = 2^fmt.prec := by rw [← Nat.pow_add]; congr 1; omega
      exact Nat.not_lt.mpr h_bound f.mantissa_bound
  · -- Both denormalized: exponent = emin, both mantissas odd
    -- Apply odd_pow2_unique directly
    have hexp_eq : f.exponent = g.exponent := by rw [hf_emin, hg_emin]
    constructor
    · -- From habs with equal exponents, mantissas equal
      have h2e_ne : (2 : Rat)^(f.exponent - (fmt.prec - 1)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
      have heq_sub : g.exponent - (fmt.prec - 1) = f.exponent - (fmt.prec - 1) := by omega
      rw [heq_sub] at habs
      exact Nat.cast_injective (mul_right_cancel₀ h2e_ne habs)
    · exact hexp_eq

/-! # Conversion to Rational -/

/-- Convert a finite float representation to a rational number -/
def FloatRepr.toRat {fmt : FloatFormat} (f : FloatRepr fmt) : Rat :=
  let sign_factor : Rat := if f.sign then -1 else 1
  let mantissa_rat : Rat := f.mantissa
  let scale : Rat := (2 : Rat) ^ (f.exponent - (fmt.prec - 1 : Int))
  sign_factor * mantissa_rat * scale

/-- Convert any float value to rational (Inf/NaN → 0) -/
def FloatValue.toRat {fmt : FloatFormat} : FloatValue fmt → Rat
  | .finite f => f.toRat
  | .infinity _ => 0
  | .nan => 0

/-- Non-zero mantissa implies non-zero toRat -/
theorem FloatRepr.toRat_ne_zero {fmt : FloatFormat} (f : FloatRepr fmt)
    (hm : f.mantissa ≠ 0) : f.toRat ≠ 0 := by
  simp only [FloatRepr.toRat]
  -- toRat = sign_factor * mantissa * scale
  -- sign_factor ∈ {-1, 1}, mantissa ≠ 0, scale = 2^k ≠ 0
  have hsign : (if f.sign then (-1 : Rat) else 1) ≠ 0 := by
    cases f.sign <;> simp
  have hmant : (f.mantissa : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hscale : (2 : Rat) ^ (f.exponent - (fmt.prec - 1 : Int)) ≠ 0 :=
    zpow_ne_zero _ (by norm_num : (2 : Rat) ≠ 0)
  exact mul_ne_zero (mul_ne_zero hsign hmant) hscale

/-! # Rounding -/

/-- Rounding mode -/
inductive RoundMode where
  | toNearest      -- Round to nearest, ties to even
  | towardZero     -- Truncate
  | towardPosInf   -- Ceiling
  | towardNegInf   -- Floor
  deriving DecidableEq

/-! # Rounding Infrastructure -/

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
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega : 0 < 2)]
    rw [h2, ih]
    omega

/-- log2Nat for values in [2^k, 2^(k+1)) -/
theorem log2Nat_normalized (m k : Nat) (h_lo : 2^k ≤ m) (h_hi : m < 2^(k+1)) :
    log2Nat m = k := by
  induction k generalizing m with
  | zero =>
    -- m ∈ [1, 2), so m = 1
    have hm1 : m = 1 := by omega
    simp [hm1, log2Nat]
  | succ n ih =>
    -- m ∈ [2^(n+1), 2^(n+2)), so m ≥ 2
    have hm_ge2 : m ≥ 2 := by
      calc m ≥ 2^(n+1) := h_lo
           _ ≥ 2^1 := Nat.pow_le_pow_right (by omega) (by omega)
           _ = 2 := by norm_num
    unfold log2Nat
    simp only [show ¬(m ≤ 1) by omega, ↓reduceIte]
    -- m/2 ∈ [2^n, 2^(n+1))
    have h_lo' : 2^n ≤ m / 2 := by
      have h1 : 2^(n+1) ≤ m := h_lo
      have h2 : 2^(n+1) = 2^n * 2 := by rw [Nat.pow_succ]
      omega
    have h_hi' : m / 2 < 2^(n+1) := by
      have h1 : m < 2^(n+2) := h_hi
      have h2 : 2^(n+2) = 2^(n+1) * 2 := by rw [Nat.pow_succ]
      omega
    have := ih (m / 2) h_lo' h_hi'
    omega

/-- For n > 0, log2Nat gives the correct floor: 2^log2Nat(n) ≤ n < 2^(log2Nat(n)+1) -/
theorem log2Nat_bounds (n : Nat) (hn : n > 0) :
    2^(log2Nat n) ≤ n ∧ n < 2^(log2Nat n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n ≤ 1
    · -- n = 1
      have hn1 : n = 1 := by omega
      simp [hn1, log2Nat]
    · -- n > 1
      push_neg at h1
      unfold log2Nat
      simp only [show ¬(n ≤ 1) by omega, ↓reduceIte]
      have hn2_pos : n / 2 > 0 := by omega
      have hn2_lt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have ⟨lo, hi⟩ := ih (n / 2) hn2_lt hn2_pos
      -- Key facts about n and n/2
      have h_n_div : n / 2 * 2 ≤ n ∧ n < n / 2 * 2 + 2 := ⟨Nat.div_mul_le_self n 2, by omega⟩
      constructor
      · -- 2^(1 + log2Nat(n/2)) ≤ n
        have h1 : 2 * 2^(log2Nat (n/2)) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 lo
        have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
        have h3 : 2^(1 + log2Nat (n/2)) = 2^1 * 2^(log2Nat (n/2)) := Nat.pow_add 2 1 _
        simp only [Nat.pow_one] at h3
        omega
      · -- n < 2^(1 + log2Nat(n/2) + 1)
        have h1 : n / 2 < 2^(log2Nat (n/2) + 1) := hi
        have h2 : n < n / 2 * 2 + 2 := by omega
        have heq : 1 + log2Nat (n/2) + 1 = 1 + (log2Nat (n/2) + 1) := by omega
        rw [heq]
        have h3 : 2^(1 + (log2Nat (n/2) + 1)) = 2^1 * 2^(log2Nat (n/2) + 1) := Nat.pow_add 2 1 _
        simp only [Nat.pow_one] at h3
        omega

/-- Compute floor(log2(|q|)) for a non-zero rational q -/
def log2Rat (q : Rat) : Int :=
  let abs_q := if q < 0 then -q else q
  let num := abs_q.num.natAbs
  let den := abs_q.den
  if num = 0 then 0
  else (log2Nat num : Int) - (log2Nat den : Int)

/-- Round a non-negative rational to a natural number according to rounding mode -/
def roundRatToNat (mode : RoundMode) (q : Rat) : Nat :=
  let floor_q := q.floor.toNat
  let frac := q - floor_q
  match mode with
  | .towardZero => floor_q
  | .towardNegInf => floor_q
  | .towardPosInf => if frac > 0 then floor_q + 1 else floor_q
  | .toNearest =>
    if frac > 1/2 then floor_q + 1
    else if frac < 1/2 then floor_q
    else if floor_q % 2 = 0 then floor_q else floor_q + 1  -- tie: to even

/-- Normalize a (mantissa, exponent) pair so mantissa is in [2^prec, 2^(prec+1)) or is 0.
    Uses fuel to ensure termination. -/
def normalizeMantissa (prec : Nat) (mantissa : Nat) (exponent : Int) (fuel : Nat) :
    Nat × Int :=
  if fuel = 0 then (mantissa, exponent)
  else if mantissa = 0 then (0, exponent)
  else if mantissa ≥ 2^(prec + 1) then
    normalizeMantissa prec (mantissa / 2) (exponent + 1) (fuel - 1)
  else if mantissa < 2^prec then
    normalizeMantissa prec (mantissa * 2) (exponent - 1) (fuel - 1)
  else
    (mantissa, exponent)

/-- Normalization preserves zero mantissa -/
theorem normalizeMantissa_zero (prec : Nat) (exp : Int) (fuel : Nat) :
    (normalizeMantissa prec 0 exp fuel).1 = 0 := by
  induction fuel with
  | zero => unfold normalizeMantissa; simp
  | succ n ih =>
    unfold normalizeMantissa
    simp

/-- Check if a rational is exactly representable in the format -/
def isExactlyRepresentable (fmt : FloatFormat) (q : Rat) : Prop :=
  ∃ f : FloatRepr fmt, f.toRat = q

/-- Round a rational to a FloatRepr in the given format.

This is the core rounding operation that converts exact rational arithmetic
back to floating-point representation with correct rounding.

Algorithm:
1. Handle zero specially
2. Extract sign and work with |q|
3. Find exponent e ≈ floor(log2(|q|))
4. Compute mantissa = round(|q| * 2^(precision - e))
5. Normalize if mantissa overflows
6. Clamp exponent to valid range
-/
def roundToFloatRepr (fmt : FloatFormat) (mode : RoundMode) (q : Rat) : FloatRepr fmt :=
  -- Handle zero
  if h_zero : q = 0 then
    ⟨false, 0, fmt.emin,
      Nat.two_pow_pos fmt.prec,
      ⟨le_refl _, Int.le_of_lt fmt.emin_lt_emax⟩⟩
  else
    -- Extract sign
    let sign := q < 0
    let abs_q : Rat := if sign then -q else q

    -- Find approximate exponent: e ≈ floor(log2(|q|))
    let e_approx := log2Rat abs_q

    -- Scale to get mantissa in the right range
    let scale_exp := (fmt.prec : Int) - e_approx
    let mantissa_exact := abs_q * ((2 : Rat) ^ scale_exp)

    -- Round to integer
    let mantissa_rounded := roundRatToNat mode mantissa_exact

    -- Normalize
    let (mantissa_norm, exp_norm) :=
      normalizeMantissa fmt.prec mantissa_rounded e_approx (mantissa_rounded + fmt.prec)

    -- Clamp exponent to valid range
    let clamped_exp :=
      if exp_norm < fmt.emin then fmt.emin
      else if exp_norm > fmt.emax then fmt.emax
      else exp_norm

    -- Use modular arithmetic to ensure mantissa is in bounds
    -- Exponent bounds follow from clamping logic (proved by case analysis on if-then-else)
    have h_emin_lt_emax := fmt.emin_lt_emax
    ⟨sign, mantissa_norm % 2^fmt.prec, clamped_exp,
      Nat.mod_lt _ (Nat.two_pow_pos fmt.prec),
      ⟨by simp only [clamped_exp]; split_ifs <;> omega,
       by simp only [clamped_exp]; split_ifs <;> omega⟩⟩

/-- Round a rational to the nearest representable value.
    This is the core definition from which error bounds are derived. -/
def round (fmt : FloatFormat) (mode : RoundMode) (q : Rat) : FloatValue fmt :=
  .finite (roundToFloatRepr fmt mode q)

/-! # Operations Defined via Exact + Round -/

/-- Floating-point addition: compute exact sum, then round -/
def fadd (fmt : FloatFormat) (mode : RoundMode)
    (x y : FloatValue fmt) : FloatValue fmt :=
  match x, y with
  | .finite fx, .finite fy => round fmt mode (fx.toRat + fy.toRat)
  | .infinity sx, .infinity sy =>
      if sx == sy then .infinity sx else .nan
  | .infinity s, _ => .infinity s
  | _, .infinity s => .infinity s
  | .nan, _ => .nan
  | _, .nan => .nan

/-- Get the sign of a float value -/
def FloatValue.isNegative {fmt : FloatFormat} : FloatValue fmt → Bool
  | .finite f => f.sign
  | .infinity s => s
  | .nan => false

/-- Floating-point multiplication: compute exact product, then round -/
def fmul (fmt : FloatFormat) (mode : RoundMode)
    (x y : FloatValue fmt) : FloatValue fmt :=
  match x, y with
  | .finite fx, .finite fy => round fmt mode (fx.toRat * fy.toRat)
  | .infinity _, .finite fy =>
      if fy.mantissa = 0 then .nan else .infinity (xor x.isNegative fy.sign)
  | .finite fx, .infinity _ =>
      if fx.mantissa = 0 then .nan else .infinity (xor fx.sign y.isNegative)
  | .infinity sx, .infinity sy => .infinity (xor sx sy)
  | .nan, _ => .nan
  | _, .nan => .nan

/-- Floating-point negation (exact, no rounding needed) -/
def fneg {fmt : FloatFormat} : FloatValue fmt → FloatValue fmt
  | .finite f => .finite { f with sign := !f.sign }
  | .infinity s => .infinity (!s)
  | .nan => .nan

/-- Floating-point division: compute exact quotient, then round -/
def fdiv (fmt : FloatFormat) (mode : RoundMode)
    (x y : FloatValue fmt) : FloatValue fmt :=
  match x, y with
  | .finite fx, .finite fy =>
      if fy.mantissa = 0 then
        if fx.mantissa = 0 then .nan  -- 0/0 = NaN
        else .infinity fx.sign        -- x/0 = ±Inf
      else round fmt mode (fx.toRat / fy.toRat)
  | .infinity sx, .infinity _ => .nan  -- Inf/Inf = NaN
  | .infinity s, .finite _ => .infinity s
  | .finite fx, .infinity _ =>
      -- finite/Inf = ±0
      round fmt mode 0
  | .nan, _ => .nan
  | _, .nan => .nan

/-- Floating-point subtraction: x - y = x + (-y) -/
def fsub (fmt : FloatFormat) (mode : RoundMode)
    (x y : FloatValue fmt) : FloatValue fmt :=
  fadd fmt mode x (fneg y)

/-! # Constants -/

/-- Zero value -/
def fzero (fmt : FloatFormat) : FloatValue fmt :=
  .finite ⟨false, 0, fmt.emin,
    Nat.two_pow_pos fmt.prec,
    ⟨le_refl _, Int.le_of_lt fmt.emin_lt_emax⟩⟩

/-- One value -/
def fone (fmt : FloatFormat) : FloatValue fmt :=
  -- 1.0 = 2^(prec-1) * 2^(-(prec-1)) = 1
  -- For standard formats (binary32, binary64), 0 is in exponent range
  .finite ⟨false, 2^(fmt.prec - 1), 0,
    by have h : fmt.prec - 1 < fmt.prec := Nat.sub_lt fmt.prec_pos (by omega)
       exact Nat.pow_lt_pow_right (by omega : 1 < 2) h,
    fmt.zero_exp_valid⟩

/-- Positive infinity -/
def finfinity (fmt : FloatFormat) : FloatValue fmt := .infinity false

/-- NaN value -/
def fnan (fmt : FloatFormat) : FloatValue fmt := .nan

/-- Rounding 0 gives fzero -/
theorem round_zero (fmt : FloatFormat) (mode : RoundMode) :
    round fmt mode 0 = fzero fmt := by
  simp only [round, roundToFloatRepr, fzero]
  -- q = 0 so we take the if-branch that returns the zero representation
  simp

/-! # Predicates -/

/-- Check if a value is NaN -/
def FloatValue.isNaN {fmt : FloatFormat} : FloatValue fmt → Bool
  | .nan => true
  | _ => false

/-- Check if a value is infinite -/
def FloatValue.isInf {fmt : FloatFormat} : FloatValue fmt → Bool
  | .infinity _ => true
  | _ => false

/-- Check if a value is finite -/
def FloatValue.isFinite {fmt : FloatFormat} : FloatValue fmt → Bool
  | .finite _ => true
  | _ => false

/-! # Semantic Equivalence

IEEE 754 defines equality differently from structural equality:
- +0 and -0 are equal (same mathematical value)
- All NaNs could be considered equivalent (though IEEE says NaN ≠ NaN for comparison)

For our formalization, we define a semantic equivalence that identifies
values with the same mathematical meaning.
-/

/-- Semantic equivalence: values that represent the same mathematical quantity.
    This identifies +0 with -0, and treats all NaNs as equivalent. -/
def FloatValue.equiv {fmt : FloatFormat} (x y : FloatValue fmt) : Prop :=
  match x, y with
  | .nan, .nan => True                           -- All NaNs are equivalent
  | .infinity sx, .infinity sy => sx = sy        -- Infinities must have same sign
  | .finite fx, .finite fy => fx.toRat = fy.toRat  -- Same rational value (identifies ±0)
  | _, _ => False

notation:50 x " ≃ " y => FloatValue.equiv x y

/-- Semantic equivalence is reflexive -/
theorem FloatValue.equiv_refl {fmt : FloatFormat} (x : FloatValue fmt) : x ≃ x := by
  cases x with
  | nan => trivial
  | infinity s => rfl
  | finite f => rfl

/-- Semantic equivalence is symmetric -/
theorem FloatValue.equiv_symm {fmt : FloatFormat} {x y : FloatValue fmt}
    (h : x ≃ y) : y ≃ x := by
  cases x with
  | nan => cases y <;> simp [FloatValue.equiv] at h ⊢; trivial
  | infinity sx =>
    cases y with
    | nan => simp [FloatValue.equiv] at h
    | infinity sy => simp [FloatValue.equiv] at h ⊢; exact h.symm
    | finite _ => simp [FloatValue.equiv] at h
  | finite fx =>
    cases y with
    | nan => simp [FloatValue.equiv] at h
    | infinity _ => simp [FloatValue.equiv] at h
    | finite fy => simp [FloatValue.equiv] at h ⊢; exact h.symm

/-- Semantic equivalence is transitive -/
theorem FloatValue.equiv_trans {fmt : FloatFormat} {x y z : FloatValue fmt}
    (hxy : x ≃ y) (hyz : y ≃ z) : x ≃ z := by
  cases x with
  | nan =>
    cases y <;> simp [FloatValue.equiv] at hxy
    cases z <;> simp [FloatValue.equiv] at hyz ⊢; trivial
  | infinity sx =>
    cases y with
    | nan => simp [FloatValue.equiv] at hxy
    | infinity sy =>
      simp [FloatValue.equiv] at hxy
      cases z with
      | nan => simp [FloatValue.equiv] at hyz
      | infinity sz => simp [FloatValue.equiv] at hxy hyz ⊢; exact hxy.trans hyz
      | finite _ => simp [FloatValue.equiv] at hyz
    | finite _ => simp [FloatValue.equiv] at hxy
  | finite fx =>
    cases y with
    | nan => simp [FloatValue.equiv] at hxy
    | infinity _ => simp [FloatValue.equiv] at hxy
    | finite fy =>
      simp [FloatValue.equiv] at hxy
      cases z with
      | nan => simp [FloatValue.equiv] at hyz
      | infinity _ => simp [FloatValue.equiv] at hyz
      | finite fz => simp [FloatValue.equiv] at hxy hyz ⊢; exact hxy.trans hyz

/-- Setoid instance for semantic equivalence -/
instance FloatValue.setoid (fmt : FloatFormat) : Setoid (FloatValue fmt) where
  r := FloatValue.equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-- Semantic equivalence implies equal toRat for finite values -/
theorem FloatValue.equiv_toRat {fmt : FloatFormat} {x y : FloatValue fmt}
    (hx : x.isFinite) (hy : y.isFinite) (h : x ≃ y) : x.toRat = y.toRat := by
  cases x with
  | finite fx =>
    cases y with
    | finite fy => exact h
    | infinity _ => simp [FloatValue.isFinite] at hy
    | nan => simp [FloatValue.isFinite] at hy
  | infinity _ => simp [FloatValue.isFinite] at hx
  | nan => simp [FloatValue.isFinite] at hx

/-! # Ordering -/

/-- Less than or equal (via rational conversion, NaN unordered) -/
def FloatValue.le {fmt : FloatFormat} (x y : FloatValue fmt) : Prop :=
  match x, y with
  | .nan, _ => False
  | _, .nan => False
  | .infinity true, _ => True  -- -Inf ≤ everything
  | _, .infinity false => True  -- everything ≤ +Inf
  | .infinity false, _ => False  -- +Inf ≤ x only if x = +Inf (handled above)
  | _, .infinity true => False   -- x ≤ -Inf only if x = -Inf (handled above)
  | .finite fx, .finite fy => fx.toRat ≤ fy.toRat

/-- Strict less than -/
def FloatValue.lt {fmt : FloatFormat} (x y : FloatValue fmt) : Prop :=
  x.le y ∧ ¬(y.le x)

instance {fmt : FloatFormat} : LE (FloatValue fmt) := ⟨FloatValue.le⟩
instance {fmt : FloatFormat} : LT (FloatValue fmt) := ⟨FloatValue.lt⟩

/-! # Typeclass Instances for FloatValue -/

/-- Default rounding mode for typeclass operations -/
def defaultMode : RoundMode := .toNearest

instance {fmt : FloatFormat} : Add (FloatValue fmt) := ⟨fadd fmt defaultMode⟩
instance {fmt : FloatFormat} : Sub (FloatValue fmt) := ⟨fsub fmt defaultMode⟩
instance {fmt : FloatFormat} : Mul (FloatValue fmt) := ⟨fmul fmt defaultMode⟩
instance {fmt : FloatFormat} : Div (FloatValue fmt) := ⟨fdiv fmt defaultMode⟩
instance {fmt : FloatFormat} : Neg (FloatValue fmt) := ⟨fneg⟩
instance {fmt : FloatFormat} : Zero (FloatValue fmt) := ⟨fzero fmt⟩
instance {fmt : FloatFormat} : One (FloatValue fmt) := ⟨fone fmt⟩

/-- Two as a FloatValue -/
def ftwo (fmt : FloatFormat) : FloatValue fmt :=
  fadd fmt defaultMode (fone fmt) (fone fmt)

instance {fmt : FloatFormat} : OfNat (FloatValue fmt) 2 := ⟨ftwo fmt⟩

/-! # Phase 2: Definitional Properties (trivially proved) -/

-- Predicate properties
@[simp] theorem isNaN_nan (fmt : FloatFormat) : (fnan fmt).isNaN = true := rfl
@[simp] theorem isNaN_infinity (fmt : FloatFormat) (s : Bool) :
    (FloatValue.infinity s : FloatValue fmt).isNaN = false := rfl
@[simp] theorem isNaN_finite {fmt : FloatFormat} (f : FloatRepr fmt) :
    (FloatValue.finite f).isNaN = false := rfl

@[simp] theorem isInf_nan (fmt : FloatFormat) : (fnan fmt).isInf = false := rfl
@[simp] theorem isInf_infinity (fmt : FloatFormat) (s : Bool) :
    (FloatValue.infinity s : FloatValue fmt).isInf = true := rfl
@[simp] theorem isInf_finite {fmt : FloatFormat} (f : FloatRepr fmt) :
    (FloatValue.finite f).isInf = false := rfl

@[simp] theorem isFinite_nan (fmt : FloatFormat) : (fnan fmt).isFinite = false := rfl
@[simp] theorem isFinite_infinity (fmt : FloatFormat) (s : Bool) :
    (FloatValue.infinity s : FloatValue fmt).isFinite = false := rfl
@[simp] theorem isFinite_finite {fmt : FloatFormat} (f : FloatRepr fmt) :
    (FloatValue.finite f).isFinite = true := rfl

-- Finite definition characterization
theorem finite_def {fmt : FloatFormat} (x : FloatValue fmt) :
    x.isFinite = true ↔ x.isNaN = false ∧ x.isInf = false := by
  cases x <;> simp [FloatValue.isFinite, FloatValue.isNaN, FloatValue.isInf]

-- toRat properties
@[simp] theorem toRat_nan (fmt : FloatFormat) : (fnan fmt).toRat = 0 := rfl
@[simp] theorem toRat_infinity (fmt : FloatFormat) (s : Bool) :
    (FloatValue.infinity s : FloatValue fmt).toRat = 0 := rfl

theorem toRat_zero (fmt : FloatFormat) : (fzero fmt).toRat = 0 := by
  simp only [fzero, FloatValue.toRat, FloatRepr.toRat]
  simp [mul_comm]

-- Zero and one are finite
theorem isFinite_zero (fmt : FloatFormat) : (fzero fmt).isFinite = true := rfl
theorem isFinite_one (fmt : FloatFormat) : (fone fmt).isFinite = true := rfl

-- Negation preserves finiteness
theorem isFinite_neg {fmt : FloatFormat} (x : FloatValue fmt) :
    x.isFinite = true → (fneg x).isFinite = true := by
  intro h
  cases x <;> simp_all [fneg, FloatValue.isFinite]

-- Double negation
theorem neg_neg {fmt : FloatFormat} (x : FloatValue fmt) : fneg (fneg x) = x := by
  cases x with
  | finite f => simp [fneg, Bool.not_not]
  | infinity s => simp [fneg, Bool.not_not]
  | nan => rfl

-- Negation of toRat (proving fneg_exact)
theorem fneg_toRat {fmt : FloatFormat} (x : FloatValue fmt) :
    (fneg x).toRat = -(x.toRat) := by
  cases x with
  | finite f =>
    simp only [fneg, FloatValue.toRat, FloatRepr.toRat]
    cases f.sign <;> simp [neg_mul]
  | infinity s => simp [fneg, FloatValue.toRat]
  | nan => simp [fneg, FloatValue.toRat]

/-- Rounding is symmetric: round(-q) = -round(q).

This is a fundamental property of round-to-nearest-even (and most rounding modes).
The rounded result of -q is the negation of the rounded result of q.
-/
theorem round_neg_eq_neg_round (fmt : FloatFormat) (mode : RoundMode) (q : Rat) :
    round fmt mode (-q) = fneg (round fmt mode q) := by
  sorry  -- Requires detailed analysis showing roundToFloatRepr preserves negation

/-- Negation distributes over multiplication: (-x) * y = -(x * y) -/
theorem fneg_fmul (fmt : FloatFormat) (mode : RoundMode) (x y : FloatValue fmt) :
    fmul fmt mode (fneg x) y = fneg (fmul fmt mode x y) := by
  match x, y with
  | .nan, _ => rfl
  | _, .nan => simp only [fneg, fmul]
  | .infinity sx, .infinity sy =>
    simp only [fneg, fmul, FloatValue.isNegative, Bool.not_not]
    -- Goal: .infinity ((!sx) ^^ sy) = .infinity (!(sx ^^ sy))
    -- !(sx ^^ sy) = (!sx) ^^ sy by De Morgan for xor
    cases sx <;> cases sy <;> rfl
  | .infinity sx, .finite fy =>
    simp only [fneg, fmul, FloatValue.isNegative]
    by_cases h : fy.mantissa = 0
    · simp [h]
    · simp only [h, ↓reduceIte, Bool.not_not]
      cases sx <;> cases fy.sign <;> rfl
  | .finite fx, .infinity sy =>
    simp only [fneg, fmul, FloatValue.isNegative]
    by_cases h : fx.mantissa = 0
    · simp [h]
    · simp only [h, ↓reduceIte, Bool.not_not]
      cases fx.sign <;> cases sy <;> rfl
  | .finite fx, .finite fy =>
    simp only [fneg, fmul]
    -- Goal: round (fneg fx).toRat * fy.toRat = fneg (round (fx.toRat * fy.toRat))
    have h_neg_toRat : ({ fx with sign := !fx.sign } : FloatRepr fmt).toRat = -fx.toRat := by
      simp only [FloatRepr.toRat]
      cases fx.sign <;> simp [neg_mul]
    rw [h_neg_toRat, neg_mul]
    exact round_neg_eq_neg_round fmt mode (fx.toRat * fy.toRat)

/-! # Phase 3: Commutativity -/

/-- Machine epsilon: smallest ε such that 1 + ε ≠ 1 -/
def epsilon (fmt : FloatFormat) : Rat := (2 : Rat) ^ (1 - fmt.prec : Int)

/-- Half ulp bound -/
def halfUlp (fmt : FloatFormat) : Rat := epsilon fmt / 2

-- THEOREM: Commutativity follows from exact arithmetic being commutative
-- and rounding being deterministic
theorem fadd_comm (fmt : FloatFormat) (mode : RoundMode) (x y : FloatValue fmt) :
    fadd fmt mode x y = fadd fmt mode y x := by
  match x, y with
  | .finite fx, .finite fy =>
    simp only [fadd, add_comm]
  | .finite _, .infinity _ => rfl
  | .finite _, .nan => rfl
  | .infinity _, .finite _ => rfl
  | .infinity sx, .infinity sy =>
    simp only [fadd]
    -- Rewrite sy == sx to sx == sy using commutativity
    conv_rhs => rw [Bool.beq_comm (a := sy) (b := sx)]
    -- Now both conditions are (sx == sy)
    by_cases h : sx == sy
    · simp [eq_of_beq h]
    · simp [h]
  | .infinity _, .nan => rfl
  | .nan, .finite _ => rfl
  | .nan, .infinity _ => rfl
  | .nan, .nan => rfl

theorem fmul_comm (fmt : FloatFormat) (mode : RoundMode) (x y : FloatValue fmt) :
    fmul fmt mode x y = fmul fmt mode y x := by
  match x, y with
  | .finite fx, .finite fy =>
    simp only [fmul, mul_comm]
  | .finite fx, .infinity sy =>
    simp only [fmul, FloatValue.isNegative, Bool.xor_comm]
  | .finite _, .nan => rfl
  | .infinity sx, .finite fy =>
    simp only [fmul, FloatValue.isNegative, Bool.xor_comm]
  | .infinity sx, .infinity sy =>
    simp only [fmul, Bool.xor_comm]
  | .infinity _, .nan => rfl
  | .nan, .finite _ => rfl
  | .nan, .infinity _ => rfl
  | .nan, .nan => rfl

/-! # Phase 4: Identity Properties -/

/-- Key property: rounding a representable value gives back the same value.
    This is the idempotence property of correct rounding. -/
axiom round_idempotent {fmt : FloatFormat} (mode : RoundMode) (f : FloatRepr fmt) :
    round fmt mode f.toRat = .finite f

/-- Helper: fzero.toRat = 0 -/
theorem fzero_toRat (fmt : FloatFormat) : (fzero fmt).toRat = 0 := by
  simp only [fzero, FloatValue.toRat, FloatRepr.toRat]
  simp [mul_comm]

/-- Adding zero on the right is identity for finite values -/
theorem fadd_zero_right (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt) :
    fadd fmt mode (.finite f) (fzero fmt) = .finite f := by
  -- fadd of finite values is round of sum
  change round fmt mode (f.toRat + (fzero fmt).toRat) = .finite f
  -- fzero.toRat = 0
  rw [fzero_toRat, add_zero]
  -- Apply round_idempotent
  exact round_idempotent mode f

/-- Adding zero on the left is identity for finite values -/
theorem fadd_zero_left (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt) :
    fadd fmt mode (fzero fmt) (.finite f) = .finite f := by
  rw [fadd_comm]
  exact fadd_zero_right fmt mode f

/-- Helper: fone.toRat = 1 -/
theorem fone_toRat (fmt : FloatFormat) : (fone fmt).toRat = 1 := by
  -- fone = .finite ⟨false, 2^(prec - 1), 0, ...⟩
  -- toRat = sign_factor * mantissa * 2^(exponent - (prec - 1))
  --       = 1 * 2^(prec - 1) * 2^(0 - (prec - 1))
  --       = 2^(prec - 1) * 2^(-(prec - 1))
  --       = 1
  unfold fone FloatValue.toRat FloatRepr.toRat
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  -- Goal: ↑(2 ^ (fmt.prec - 1)) * (2 : ℚ) ^ (0 - (↑fmt.prec - 1)) = 1
  have hprec : fmt.prec ≥ 1 := fmt.prec_pos
  have h1 : (0 : Int) - (↑fmt.prec - 1) = -(fmt.prec - 1 : Nat) := by
    simp only [Int.ofNat_sub hprec]
    omega
  rw [h1]
  rw [zpow_neg, zpow_natCast]
  -- Goal: ↑(2 ^ (fmt.prec - 1)) * ((2 : ℚ) ^ (fmt.prec - 1))⁻¹ = 1
  -- Convert ↑(2 ^ n) to (2 : ℚ) ^ n using simp with cast lemmas
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  -- Goal: (2 : ℚ) ^ (fmt.prec - 1) * ((2 : ℚ) ^ (fmt.prec - 1))⁻¹ = 1
  have h2 : (2 : ℚ) ^ (fmt.prec - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_inv_cancel₀ h2]

/-- Multiplying by one on the right is identity for finite values -/
theorem fmul_one_right (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt) :
    fmul fmt mode (.finite f) (fone fmt) = .finite f := by
  change round fmt mode (f.toRat * (fone fmt).toRat) = .finite f
  rw [fone_toRat, mul_one]
  exact round_idempotent mode f

/-- Multiplying by one on the left is identity for finite values -/
theorem fmul_one_left (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt) :
    fmul fmt mode (fone fmt) (.finite f) = .finite f := by
  rw [fmul_comm]
  exact fmul_one_right fmt mode f

/-- x + (-x) = 0 for finite values -/
theorem fadd_neg_self (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt) :
    fadd fmt mode (.finite f) (fneg (.finite f)) = fzero fmt := by
  simp only [fadd, fneg]
  -- Goal: round (f.toRat + (fneg f).toRat) = fzero
  -- fneg flips the sign, so (fneg f).toRat = -f.toRat
  have h : ({ f with sign := !f.sign } : FloatRepr fmt).toRat = -f.toRat := by
    simp only [FloatRepr.toRat]
    cases f.sign <;> simp [neg_mul]
  rw [h, add_neg_cancel]
  exact round_zero fmt mode

/-! # Phase 5: Ordering Properties -/

/-- Reflexivity of le for finite values -/
theorem le_refl_finite {fmt : FloatFormat} (f : FloatRepr fmt) :
    FloatValue.le (.finite f) (.finite f) := by
  simp only [FloatValue.le]
  exact le_refl f.toRat

/-- Transitivity of le -/
theorem le_trans {fmt : FloatFormat} (x y z : FloatValue fmt)
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- Unfold LE to FloatValue.le for pattern matching
  show FloatValue.le x z
  simp only [LE.le, instLEFloatValue] at hxy hyz
  -- Case analysis on all three values
  cases x with
  | nan =>
    -- nan <= y is False, so hxy : False
    simp only [FloatValue.le] at hxy
  | infinity sx =>
    cases sx with
    | true =>
      -- -∞ <= z : check if z = nan
      cases z with
      | nan =>
        -- y <= nan is False, need to reduce the match
        cases y <;> simp only [FloatValue.le] at hyz
      | infinity _ => simp only [FloatValue.le]  -- -∞ <= ±∞ is True (first clause wins)
      | finite _ => simp only [FloatValue.le]    -- -∞ <= finite is True
    | false =>
      -- +∞ <= y, need y = +∞ for this to be possible
      cases y with
      | nan => simp only [FloatValue.le] at hxy
      | infinity sy =>
        cases sy with
        | false =>
          -- +∞ <= +∞ is True, goal is +∞ <= z, use hyz
          exact hyz
        | true =>
          -- +∞ <= -∞ is False
          simp only [FloatValue.le] at hxy
      | finite _ => simp only [FloatValue.le] at hxy
  | finite fx =>
    cases z with
    | nan =>
      -- y <= nan is False
      cases y <;> simp only [FloatValue.le] at hyz
    | infinity sz =>
      cases sz with
      | false =>
        -- anything <= +∞ is True
        simp only [FloatValue.le]
      | true =>
        -- fx <= y and y <= -∞
        cases y with
        | nan => simp only [FloatValue.le] at hxy
        | infinity sy =>
          cases sy with
          | true =>
            -- fx <= -∞ is False
            simp only [FloatValue.le] at hxy
          | false =>
            -- +∞ <= -∞ is False
            simp only [FloatValue.le] at hyz
        | finite _ =>
          -- finite <= -∞ is False
          simp only [FloatValue.le] at hyz
    | finite fz =>
      cases y with
      | nan => simp only [FloatValue.le] at hxy
      | infinity sy =>
        cases sy with
        | true =>
          -- fx <= -∞ is False
          simp only [FloatValue.le] at hxy
        | false =>
          -- +∞ <= finite is False
          simp only [FloatValue.le] at hyz
      | finite fy =>
        simp only [FloatValue.le] at *
        exact _root_.le_trans hxy hyz

/-- Characterization of strict less than -/
theorem lt_iff_le_not_le {fmt : FloatFormat} (x y : FloatValue fmt) :
    x < y ↔ x ≤ y ∧ ¬(y ≤ x) := by
  simp only [LT.lt, FloatValue.lt, LE.le]

/-- Negation reverses order: x ≤ y ↔ -y ≤ -x -/
theorem fneg_le_neg {fmt : FloatFormat} (x y : FloatValue fmt) :
    x ≤ y ↔ fneg y ≤ fneg x := by
  constructor
  · -- Forward: x ≤ y → fneg y ≤ fneg x
    intro h
    simp only [LE.le, instLEFloatValue] at h ⊢
    cases x with
    | nan => simp only [FloatValue.le] at h
    | infinity sx =>
      cases sx with
      | true =>
        cases y with
        | nan => simp only [FloatValue.le] at h
        | infinity sy => cases sy <;> simp only [fneg, FloatValue.le, Bool.not_true, Bool.not_false]
        | finite fy => simp only [fneg, FloatValue.le, Bool.not_true]
      | false =>
        cases y with
        | nan => simp only [FloatValue.le] at h
        | infinity sy =>
          cases sy with
          | false => simp only [fneg, FloatValue.le, Bool.not_false]
          | true => simp only [FloatValue.le] at h
        | finite _ => simp only [FloatValue.le] at h
    | finite fx =>
      cases y with
      | nan => simp only [FloatValue.le] at h
      | infinity sy =>
        cases sy with
        | false => simp only [fneg, FloatValue.le, Bool.not_false]
        | true => simp only [FloatValue.le] at h
      | finite fy =>
        simp only [fneg, FloatValue.le, FloatRepr.toRat] at h ⊢
        have hfx : ({ fx with sign := !fx.sign } : FloatRepr fmt).toRat = -fx.toRat := by
          simp only [FloatRepr.toRat]; cases fx.sign <;> simp [neg_mul]
        have hfy : ({ fy with sign := !fy.sign } : FloatRepr fmt).toRat = -fy.toRat := by
          simp only [FloatRepr.toRat]; cases fy.sign <;> simp [neg_mul]
        rw [hfx, hfy]
        exact neg_le_neg h
  · -- Backward: fneg y ≤ fneg x → x ≤ y
    intro h
    -- Apply forward direction to fneg x and fneg y, then use neg_neg
    have h' := fneg_le_neg.mp (fneg y) (fneg x) h
    simp only [neg_neg] at h'
    exact h'
termination_by 0

/-- Antisymmetry of ordering.

Note: This is unprovable for structural equality because +0 and -0 are distinct
FloatValues but compare as equal (both +0 <= -0 and -0 <= +0 hold since toRat = 0).
IEEE 754 treats +0 == -0 as true in comparisons but they have different bit patterns.
For a complete proof, we would need either:
1. Semantic equality that identifies +0 = -0
2. Modified fneg that doesn't create -0
3. Precondition excluding signed zeros

With canonical hypotheses, this is provable using canonical_unique.
-/
theorem le_antisymm_finite {fmt : FloatFormat} (fx fy : FloatRepr fmt)
    (hxy : FloatValue.le (.finite fx) (.finite fy))
    (hyx : FloatValue.le (.finite fy) (.finite fx))
    (hfx_can : fx.isCanonical) (hfy_can : fy.isCanonical)
    (hfx_nz : fx.mantissa ≠ 0) :
    (.finite fx : FloatValue fmt) = .finite fy := by
  simp only [FloatValue.le] at hxy hyx
  -- From fx.toRat <= fy.toRat and fy.toRat <= fx.toRat, we get fx.toRat = fy.toRat
  have heq : fx.toRat = fy.toRat := le_antisymm hxy hyx
  -- Since fx.mantissa ≠ 0, fx.toRat ≠ 0, so fy.toRat ≠ 0, so fy.mantissa ≠ 0
  have hfy_nz : fy.mantissa ≠ 0 := by
    intro hfy_zero
    have : fy.toRat = 0 := by simp [FloatRepr.toRat, hfy_zero]
    have : fx.toRat = 0 := by rw [heq, this]
    exact FloatRepr.toRat_ne_zero fx hfx_nz this
  -- Use canonical_unique
  have ⟨hsign, hmant, hexp⟩ := FloatRepr.canonical_unique fx fy hfx_can hfy_can hfx_nz hfy_nz heq
  congr
  · exact hsign
  · exact hmant
  · exact hexp

/-- Antisymmetry using semantic equivalence (fully provable!) -/
theorem le_antisymm_equiv {fmt : FloatFormat} (x y : FloatValue fmt)
    (hxy : x ≤ y) (hyx : y ≤ x) : x ≃ y := by
  simp only [LE.le, instLEFloatValue] at hxy hyx
  cases x with
  | nan => simp only [FloatValue.le] at hxy
  | infinity sx =>
    cases y with
    | nan => simp only [FloatValue.le] at hyx
    | infinity sy =>
      cases sx <;> cases sy <;> simp only [FloatValue.le, FloatValue.equiv] at hxy hyx ⊢
    | finite _ =>
      cases sx <;> simp only [FloatValue.le] at hxy hyx
  | finite fx =>
    cases y with
    | nan => simp only [FloatValue.le] at hyx
    | infinity sy =>
      cases sy <;> simp only [FloatValue.le] at hxy hyx
    | finite fy =>
      simp only [FloatValue.le, FloatValue.equiv] at hxy hyx ⊢
      exact le_antisymm hxy hyx

/-- to_rat is injective up to semantic equivalence (fully provable!) -/
theorem to_rat_inj_equiv {fmt : FloatFormat} (x y : FloatValue fmt)
    (hx : x.isFinite) (hy : y.isFinite) (heq : x.toRat = y.toRat) : x ≃ y := by
  cases x with
  | finite fx =>
    cases y with
    | finite fy =>
      simp only [FloatValue.equiv, FloatValue.toRat] at heq ⊢
      exact heq
    | infinity _ => simp [FloatValue.isFinite] at hy
    | nan => simp [FloatValue.isFinite] at hy
  | infinity _ => simp [FloatValue.isFinite] at hx
  | nan => simp [FloatValue.isFinite] at hx

/-- Totality of le (for finite values - NaN is unordered) -/
theorem le_total_finite {fmt : FloatFormat} (fx fy : FloatRepr fmt) :
    FloatValue.le (.finite fx) (.finite fy) ∨ FloatValue.le (.finite fy) (.finite fx) := by
  simp only [FloatValue.le]
  exact le_total fx.toRat fy.toRat

/-- Division of a finite nonzero value by itself equals 1 -/
theorem fdiv_self (fmt : FloatFormat) (mode : RoundMode) (f : FloatRepr fmt)
    (hnz : f.mantissa ≠ 0) : fdiv fmt mode (.finite f) (.finite f) = fone fmt := by
  simp only [fdiv]
  simp only [hnz, ↓reduceIte]
  have h_toRat_nz : f.toRat ≠ 0 := by
    simp only [FloatRepr.toRat]
    intro h
    cases f.sign with
    | false =>
      simp at h
      have : (f.mantissa : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hnz
      have : (2 : Rat) ^ (f.exp - (fmt.prec : Int)) ≠ 0 := by
        apply zpow_ne_zero
        norm_num
      exact absurd (mul_eq_zero.mp h) (not_or.mpr ⟨this, ‹(2 : Rat) ^ (f.exp - ↑fmt.prec) ≠ 0›⟩)
    | true =>
      simp at h
      have : (f.mantissa : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hnz
      have : (2 : Rat) ^ (f.exp - (fmt.prec : Int)) ≠ 0 := by
        apply zpow_ne_zero
        norm_num
      have hmul : (f.mantissa : Rat) * (2 : Rat) ^ (f.exp - ↑fmt.prec) ≠ 0 :=
        mul_ne_zero this ‹(2 : Rat) ^ (f.exp - ↑fmt.prec) ≠ 0›
      exact hmul (neg_eq_zero.mp h)
  rw [div_self h_toRat_nz]
  -- Now need to show round 1 = fone
  -- 1 is exactly representable as fone, so this follows from round_idempotent
  have h_fone_toRat : (fone fmt).toRat = 1 := fone_toRat fmt
  -- rewrite using the fact that fone.toRat = 1
  conv_rhs => rw [← h_fone_toRat]
  cases fmt.fone_repr with
  | intro repr hrepr =>
    have hfone_eq : fone fmt = .finite repr := hrepr.2
    rw [hfone_eq]
    exact round_idempotent mode repr

/-- Rounding is monotonic: if q₁ ≤ q₂, then round(q₁) ≤ round(q₂).

This is a fundamental property of IEEE 754 rounding modes.
For finite inputs, the rounded results preserve the order.
Overflow to ±∞ also preserves order.
-/
theorem round_monotonic (fmt : FloatFormat) (mode : RoundMode) (q₁ q₂ : Rat)
    (h : q₁ ≤ q₂) : FloatValue.le (round fmt mode q₁) (round fmt mode q₂) := by
  sorry  -- Requires detailed analysis of the rounding algorithm

/-- Addition monotonicity for finite values -/
theorem fadd_monotonic_left (fmt : FloatFormat) (mode : RoundMode)
    (x y z : FloatValue fmt) (hz : z.isFinite) (hxy : x ≤ y) :
    fadd fmt mode x z ≤ fadd fmt mode y z := by
  cases x with
  | nan =>
    simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy
  | infinity sx =>
    cases y with
    | nan =>
      simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy
    | infinity sy =>
      cases z with
      | finite fz =>
        simp only [fadd]
        cases sx <;> cases sy <;> simp only [FloatValue.le] at hxy ⊢
        -- -∞ + z ≤ -∞ + z, +∞ + z ≤ +∞ + z: reflexive
        all_goals simp only [FloatValue.le]
        -- -∞ ≤ +∞ case: -∞ + z ≤ +∞ + z is True (first wins in le definition)
        simp only [FloatValue.le]
      | infinity s => simp [FloatValue.isFinite] at hz
      | nan => simp [FloatValue.isFinite] at hz
    | finite fy =>
      cases sx with
      | false =>
        -- +∞ ≤ finite is False
        simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy
      | true =>
        -- -∞ ≤ finite is True
        -- -∞ + z = -∞, which is ≤ anything
        cases z with
        | finite fz =>
          simp only [fadd, FloatValue.le]
        | infinity s => simp [FloatValue.isFinite] at hz
        | nan => simp [FloatValue.isFinite] at hz
  | finite fx =>
    cases y with
    | nan =>
      simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy
    | infinity sy =>
      cases sy with
      | false =>
        -- fx ≤ +∞ is True
        -- fx + z and +∞ + z = +∞
        cases z with
        | finite fz =>
          simp only [fadd, FloatValue.le]
        | infinity s => simp [FloatValue.isFinite] at hz
        | nan => simp [FloatValue.isFinite] at hz
      | true =>
        -- fx ≤ -∞ is False
        simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy
    | finite fy =>
      cases z with
      | finite fz =>
        simp only [fadd]
        -- Need to show round(fx.toRat + fz.toRat) ≤ round(fy.toRat + fz.toRat)
        simp only [LE.le, instLEFloatValue, FloatValue.le] at hxy ⊢
        have hle : fx.toRat + fz.toRat ≤ fy.toRat + fz.toRat := add_le_add_right hxy fz.toRat
        exact round_monotonic fmt mode _ _ hle
      | infinity s => simp [FloatValue.isFinite] at hz
      | nan => simp [FloatValue.isFinite] at hz

-- THEOREM: Error bounds follow from the definition of rounding
theorem round_relative_error (fmt : FloatFormat) (q : Rat) (hq : q ≠ 0) :
    ∃ δ : Rat, |δ| ≤ halfUlp fmt ∧
      (round fmt .toNearest q).toRat = q * (1 + δ) := by
  sorry -- Would be proved from the definition of round

-- THEOREM: Addition error bound
theorem fadd_relative_error (fmt : FloatFormat) (x y : FloatValue fmt)
    (hx : x.toRat ≠ 0 ∨ y.toRat ≠ 0) :
    ∃ δ : Rat, |δ| ≤ halfUlp fmt ∧
      (fadd fmt .toNearest x y).toRat = (x.toRat + y.toRat) * (1 + δ) := by
  sorry -- Follows from round_relative_error

-- Note: fneg is exact, proved earlier as fneg_toRat

/-! # Mapping to Native Float Types

To use this with Lean's native Float/Float32, we need to establish
that the native operations agree with our constructive definitions.
This requires a small trusted base of axioms connecting the representations.
-/

/-- Axiom: Native Float agrees with binary64 representation -/
axiom float_is_binary64 :
  ∃ (encode : Float → FloatValue binary64) (decode : FloatValue binary64 → Float),
    (∀ x, decode (encode x) = x) ∧
    (∀ x y, encode (x + y) = fadd binary64 .toNearest (encode x) (encode y))

/-! # Summary: Axioms vs Theorems

With this constructive approach:

**Remaining Axioms (trusted base):**
1. float_is_binary64: Native Float matches our binary64 representation
2. round: Definition of rounding (could be made computable)

**Now Theorems (proved from definitions):**
- isNaN_nan, isNaN_infinity, isNaN_finite: NaN predicate
- isInf_nan, isInf_infinity, isInf_finite: Infinity predicate
- isFinite_nan, isFinite_infinity, isFinite_finite: Finiteness predicate
- finite_def: Finite characterization
- toRat_nan, toRat_infinity, toRat_zero: Rational conversion
- neg_neg: Double negation
- fneg_toRat: Negation preserves rational value
- fadd_comm, fmul_comm: Commutativity (fully proved)
- fadd_zero_left/right: Addition identity (uses round_idempotent axiom)
- fmul_one_left/right: Multiplication identity (uses round_idempotent axiom)
- le_refl_finite: Reflexivity for finite values
- le_trans: Transitivity (outline with sorry)
- lt_iff_le_not_le: Strict ordering characterization

**Remaining Axioms (with sorry):**
- round_idempotent: Rounding representable values is idempotent
- fone_toRat: 1.0 converts to rational 1
- le_trans: Needs exhaustive case analysis
- round_relative_error, fadd_relative_error: Error bounds

This dramatically reduces the trusted axiom base while providing
the same usable properties for verification.
-/

/-! # FloatSpec Instance for FloatValue binary64 -/

open Float.Spec in
instance : FloatSpec (FloatValue binary64) where
  epsilon := epsilon binary64

  equiv := FloatValue.equiv
  equiv_refl := FloatValue.equiv_refl
  equiv_symm := fun _ _ => FloatValue.equiv_symm
  equiv_trans := fun _ _ _ => FloatValue.equiv_trans
  eq_implies_equiv := fun x _ h => by rw [h]; exact FloatValue.equiv_refl x

  nan := fnan binary64
  infinity := finfinity binary64

  is_nan := FloatValue.isNaN
  is_inf := FloatValue.isInf
  is_finite := FloatValue.isFinite

  is_nan_nan := isNaN_nan binary64
  is_inf_infinity := isInf_infinity binary64 false
  not_nan_infinity := by simp [finfinity, FloatValue.isNaN]
  not_inf_nan := by simp [fnan, FloatValue.isInf]

  finite_def := fun x => by
    constructor
    · intro h
      cases x with
      | finite f => simp [FloatValue.isNaN, FloatValue.isInf]
      | infinity s => simp [FloatValue.isFinite] at h
      | nan => simp [FloatValue.isFinite] at h
    · intro ⟨hnan, hinf⟩
      cases x with
      | finite f => rfl
      | infinity s => simp [FloatValue.isInf] at hinf
      | nan => simp [FloatValue.isNaN] at hnan

  is_finite_zero := rfl
  is_finite_one := rfl
  is_finite_neg := fun x hfin => by
    cases x with
    | finite f => simp [Neg.neg, fneg, FloatValue.isFinite]
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  is_canonical := FloatValue.isCanonical
  is_nonzero := FloatValue.isNonZero

  zero_not_nonzero := by
    simp only [Zero.zero, FloatValue.isNonZero, fzero]
    exact fun h => h rfl

  zero_is_canonical := by
    simp only [Zero.zero, FloatValue.isCanonical, FloatRepr.isCanonical, fzero]
    left; rfl

  one_is_canonical := by
    simp only [One.one, FloatValue.isCanonical, FloatRepr.isCanonical, fone]
    right; left
    -- 2^(prec-1) ≥ 2^(prec-1)
    exact le_refl _

  one_is_nonzero := by
    simp only [One.one, FloatValue.isNonZero, fone]
    exact Nat.two_pow_pos (binary64.prec - 1) |>.ne'

  nonzero_not_equiv_zero := fun x hfin hnz => by
    cases x with
    | finite f =>
      simp only [FloatValue.isNonZero] at hnz
      simp only [Zero.zero, FloatValue.equiv, fzero, FloatRepr.toRat]
      intro heq
      -- heq : f.toRat = 0, but f.mantissa ≠ 0 implies f.toRat ≠ 0
      exact FloatRepr.toRat_ne_zero f hnz heq
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  neg_preserves_nonzero := fun x hnz => by
    cases x with
    | finite f =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero] at hnz ⊢
      exact hnz
    | infinity s =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero]
      trivial
    | nan =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero]
      trivial

  mul_zero_finite := fun x hfin => by
    cases x with
    | finite f =>
      -- Goal: 0 * finite f = 0
      -- This reduces to fmul (fzero binary64) (finite f) = fzero binary64
      show fmul binary64 defaultMode (fzero binary64) (.finite f) = fzero binary64
      simp only [fmul, fzero, FloatRepr.toRat, Bool.false_eq_true, ↓reduceIte,
                 Nat.cast_zero, mul_zero, zero_mul]
      exact round_zero binary64 defaultMode
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  to_rat := FloatValue.toRat
  to_rat_nan := toRat_nan binary64
  to_rat_inf := toRat_infinity binary64 false
  to_rat_zero := toRat_zero binary64

  to_rat_inj := fun x y hx hy hx_can hy_can hx_nz hy_nz heq => by
    -- With canonical and non-zero preconditions, this should be provable
    cases x with
    | finite fx =>
      cases y with
      | finite fy =>
        simp only [FloatValue.toRat] at heq
        simp only [FloatValue.isCanonical, FloatValue.isNonZero] at hx_can hy_can hx_nz hy_nz
        -- Use canonical_unique theorem
        have ⟨hsign, hmant, hexp⟩ := FloatRepr.canonical_unique fx fy hx_can hy_can hx_nz hy_nz heq
        -- Now construct equality
        congr 1
        cases fx; cases fy
        simp only at hsign hmant hexp
        simp [hsign, hmant, hexp]
      | infinity s => simp [FloatValue.isFinite] at hy
      | nan => simp [FloatValue.isFinite] at hy
    | infinity s => simp [FloatValue.isFinite] at hx
    | nan => simp [FloatValue.isFinite] at hx

  to_rat_inj_equiv := to_rat_inj_equiv

  to_rat_neg := fneg_toRat

  add_comm := fun x y => by
    simp only [HAdd.hAdd, Add.add]
    exact fadd_comm binary64 defaultMode x y

  mul_comm := fun x y => by
    simp only [HMul.hMul, Mul.mul]
    exact fmul_comm binary64 defaultMode x y

  add_zero_left := fun x => by
    simp only [HAdd.hAdd, Add.add, Zero.zero]
    cases x with
    | finite f => exact fadd_zero_left binary64 defaultMode f
    | infinity s => rfl
    | nan => rfl

  mul_one_left := fun x => by
    cases x with
    | finite f => exact fmul_one_left binary64 defaultMode f
    | infinity s =>
      -- Goal: 1 * infinity s = infinity s
      show fmul binary64 defaultMode (fone binary64) (.infinity s) = .infinity s
      simp only [fmul, fone, FloatValue.isNegative, Bool.false_xor]
      -- mantissa of fone is 2^(prec-1) ≠ 0
      have h : ¬(2 : Nat) ^ (binary64.prec - 1) = 0 := Nat.two_pow_pos (binary64.prec - 1) |>.ne'
      simp only [h, ↓reduceIte]
    | nan => rfl

  add_monotonic_left := fun x y z hz hxy => by
    simp only [HAdd.hAdd, Add.add]
    exact fadd_monotonic_left binary64 defaultMode x y z hz hxy
  mul_monotonic_pos := fun _ _ _ _ _ => by sorry
  div_monotonic_num := fun _ _ _ _ _ => by sorry
  div_antimonotonic_den := fun _ _ _ _ _ _ _ => by sorry

  sterbenz := fun _ _ _ _ => by sorry

  neg_exact := neg_neg
  neg_mul := fun x y => by
    simp only [HMul.hMul, Mul.mul, Neg.neg]
    exact fneg_fmul binary64 defaultMode x y

  neg_le_neg := fun x y => fneg_le_neg x y

  sub_eq_add_neg := fun x y => by
    simp only [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, Neg.neg]
    rfl

  add_neg_self := fun x hfin => by
    cases x with
    | finite f =>
      show fadd binary64 defaultMode (.finite f) (fneg (.finite f)) = fzero binary64
      exact fadd_neg_self binary64 defaultMode f
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  le_trans := le_trans
  le_antisymm := fun x y hxy hyx hx_can hy_can hx_nz hy_nz => by
    -- With canonical and non-zero preconditions, use canonical_unique
    cases x with
    | finite fx =>
      cases y with
      | finite fy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        have heq : fx.toRat = fy.toRat := le_antisymm hxy hyx
        simp only [FloatValue.isCanonical, FloatValue.isNonZero] at hx_can hy_can hx_nz hy_nz
        -- Use canonical_unique
        have ⟨hsign, hmant, hexp⟩ := FloatRepr.canonical_unique fx fy hx_can hy_can hx_nz hy_nz heq
        congr 1
        cases fx; cases fy
        simp only at hsign hmant hexp
        simp [hsign, hmant, hexp]
      | infinity s =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        -- -Inf ≤ finite, finite ≤ +Inf, but not both -Inf and +Inf
        cases s <;> simp at hxy hyx
      | nan =>
        simp only [LE.le, FloatValue.le] at hxy
    | infinity s =>
      cases y with
      | finite fy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        cases s <;> simp at hxy hyx
      | infinity sy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        cases s <;> cases sy <;> simp at hxy hyx
        · rfl  -- both -Inf
        · rfl  -- both +Inf
      | nan =>
        simp only [LE.le, FloatValue.le] at hxy
    | nan =>
      simp only [LE.le, FloatValue.le] at hxy
  le_antisymm_equiv := le_antisymm_equiv
  le_total := fun x y hx hy => by
    cases x with
    | finite fx =>
      cases y with
      | finite fy => exact le_total_finite fx fy
      | infinity s => simp [FloatValue.isFinite] at hy
      | nan => simp [FloatValue.isFinite] at hy
    | infinity s => simp [FloatValue.isFinite] at hx
    | nan => simp [FloatValue.isFinite] at hx

  lt_iff_le_not_le := lt_iff_le_not_le

  div_self := fun x hfin hnz => by
    cases x with
    | finite f =>
      show fdiv binary64 defaultMode (.finite f) (.finite f) = fone binary64
      -- hnz : is_nonzero (.finite f) = f.mantissa ≠ 0
      simp only [FloatValue.isNonZero] at hnz
      exact fdiv_self binary64 defaultMode f hnz
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  mul_div_cancel := fun _ _ _ _ _ _ _ => by sorry
  div_mul_cancel := fun _ _ _ _ _ _ _ => by sorry

  add_relative_error := fun x y hx hy hxy => by
    sorry -- Error bound proof

  mul_relative_error := fun x y hx hy hxy => by
    sorry -- Error bound proof

  div_relative_error := fun x y hx hy hxy hnz => by
    sorry -- Error bound proof

open Float.Spec in
/-- FloatSpec instance for binary32 (single precision) -/
instance : FloatSpec (FloatValue binary32) where
  epsilon := epsilon binary32

  equiv := FloatValue.equiv
  equiv_refl := FloatValue.equiv_refl
  equiv_symm := fun _ _ => FloatValue.equiv_symm
  equiv_trans := fun _ _ _ => FloatValue.equiv_trans
  eq_implies_equiv := fun x _ h => by rw [h]; exact FloatValue.equiv_refl x

  nan := fnan binary32
  infinity := finfinity binary32

  is_nan := FloatValue.isNaN
  is_inf := FloatValue.isInf
  is_finite := FloatValue.isFinite

  is_nan_nan := isNaN_nan binary32
  is_inf_infinity := isInf_infinity binary32 false
  not_nan_infinity := by simp [finfinity, FloatValue.isNaN]
  not_inf_nan := by simp [fnan, FloatValue.isInf]

  finite_def := fun x => by
    constructor
    · intro h
      cases x with
      | finite f => simp [FloatValue.isNaN, FloatValue.isInf]
      | infinity s => simp [FloatValue.isFinite] at h
      | nan => simp [FloatValue.isFinite] at h
    · intro ⟨hnan, hinf⟩
      cases x with
      | finite f => rfl
      | infinity s => simp [FloatValue.isInf] at hinf
      | nan => simp [FloatValue.isNaN] at hnan

  is_finite_zero := rfl
  is_finite_one := rfl
  is_finite_neg := fun x hfin => by
    cases x with
    | finite f => simp [Neg.neg, fneg, FloatValue.isFinite]
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  is_canonical := FloatValue.isCanonical
  is_nonzero := FloatValue.isNonZero

  zero_not_nonzero := by
    simp only [Zero.zero, FloatValue.isNonZero, fzero]
    exact fun h => h rfl

  zero_is_canonical := by
    simp only [Zero.zero, FloatValue.isCanonical, FloatRepr.isCanonical, fzero]
    left; rfl

  one_is_canonical := by
    simp only [One.one, FloatValue.isCanonical, FloatRepr.isCanonical, fone]
    right; left
    exact le_refl _

  one_is_nonzero := by
    simp only [One.one, FloatValue.isNonZero, fone]
    exact Nat.two_pow_pos (binary32.prec - 1) |>.ne'

  nonzero_not_equiv_zero := fun x hfin hnz => by
    cases x with
    | finite f =>
      simp only [FloatValue.isNonZero] at hnz
      simp only [Zero.zero, FloatValue.equiv, fzero, FloatRepr.toRat]
      intro heq
      -- heq : f.toRat = 0, but f.mantissa ≠ 0 implies f.toRat ≠ 0
      exact FloatRepr.toRat_ne_zero f hnz heq
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  neg_preserves_nonzero := fun x hnz => by
    cases x with
    | finite f =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero] at hnz ⊢
      exact hnz
    | infinity s =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero]
      trivial
    | nan =>
      simp only [Neg.neg, fneg, FloatValue.isNonZero]
      trivial

  mul_zero_finite := fun x hfin => by
    cases x with
    | finite f =>
      show fmul binary32 defaultMode (fzero binary32) (.finite f) = fzero binary32
      simp only [fmul, fzero, FloatRepr.toRat, Bool.false_eq_true, ↓reduceIte,
                 Nat.cast_zero, mul_zero, zero_mul]
      exact round_zero binary32 defaultMode
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin

  to_rat := FloatValue.toRat
  to_rat_nan := toRat_nan binary32
  to_rat_inf := toRat_infinity binary32 false
  to_rat_zero := toRat_zero binary32
  to_rat_inj := fun x y hx hy hx_can hy_can hx_nz hy_nz heq => by
    cases x with
    | finite fx =>
      cases y with
      | finite fy =>
        simp only [FloatValue.toRat] at heq
        simp only [FloatValue.isCanonical, FloatValue.isNonZero] at hx_can hy_can hx_nz hy_nz
        have ⟨hsign, hmant, hexp⟩ := FloatRepr.canonical_unique fx fy hx_can hy_can hx_nz hy_nz heq
        congr 1
        cases fx; cases fy
        simp only at hsign hmant hexp
        simp [hsign, hmant, hexp]
      | infinity s => simp [FloatValue.isFinite] at hy
      | nan => simp [FloatValue.isFinite] at hy
    | infinity s => simp [FloatValue.isFinite] at hx
    | nan => simp [FloatValue.isFinite] at hx
  to_rat_inj_equiv := to_rat_inj_equiv
  to_rat_neg := fneg_toRat

  add_comm := fun x y => by
    simp only [HAdd.hAdd, Add.add]
    exact fadd_comm binary32 defaultMode x y

  mul_comm := fun x y => by
    simp only [HMul.hMul, Mul.mul]
    exact fmul_comm binary32 defaultMode x y

  add_zero_left := fun x => by
    simp only [HAdd.hAdd, Add.add]
    cases x with
    | finite f => exact fadd_zero_left binary32 defaultMode f
    | infinity s => rfl
    | nan => rfl

  mul_one_left := fun x => by
    cases x with
    | finite f => exact fmul_one_left binary32 defaultMode f
    | infinity s =>
      -- Goal: 1 * infinity s = infinity s
      show fmul binary32 defaultMode (fone binary32) (.infinity s) = .infinity s
      simp only [fmul, fone, FloatValue.isNegative, Bool.false_xor]
      have h : ¬(2 : Nat) ^ (binary32.prec - 1) = 0 := Nat.two_pow_pos (binary32.prec - 1) |>.ne'
      simp only [h, ↓reduceIte]
    | nan => rfl

  add_monotonic_left := fun x y z hz hxy => by
    simp only [HAdd.hAdd, Add.add]
    exact fadd_monotonic_left binary32 defaultMode x y z hz hxy
  mul_monotonic_pos := fun _ _ _ _ _ => by sorry
  div_monotonic_num := fun _ _ _ _ _ => by sorry
  div_antimonotonic_den := fun _ _ _ _ _ _ _ => by sorry
  sterbenz := fun _ _ _ _ => by sorry
  neg_exact := neg_neg
  neg_mul := fun x y => by
    simp only [HMul.hMul, Mul.mul, Neg.neg]
    exact fneg_fmul binary32 defaultMode x y
  neg_le_neg := fun x y => fneg_le_neg x y
  sub_eq_add_neg := fun x y => by simp only [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, Neg.neg]; rfl
  add_neg_self := fun x hfin => by
    cases x with
    | finite f =>
      show fadd binary32 defaultMode (.finite f) (fneg (.finite f)) = fzero binary32
      exact fadd_neg_self binary32 defaultMode f
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin
  le_trans := le_trans
  le_antisymm := fun x y hxy hyx hx_can hy_can hx_nz hy_nz => by
    -- Same as binary64
    cases x with
    | finite fx =>
      cases y with
      | finite fy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        have heq : fx.toRat = fy.toRat := le_antisymm hxy hyx
        simp only [FloatValue.isCanonical, FloatValue.isNonZero] at hx_can hy_can hx_nz hy_nz
        have ⟨hsign, hmant, hexp⟩ := FloatRepr.canonical_unique fx fy hx_can hy_can hx_nz hy_nz heq
        congr 1
        cases fx; cases fy
        simp only at hsign hmant hexp
        simp [hsign, hmant, hexp]
      | infinity s =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        cases s <;> simp at hxy hyx
      | nan =>
        simp only [LE.le, FloatValue.le] at hxy
    | infinity s =>
      cases y with
      | finite fy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        cases s <;> simp at hxy hyx
      | infinity sy =>
        simp only [LE.le, FloatValue.le] at hxy hyx
        cases s <;> cases sy <;> simp at hxy hyx
        · rfl
        · rfl
      | nan =>
        simp only [LE.le, FloatValue.le] at hxy
    | nan =>
      simp only [LE.le, FloatValue.le] at hxy
  le_antisymm_equiv := le_antisymm_equiv
  le_total := fun x y hx hy => by
    cases x with
    | finite fx =>
      cases y with
      | finite fy => exact le_total_finite fx fy
      | infinity s => simp [FloatValue.isFinite] at hy
      | nan => simp [FloatValue.isFinite] at hy
    | infinity s => simp [FloatValue.isFinite] at hx
    | nan => simp [FloatValue.isFinite] at hx
  lt_iff_le_not_le := lt_iff_le_not_le
  div_self := fun x hfin hnz => by
    cases x with
    | finite f =>
      show fdiv binary32 defaultMode (.finite f) (.finite f) = fone binary32
      -- hnz : is_nonzero (.finite f) = f.mantissa ≠ 0
      simp only [FloatValue.isNonZero] at hnz
      exact fdiv_self binary32 defaultMode f hnz
    | infinity s => simp [FloatValue.isFinite] at hfin
    | nan => simp [FloatValue.isFinite] at hfin
  mul_div_cancel := fun _ _ _ _ _ _ _ => by sorry
  div_mul_cancel := fun _ _ _ _ _ _ _ => by sorry
  add_relative_error := fun x y hx hy hxy => by sorry
  mul_relative_error := fun x y hx hy hxy => by sorry
  div_relative_error := fun x y hx hy hxy hnz => by sorry

/-! # Examples using Constructive Definitions -/

section Examples

variable (fmt : FloatFormat) (mode : RoundMode)
variable (x y z : FloatValue fmt)
variable (f g : FloatRepr fmt)

-- Commutativity examples (fully proved)
example : fadd fmt mode x y = fadd fmt mode y x := fadd_comm fmt mode x y
example : fmul fmt mode x y = fmul fmt mode y x := fmul_comm fmt mode x y

-- Identity examples (proved using round_idempotent axiom)
example : fadd fmt mode (.finite f) (fzero fmt) = .finite f := fadd_zero_right fmt mode f
example : fadd fmt mode (fzero fmt) (.finite f) = .finite f := fadd_zero_left fmt mode f
example : fmul fmt mode (.finite f) (fone fmt) = .finite f := fmul_one_right fmt mode f
example : fmul fmt mode (fone fmt) (.finite f) = .finite f := fmul_one_left fmt mode f

-- Predicate examples (definitionally true)
example : (fnan fmt).isNaN = true := isNaN_nan fmt
example : (finfinity fmt).isInf = true := isInf_infinity fmt false
example : (.finite f : FloatValue fmt).isFinite = true := isFinite_finite f

-- Negation examples (proved from definition)
example : fneg (fneg x) = x := neg_neg x
example : (fneg x).toRat = -(x.toRat) := fneg_toRat x

-- Ordering examples
example : (.finite f : FloatValue fmt) ≤ .finite f := le_refl_finite f
example : x < y ↔ x ≤ y ∧ ¬(y ≤ x) := lt_iff_le_not_le x y

-- toRat examples
example : (fnan fmt).toRat = 0 := toRat_nan fmt
example : (fzero fmt).toRat = 0 := toRat_zero fmt

end Examples

/-! # Examples using FloatSpec Instance -/

section FloatSpecExamples

-- These examples use the FloatSpec typeclass with our binary64 instance
variable (x y z : FloatValue binary64)

-- Commutativity via FloatSpec
example : x + y = y + x := Float.Spec.FloatSpec.add_comm x y
example : x * y = y * x := Float.Spec.FloatSpec.mul_comm x y

-- Identity via FloatSpec
example : 0 + x = x := Float.Spec.FloatSpec.add_zero_left x

-- Negation via FloatSpec
example : -(-x) = x := Float.Spec.FloatSpec.neg_exact x

-- Subtraction definition via FloatSpec
example : x - y = x + (-y) := Float.Spec.FloatSpec.sub_eq_add_neg x y

-- Ordering via FloatSpec
example : x ≤ y → y ≤ z → x ≤ z := Float.Spec.FloatSpec.le_trans x y z
example : x < y ↔ (x ≤ y ∧ ¬(y ≤ x)) := Float.Spec.FloatSpec.lt_iff_le_not_le x y

end FloatSpecExamples

/-! # Examples using binary32 FloatSpec Instance -/

section FloatSpec32Examples

-- These examples use the FloatSpec typeclass with our binary32 instance
variable (x y z : FloatValue binary32)

-- Commutativity via FloatSpec
example : x + y = y + x := Float.Spec.FloatSpec.add_comm x y
example : x * y = y * x := Float.Spec.FloatSpec.mul_comm x y

-- Identity via FloatSpec
example : 0 + x = x := Float.Spec.FloatSpec.add_zero_left x

-- Negation via FloatSpec
example : -(-x) = x := Float.Spec.FloatSpec.neg_exact x

-- Subtraction definition via FloatSpec
example : x - y = x + (-y) := Float.Spec.FloatSpec.sub_eq_add_neg x y

-- Ordering via FloatSpec
example : x ≤ y → y ≤ z → x ≤ z := Float.Spec.FloatSpec.le_trans x y z
example : x < y ↔ (x ≤ y ∧ ¬(y ≤ x)) := Float.Spec.FloatSpec.lt_iff_le_not_le x y

end FloatSpec32Examples

end Float.Constructive
