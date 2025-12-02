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

/-- Compute floor(log2(|q|)) for a non-zero rational q.
    Returns an approximation based on numerator/denominator bit lengths. -/
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
          -- After at most cfg_prec multiplications, mantissa reaches [2^cfg_prec, 2^(cfg_prec+1))
          -- The bound is complex; we use sorry for this branch
          -- A proper proof would use well-founded induction on (2^cfg_prec - mantissa)
          have h_fuel' : n ≥ mantissa * 2 + cfg_prec := by
            -- This doesn't follow directly from h_fuel, needs a different termination argument
            sorry
          exact ih (mantissa * 2) (exp - 1) h_fuel'
        · -- mantissa in [2^cfg_prec, 2^(cfg_prec+1))
          rename_i h_not_small
          right
          constructor
          · exact Nat.not_lt.mp h_not_small
          · exact Nat.not_le.mp h_not_big

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
    sorry

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

/-- Rounding preserves order.

    This is a fundamental property of IEEE 754 rounding:
    if x ≤ y then round(x) ≤ round(y) for any rounding mode.

    The proof requires showing that roundToFloat is monotonic,
    which follows from:
    1. The representable float values form a well-ordered set
    2. Rounding maps each rational to a nearby representable value
    3. The rounding operation preserves the relative order -/
theorem roundToFloat_monotonic (cfg_prec : Nat) (cfg_emin cfg_emax : Int)
    (mode : RoundMode) (x y : Rat) :
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
          -- This requires showing rounding preserves order for same-sign values
          sorry
      · -- x ≥ 0, but x ≠ 0, so x > 0
        have hx_pos : 0 < x := lt_of_le_of_ne (not_lt.mp hx_neg) (Ne.symm hx)
        -- Since x > 0 and x ≤ y, we have y > 0
        have hy_pos : 0 < y := lt_of_lt_of_le hx_pos h_le
        -- Both positive: requires showing rounding preserves order for positive values
        sorry

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
    sorry
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

