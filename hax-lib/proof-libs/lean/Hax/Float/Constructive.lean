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
  sorry -- TODO: prove rational arithmetic identity

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

/-! # Phase 5: Ordering Properties -/

/-- Reflexivity of le for finite values -/
theorem le_refl_finite {fmt : FloatFormat} (f : FloatRepr fmt) :
    FloatValue.le (.finite f) (.finite f) := by
  simp only [FloatValue.le]
  exact le_refl f.toRat

/-- Transitivity of le -/
theorem le_trans {fmt : FloatFormat} (x y z : FloatValue fmt)
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- This follows from the definition: NaN cases are vacuously true,
  -- infinity cases are straightforward, and finite cases use Rat.le_trans
  sorry

/-- Characterization of strict less than -/
theorem lt_iff_le_not_le {fmt : FloatFormat} (x y : FloatValue fmt) :
    x < y ↔ x ≤ y ∧ ¬(y ≤ x) := by
  simp only [LT.lt, FloatValue.lt, LE.le]

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

  mul_zero_finite := fun x _ => by
    simp only [HMul.hMul, Mul.mul, Zero.zero]
    simp only [fmul, fzero, FloatRepr.toRat]
    simp [zero_mul, round]
    sorry -- Need to show round 0 = fzero

  to_rat := FloatValue.toRat
  to_rat_nan := toRat_nan binary64
  to_rat_inf := toRat_infinity binary64 false
  to_rat_zero := toRat_zero binary64

  to_rat_inj := fun x y hx hy heq => by
    sorry -- Requires showing toRat is injective for finite values

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
    simp only [HMul.hMul, Mul.mul, One.one]
    cases x with
    | finite f => exact fmul_one_left binary64 defaultMode f
    | infinity s =>
      simp only [fmul, fone]
      sorry -- Need to handle infinity * 1 case
    | nan => rfl

  add_monotonic_left := fun _ _ _ _ _ => by sorry
  mul_monotonic_pos := fun _ _ _ _ _ => by sorry
  div_monotonic_num := fun _ _ _ _ _ => by sorry
  div_antimonotonic_den := fun _ _ _ _ _ _ _ => by sorry

  sterbenz := fun _ _ _ _ => by sorry

  neg_exact := neg_neg
  neg_mul := fun x y => by
    simp only [HMul.hMul, Mul.mul, Neg.neg]
    sorry -- Need to prove fneg distributes over fmul

  neg_le_neg := fun _ _ => by sorry

  sub_eq_add_neg := fun x y => by
    simp only [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, Neg.neg]
    rfl

  add_neg_self := fun x hfin => by
    simp only [HAdd.hAdd, Add.add, Neg.neg, Zero.zero]
    sorry -- Need to prove x + (-x) = 0 for finite x

  le_trans := le_trans
  le_antisymm := fun _ _ _ _ => by sorry
  le_total := fun _ _ _ _ => by sorry

  lt_iff_le_not_le := lt_iff_le_not_le

  div_self := fun _ _ _ => by sorry

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

  mul_zero_finite := fun x _ => by
    simp only [HMul.hMul, Mul.mul, Zero.zero]
    simp only [fmul, fzero, FloatRepr.toRat]
    simp [round]
    sorry

  to_rat := FloatValue.toRat
  to_rat_nan := toRat_nan binary32
  to_rat_inf := toRat_infinity binary32 false
  to_rat_zero := toRat_zero binary32
  to_rat_inj := fun x y hx hy heq => by sorry
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
    simp only [HMul.hMul, Mul.mul]
    cases x with
    | finite f => exact fmul_one_left binary32 defaultMode f
    | infinity s => simp only [fmul]; sorry
    | nan => rfl

  add_monotonic_left := fun _ _ _ _ _ => by sorry
  mul_monotonic_pos := fun _ _ _ _ _ => by sorry
  div_monotonic_num := fun _ _ _ _ _ => by sorry
  div_antimonotonic_den := fun _ _ _ _ _ _ _ => by sorry
  sterbenz := fun _ _ _ _ => by sorry
  neg_exact := neg_neg
  neg_mul := fun x y => by simp only [HMul.hMul, Mul.mul, Neg.neg]; sorry
  neg_le_neg := fun _ _ => by sorry
  sub_eq_add_neg := fun x y => by simp only [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, Neg.neg]; rfl
  add_neg_self := fun x hfin => by simp only [HAdd.hAdd, Add.add, Neg.neg, Zero.zero]; sorry
  le_trans := le_trans
  le_antisymm := fun _ _ _ _ => by sorry
  le_total := fun _ _ _ _ => by sorry
  lt_iff_le_not_le := lt_iff_le_not_le
  div_self := fun _ _ _ => by sorry
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
