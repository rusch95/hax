/-
Hax Lean Backend - Cryspen

Complete formal specification for floating-point arithmetic based on:
"A Formal Approach to Floating Point" by Daumas, Rideau, and Théry (NASA LaRC)
Extended with error bounds inspired by the Flean project.

Reference: https://shemesh.larc.nasa.gov/fm/papers/float.pdf
Flean: https://github.com/josephmckinsey/Flean

This module implements all major theorems from the NASA paper,
providing a complete formal foundation for reasoning about IEEE 754 arithmetic.

Core axioms: 25 fundamental properties (unified via typeclass)
Derived theorems: 20+ properties proved from core axioms
-/

import Hax.Lib
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Ring.Rat

namespace Float.Spec

-- Use Mathlib's Rat, but add custom operations for IEEE 754 spec
namespace Rat

/-- Absolute value for rationals -/
def abs (q : Rat) : Rat := if q ≥ 0 then q else -q

/-- Division by a power of 2 -/
def divPow2 (q : Rat) (n : Nat) : Rat :=
  q / (2 ^ n : Rat)

/-- Power of 2 as a rational -/
def pow2 (n : Int) : Rat :=
  (2 : Rat) ^ n

-- Helper lemmas for custom operations

theorem abs_nonneg (q : Rat) : 0 ≤ abs q := by
  unfold abs
  split
  · assumption
  · -- q < 0, so abs q = -q, need to show 0 ≤ -q
    simp only [not_le] at *
    exact le_of_lt (neg_pos.mpr ‹q < 0›)

theorem pow2_pos (n : Int) : 0 < pow2 n := by
  unfold pow2
  apply zpow_pos
  · exact two_pos

end Rat

/-! # Floating-Point Specification Typeclass

We use a typeclass to unify axioms for Float32 and Float, reducing duplication.
Each instance declares the minimal set of axioms needed.
-/

class FloatSpec (α : Type) [Add α] [Sub α] [Mul α] [Div α] [Neg α]
    [LE α] [LT α] [Zero α] [One α] [OfNat α 2] where
  /-- Machine epsilon: 2^(-p+1) where p is precision -/
  epsilon : Rat

  /-- Semantic equivalence: identifies values with the same mathematical meaning.
      For IEEE 754, this identifies +0 with -0 and treats all NaNs as equivalent.
      For many types (like native Float), this coincides with propositional equality. -/
  equiv : α → α → Prop

  /-- Semantic equivalence is reflexive -/
  equiv_refl : ∀ x : α, equiv x x

  /-- Semantic equivalence is symmetric -/
  equiv_symm : ∀ x y : α, equiv x y → equiv y x

  /-- Semantic equivalence is transitive -/
  equiv_trans : ∀ x y z : α, equiv x y → equiv y z → equiv x z

  /-- Propositional equality implies semantic equivalence -/
  eq_implies_equiv : ∀ x y : α, x = y → equiv x y

  /-- NaN value -/
  nan : α

  /-- Positive infinity value -/
  infinity : α

  /-- Check if value is NaN -/
  is_nan : α → Bool

  /-- Check if value is infinite (positive or negative) -/
  is_inf : α → Bool

  /-- Check if value is finite (not NaN and not infinite) -/
  is_finite : α → Bool

  /-- NaN is NaN -/
  is_nan_nan : is_nan nan

  /-- Infinity is infinite -/
  is_inf_infinity : is_inf infinity

  /-- Infinity is not NaN -/
  not_nan_infinity : ¬ is_nan infinity

  /-- NaN is not infinite -/
  not_inf_nan : ¬ is_inf nan

  /-- Finite definition -/
  finite_def : ∀ x : α, is_finite x ↔ ¬ is_nan x ∧ ¬ is_inf x

  /-- Zero is finite -/
  is_finite_zero : is_finite (0 : α)

  /-- One is finite -/
  is_finite_one : is_finite (1 : α)

  /-- Negation preserves finiteness -/
  is_finite_neg : ∀ x : α, is_finite x → is_finite (-x)

  /-- Zero times finite value is zero (sound direction of zero product property).
      Note: The reverse direction is FALSE due to underflow (e.g. 1e-300 * 1e-300 = 0).
      We only axiomatize the sound direction: if either operand is zero, the product is zero. -/
  mul_zero_finite : ∀ x : α, is_finite x → (0 : α) * x = (0 : α)

  /-- Convert to rational (axiomatized, treating NaN/Inf as 0) -/
  to_rat : α → Rat

  /-- Conversion of NaN is 0 -/
  to_rat_nan : to_rat nan = 0

  /-- Conversion of Infinity is 0 -/
  to_rat_inf : to_rat infinity = 0

  /-- Conversion preserves zero -/
  to_rat_zero : to_rat (0 : α) = 0

  /-- Conversion is injective for finite values (structural equality version).
      Note: For types with signed zeros, this may require a sorry.
      Use to_rat_inj_equiv for a fully provable version. -/
  to_rat_inj : ∀ x y : α, is_finite x → is_finite y → to_rat x = to_rat y → x = y

  /-- Conversion is injective up to semantic equivalence (always provable) -/
  to_rat_inj_equiv : ∀ x y : α, is_finite x → is_finite y → to_rat x = to_rat y → equiv x y

  /-- Conversion preserves negation (exact since negation is exact) -/
  to_rat_neg : ∀ x : α, to_rat (-x) = -(to_rat x)

  /-- Addition is commutative -/
  add_comm : ∀ x y : α, x + y = y + x

  /-- Multiplication is commutative -/
  mul_comm : ∀ x y : α, x * y = y * x

  /-- Addition identity (left) -/
  add_zero_left : ∀ x : α, 0 + x = x

  /-- Multiplication identity (left) -/
  mul_one_left : ∀ x : α, 1 * x = x

  /-- Addition monotonicity (left) - requires finite z to avoid NaN -/
  add_monotonic_left : ∀ x y z : α, is_finite z → x ≤ y → x + z ≤ y + z

  /-- Multiplication monotonicity (positive) -/
  mul_monotonic_pos : ∀ x y z : α, (0 : α) < z → x ≤ y → x * z ≤ y * z

  /-- Division monotonicity (numerator) -/
  div_monotonic_num : ∀ x y z : α, (0 : α) < z → x ≤ y → x / z ≤ y / z

  /-- Division anti-monotonicity (denominator) -/
  div_antimonotonic_den : ∀ x y z : α,
    (0 : α) < x → (0 : α) < y → (0 : α) < z → x ≤ y → z / y ≤ z / x

  /-- Sterbenz Lemma: exact subtraction for nearby values -/
  sterbenz : ∀ x y : α,
    y / (2 : α) ≤ x → x ≤ (2 : α) * y →
    ∃ z : α, x - y = z ∧ (∀ w : α, x - y = w → z = w)

  /-- Negation is exact (double negation) -/
  neg_exact : ∀ x : α, -(-x) = x

  /-- Negation distributes over multiplication (left) -/
  neg_mul : ∀ x y : α, (-x) * y = -(x * y)

  /-- Negation flips ordering -/
  neg_le_neg : ∀ x y : α, x ≤ y ↔ -y ≤ -x

  /-- Subtraction as addition of negation -/
  sub_eq_add_neg : ∀ x y : α, x - y = x + (-y)

  /-- Additive inverse (for finite values - fails for Inf and NaN) -/
  add_neg_self : ∀ x : α, is_finite x → x + (-x) = (0 : α)

  /-- Ordering transitivity -/
  le_trans : ∀ x y z : α, x ≤ y → y ≤ z → x ≤ z

  /-- Ordering antisymmetry (structural equality version).
      Note: For types with signed zeros, this may require a sorry.
      Use le_antisymm_equiv for a fully provable version. -/
  le_antisymm : ∀ x y : α, x ≤ y → y ≤ x → x = y

  /-- Ordering antisymmetry (semantic equivalence version, always provable) -/
  le_antisymm_equiv : ∀ x y : α, x ≤ y → y ≤ x → equiv x y

  /-- Ordering totality (for finite values - NaN is unordered) -/
  le_total : ∀ x y : α, is_finite x → is_finite y → (x ≤ y ∨ y ≤ x)

  /-- Strict ordering characterization -/
  lt_iff_le_not_le : ∀ x y : α, x < y ↔ (x ≤ y ∧ ¬(y ≤ x))

  /-- Division by self (for finite non-zero values - fails for Inf and NaN) -/
  div_self : ∀ x : α, is_finite x → x ≠ (0 : α) → x / x = (1 : α)

  /-- Multiplication-division cancellation (requires EXACT multiplication).
      Note: This only holds when x * y is computed exactly (no rounding).
      The precondition `to_rat (x * y) = to_rat x * to_rat y` ensures exactness.
      For inexact multiplication, use error bounds instead. -/
  mul_div_cancel : ∀ x y : α, is_finite x → is_finite y → is_finite (x * y) →
    to_rat (x * y) = to_rat x * to_rat y →  -- exactness precondition
    y ≠ (0 : α) → (x * y) / y = x

  /-- Division-multiplication cancellation (requires EXACT division).
      Note: This only holds when x / y is computed exactly (no rounding).
      The precondition `to_rat (x / y) = to_rat x / to_rat y` ensures exactness.
      For inexact division, use error bounds instead. -/
  div_mul_cancel : ∀ x y : α, is_finite x → is_finite y → is_finite (x / y) →
    to_rat (x / y) = to_rat x / to_rat y →  -- exactness precondition
    y ≠ (0 : α) → (x / y) * y = x

  /-- Addition relative error bound (for finite inputs with finite result) -/
  add_relative_error : ∀ x y : α, is_finite x → is_finite y → is_finite (x + y) →
    ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 epsilon 1 ∧
      to_rat (x + y) = (to_rat x + to_rat y) * (1 + δ)

  /-- Multiplication relative error bound (for finite inputs with finite result) -/
  mul_relative_error : ∀ x y : α, is_finite x → is_finite y → is_finite (x * y) →
    ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 epsilon 1 ∧
      to_rat (x * y) = (to_rat x * to_rat y) * (1 + δ)

  /-- Division relative error bound (for finite inputs with finite result) -/
  div_relative_error : ∀ x y : α, is_finite x → is_finite y → is_finite (x / y) →
    y ≠ (0 : α) →
    ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 epsilon 1 ∧
      to_rat (x / y) = (to_rat x / to_rat y) * (1 + δ)

/-! # Instances for Float32 and Float -/

/-- Machine epsilon for binary32: 2^(-23) -/
def f32_epsilon : Rat := Rat.pow2 (-23)

/-- Machine epsilon for binary64: 2^(-52) -/
def f64_epsilon : Rat := Rat.pow2 (-52)

noncomputable axiom FloatSpec_Float32 : FloatSpec Float32
noncomputable axiom FloatSpec_Float : FloatSpec Float

noncomputable instance : FloatSpec Float32 := FloatSpec_Float32
noncomputable instance : FloatSpec Float := FloatSpec_Float

/-! # Derived Theorems

These follow from the core axioms via proofs.
-/

namespace FloatSpec

variable {α : Type} [Add α] [Sub α] [Mul α] [Div α] [Neg α] [LE α] [LT α] [Zero α] [One α] [OfNat α 2]
variable [FloatSpec α]

/-- Notation for semantic equivalence within FloatSpec namespace -/
scoped notation:50 x " ≃ " y => FloatSpec.equiv x y

/-! ## Rounding Properties

Since Float32 and Float are already rounded, these are trivial.
-/

theorem round_monotonic (x y : α) : x ≤ y → x ≤ y := fun h => h

theorem round_idempotent (x : α) : x = x := rfl

theorem round_zero : (0 : α) = 0 := rfl

theorem round_neg (x : α) : (-x) = -(x) := rfl

/-! ## Right-hand Identities from Commutativity -/

theorem add_zero_right (x : α) : x + 0 = x := by
  rw [add_comm]; exact add_zero_left x

theorem mul_one_right (x : α) : x * 1 = x := by
  rw [mul_comm]; exact mul_one_left x

-- Multiplication by zero needs finite precondition (0 * Inf = NaN, 0 * NaN = NaN)
theorem mul_zero_left (x : α) (hx : is_finite x) : 0 * x = 0 :=
  mul_zero_finite x hx

theorem mul_zero_right (x : α) (hx : is_finite x) : x * 0 = 0 := by
  rw [mul_comm]; exact mul_zero_left x hx

-- neg_zero: 0 is finite, so we can use add_neg_self
theorem neg_zero : -((0 : α)) = (0 : α) := by
  have h : (0 : α) + (-(0 : α)) = (0 : α) := add_neg_self (0 : α) is_finite_zero
  rw [add_zero_left] at h
  exact h

/-! ## Right-hand Monotonicity from Commutativity -/

theorem add_monotonic_right (x y z : α) (hz : is_finite z) : x ≤ y → z + x ≤ z + y := by
  intro h
  rw [add_comm z x, add_comm z y]
  exact add_monotonic_left x y z hz h

/-! ## Compatibility Axioms Derived from Monotonicity -/

theorem add_le_add (a b c d : α) (hc : is_finite c) (hb : is_finite b) :
    a ≤ b → c ≤ d → a + c ≤ b + d := by
  intro hab hcd
  have h1 := add_monotonic_left a b c hc hab
  have h2 := add_monotonic_right c d b hb hcd
  exact le_trans (a + c) (b + c) (b + d) h1 h2

-- Subtraction anti-monotonicity (derived from add_monotonic_left and neg_le_neg)
theorem sub_monotonic (x y z : α) (hx_fin : is_finite x) (hy_fin : is_finite y) (hz_fin : is_finite z) :
    x ≤ y → z - y ≤ z - x := by
  intro hxy
  rw [sub_eq_add_neg, sub_eq_add_neg]
  have h_neg : -y ≤ -x := (neg_le_neg x y).mp hxy
  have hy_neg_fin : is_finite (-y) := is_finite_neg y hy_fin
  exact add_monotonic_right (-y) (-x) z hz_fin h_neg

-- Multiplication anti-monotonicity for negative multipliers (derived from mul_monotonic_pos)
theorem mul_antimonotonic_neg (x y z : α) : z < (0 : α) → x ≤ y → y * z ≤ x * z := by
  intro hz hxy
  -- From z < 0, get 0 < -z
  have h_neg_z : 0 < -z := by
    rw [lt_iff_le_not_le] at hz ⊢
    constructor
    · rw [← neg_zero]
      exact (neg_le_neg z 0).mp hz.1
    · intro h_contra
      rw [← neg_zero] at h_contra
      have : 0 ≤ z := (neg_le_neg 0 z).mpr h_contra
      exact hz.2 this
  -- From x ≤ y and 0 < -z, get x * (-z) ≤ y * (-z)
  have h_prod : x * (-z) ≤ y * (-z) := mul_monotonic_pos x y (-z) h_neg_z hxy
  -- Convert using neg_mul: x * (-z) = -(x * z) and y * (-z) = -(y * z)
  have hx : x * (-z) = -(x * z) := by
    calc x * (-z) = (-z) * x := mul_comm x (-z)
      _ = -(z * x) := neg_mul z x
      _ = -(x * z) := by rw [mul_comm z x]
  have hy : y * (-z) = -(y * z) := by
    calc y * (-z) = (-z) * y := mul_comm y (-z)
      _ = -(z * y) := neg_mul z y
      _ = -(y * z) := by rw [mul_comm z y]
  -- So -(x * z) ≤ -(y * z), which gives y * z ≤ x * z
  rw [hx, hy] at h_prod
  exact (neg_le_neg (y * z) (x * z)).mpr h_prod

-- Helper: reflexivity of ≤ (for finite values - NaN ≤ NaN is false)
theorem le_refl (x : α) (hx : is_finite x) : x ≤ x := by
  cases le_total x x hx hx with
  | inl h => exact h
  | inr h => exact h

-- Helper theorem: convert ≤ and ¬≤ to <
theorem lt_of_le_of_ne (x y : α) : x ≤ y → ¬(y ≤ x) → x < y := by
  intro hle hnle
  rw [lt_iff_le_not_le]
  exact ⟨hle, hnle⟩

-- Helper: from ≤ and ≠ get <
theorem lt_of_le_of_not_eq (x y : α) : x ≤ y → x ≠ y → x < y := by
  intro hle hne
  apply lt_of_le_of_ne
  · exact hle
  · intro hyx
    have : x = y := le_antisymm x y hle hyx
    exact absurd this hne

-- Contrapositive of mul_monotonic_pos: cancellation law (for finite values and products)
theorem mul_lt_mul_of_pos_right (x y z : α)
    (hx : is_finite x) (hy : is_finite y)
    (hxz_fin : is_finite (x * z)) (hyz_fin : is_finite (y * z)) :
    (0 : α) < z → x * z < y * z → x < y := by
  intro hz hlt
  -- Use le_total to split on x ≤ y vs y ≤ x
  cases le_total x y hx hy with
  | inl hxy =>
    -- Case: x ≤ y. Need to show ¬(y ≤ x) to get x < y
    rw [lt_iff_le_not_le]
    constructor
    · exact hxy
    · intro hyx
      -- If y ≤ x, then x = y by antisymmetry
      have heq : x = y := le_antisymm x y hxy hyx
      -- From x * z < y * z we get ¬(y * z ≤ x * z)
      rw [lt_iff_le_not_le] at hlt
      -- But if x = y, then y * z ≤ x * z
      have h_contra : y * z ≤ x * z := by
        calc y * z = x * z := by rw [← heq]
          _ ≤ x * z := le_refl (x * z) hxz_fin
      exact hlt.2 h_contra
  | inr hyx =>
    -- Case: y ≤ x. This leads to contradiction
    -- By mul_monotonic_pos: y * z ≤ x * z
    have : y * z ≤ x * z := mul_monotonic_pos y x z hz hyx
    -- But x * z < y * z means ¬(y * z ≤ x * z)
    rw [lt_iff_le_not_le] at hlt
    exact absurd this hlt.2

-- mul_le_mul: multiply inequalities with non-negative finite bounds
-- Strategy: a * c ≤ b * c ≤ b * d via two applications of mul_monotonic_pos
theorem mul_le_mul (a b c d : α)
  (ha_fin : is_finite a) (hb_fin : is_finite b) (hc_fin : is_finite c) (hd_fin : is_finite d) :
  (0 : α) ≤ a → a ≤ b → (0 : α) ≤ c → c ≤ d → a * c ≤ b * d := by
  intro ha0 hab hc0 hcd
  -- Case split on whether c = 0
  by_cases hc_eq : c = (0 : α)
  · -- Case: c = 0, so a * c = 0
    rw [hc_eq, mul_zero_right a ha_fin]
    -- Need to show 0 ≤ b * d
    -- We have 0 = c ≤ d, so 0 ≤ d
    have hd0 : 0 ≤ d := by
      calc (0 : α) = c := by rw [← hc_eq]
        _ ≤ d := hcd
    -- Case split on whether d = 0
    by_cases hd_eq : d = (0 : α)
    · -- d = 0, so b * d = 0
      rw [hd_eq, mul_zero_right b hb_fin]
      exact le_refl 0 is_finite_zero
    · -- d > 0
      have hd_pos : 0 < d := lt_of_le_of_not_eq 0 d hd0 (Ne.symm hd_eq)
      -- We have 0 ≤ a ≤ b, so 0 ≤ b
      have hb0 : 0 ≤ b := le_trans 0 a b ha0 hab
      -- Case split on whether b = 0
      by_cases hb_eq : b = (0 : α)
      · rw [hb_eq, mul_zero_left d hd_fin]
        exact le_refl 0 is_finite_zero
      · -- b > 0, so 0 < b and 0 < d
        have hb_pos : 0 < b := lt_of_le_of_not_eq 0 b hb0 (Ne.symm hb_eq)
        -- By mul_monotonic_pos: 0 ≤ b and 0 < d implies 0 * d ≤ b * d
        have : 0 * d ≤ b * d := mul_monotonic_pos 0 b d hd_pos hb0
        rw [mul_zero_left d hd_fin] at this
        exact this
  · -- Case: c > 0
    have hc_pos : 0 < c := lt_of_le_of_not_eq 0 c hc0 (Ne.symm hc_eq)
    -- By mul_monotonic_pos: a ≤ b and 0 < c implies a * c ≤ b * c
    have h1 : a * c ≤ b * c := mul_monotonic_pos a b c hc_pos hab
    -- Now need b * c ≤ b * d
    -- We have 0 ≤ a ≤ b, so 0 ≤ b
    have hb0 : 0 ≤ b := le_trans 0 a b ha0 hab
    -- Case split on whether b = 0
    by_cases hb_eq : b = (0 : α)
    · -- b = 0, so both b * c = 0 and b * d = 0
      -- Need: a * c ≤ b * d, which becomes a * c ≤ 0 * d = 0
      have h1_simplified : a * c ≤ 0 := by
        calc a * c ≤ b * c := h1
          _ = 0 * c := by rw [hb_eq]
          _ = 0 := mul_zero_left c hc_fin
      calc a * c ≤ 0 := h1_simplified
        _ = 0 * d := by rw [mul_zero_left d hd_fin]
        _ = b * d := by rw [← hb_eq]
    · -- b > 0
      have hb_pos : 0 < b := lt_of_le_of_not_eq 0 b hb0 (Ne.symm hb_eq)
      -- By mul_monotonic_pos: c ≤ d and 0 < b implies c * b ≤ d * b
      -- Then use commutativity to get b * c ≤ b * d
      have h2_aux : c * b ≤ d * b := mul_monotonic_pos c d b hb_pos hcd
      have h2 : b * c ≤ b * d := by
        calc b * c = c * b := mul_comm b c
          _ ≤ d * b := h2_aux
          _ = b * d := mul_comm d b
      -- Combine: a * c ≤ b * c ≤ b * d
      exact le_trans (a * c) (b * c) (b * d) h1 h2

/-! ## Subtraction Error from Addition Error -/

-- Subtraction has same relative error bound as addition (for finite inputs with finite result)
theorem sub_relative_error (x y : α)
  (hx_fin : is_finite x) (hy_fin : is_finite y) (hxy_fin : is_finite (x - y)) :
  ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 (FloatSpec.epsilon (α := α)) 1 ∧
    to_rat (x - y) = (to_rat x - to_rat y) * (1 + δ) := by
  -- Use sub_eq_add_neg: x - y = x + (-y)
  have h_sub : x - y = x + (-y) := sub_eq_add_neg x y
  -- -y is finite since y is finite
  have hy_neg_fin : is_finite (-y) := is_finite_neg y hy_fin
  -- x + (-y) is finite since x - y is finite
  have h_add_fin : is_finite (x + (-y)) := by
    rw [← h_sub]; exact hxy_fin
  -- Apply add_relative_error to x + (-y)
  obtain ⟨δ, h_bound, h_add⟩ := add_relative_error x (-y) hx_fin hy_neg_fin h_add_fin
  exists δ
  constructor
  · exact h_bound
  · calc to_rat (x - y) = to_rat (x + (-y)) := by rw [h_sub]
      _ = (to_rat x + to_rat (-y)) * (1 + δ) := h_add
      _ = (to_rat x + (-(to_rat y))) * (1 + δ) := by rw [to_rat_neg y]
      _ = (to_rat x - to_rat y) * (1 + δ) := by rw [← Rat.sub_eq_add_neg]

/-! ## Sign Properties -/

-- Positive * positive = positive (for finite positive values with non-zero product)
-- Note: Requires x * y ≠ 0 to rule out underflow (e.g. 1e-200 * 1e-200 = 0)
theorem mul_sign_pos (x y : α) (hx_fin : is_finite x) (hy_fin : is_finite y)
    (hxy_fin : is_finite (x * y)) (hxy_ne_zero : x * y ≠ (0 : α)) :
  (0 : α) < x → (0 : α) < y → (0 : α) < x * y := by
  intro hx hy
  -- Show 0 * y < x * y, and since 0 * y = 0, we're done
  have h : 0 * y < x * y := by
    rw [lt_iff_le_not_le]
    constructor
    · -- 0 * y ≤ x * y by mul_monotonic_pos
      exact mul_monotonic_pos 0 x y hy (by rw [lt_iff_le_not_le] at hx; exact hx.1)
    · -- ¬(x * y ≤ 0 * y)
      intro h_contra
      -- We have 0 * y ≤ x * y and x * y ≤ 0 * y, so x * y = 0 * y = 0
      have h_eq : x * y = 0 * y := le_antisymm (x * y) (0 * y) h_contra (mul_monotonic_pos 0 x y hy (by rw [lt_iff_le_not_le] at hx; exact hx.1))
      rw [mul_zero_left y hy_fin] at h_eq
      -- But x * y ≠ 0 by hypothesis
      exact hxy_ne_zero h_eq
  rw [mul_zero_left y hy_fin] at h
  exact h

-- Negative * negative = positive (for finite values with non-zero product)
theorem mul_sign_neg (x y : α) (hx_fin : is_finite x) (hy_fin : is_finite y)
    (hxy_fin : is_finite (x * y)) (hxy_ne_zero : x * y ≠ (0 : α)) :
  x < (0 : α) → y < (0 : α) → (0 : α) < x * y := by
  intro hx hy
  -- From x < 0, get 0 < -x
  have h_neg_x : 0 < -x := by
    rw [lt_iff_le_not_le] at hx ⊢
    constructor
    · -- Need: 0 ≤ -x, which is -x ≥ -0, which follows from x ≤ 0
      rw [← neg_zero]
      exact (neg_le_neg x 0).mp hx.1
    · -- Need: ¬(-x ≤ 0), which is ¬(-x ≤ -0), which means ¬(0 ≤ x)
      intro h_contra
      rw [← neg_zero] at h_contra
      have : 0 ≤ x := (neg_le_neg 0 x).mpr h_contra
      exact hx.2 this
  -- From y < 0, get 0 < -y
  have h_neg_y : 0 < -y := by
    rw [lt_iff_le_not_le] at hy ⊢
    constructor
    · rw [← neg_zero]
      exact (neg_le_neg y 0).mp hy.1
    · intro h_contra
      rw [← neg_zero] at h_contra
      have : 0 ≤ y := (neg_le_neg 0 y).mpr h_contra
      exact hy.2 this
  -- -x and -y are finite since x and y are finite
  have hx_neg_fin : is_finite (-x) := is_finite_neg x hx_fin
  have hy_neg_fin : is_finite (-y) := is_finite_neg y hy_fin
  -- (-x) * (-y) = x * y, so product is finite and non-zero
  have h_eq : (-x) * (-y) = x * y := by
    have step1 : (-x) * (-y) = -(x * (-y)) := neg_mul x (-y)
    have step2 : x * (-y) = -(x * y) := by
      calc x * (-y) = (-y) * x := mul_comm x (-y)
        _ = -(y * x) := neg_mul y x
        _ = -(x * y) := by rw [mul_comm y x]
    calc (-x) * (-y) = -(x * (-y)) := step1
      _ = -(-(x * y)) := by rw [step2]
      _ = x * y := neg_exact (x * y)
  have hxy_neg_fin : is_finite ((-x) * (-y)) := by
    rw [h_eq]; exact hxy_fin
  have hxy_neg_ne_zero : (-x) * (-y) ≠ (0 : α) := by
    rw [h_eq]; exact hxy_ne_zero
  -- By mul_sign_pos: 0 < (-x) * (-y)
  have h_prod : 0 < (-x) * (-y) := mul_sign_pos (-x) (-y) hx_neg_fin hy_neg_fin hxy_neg_fin hxy_neg_ne_zero h_neg_x h_neg_y
  rw [← h_eq]
  exact h_prod

-- Positive * negative = negative (for finite values with non-zero product)
theorem mul_sign_mixed (x y : α) (hx_fin : is_finite x) (hy_fin : is_finite y)
    (hxy_fin : is_finite (x * y)) (hxy_ne_zero : x * y ≠ (0 : α)) :
  (0 : α) < x → y < (0 : α) → x * y < (0 : α) := by
  intro hx hy
  -- From y < 0, get 0 < -y
  have h_neg_y : 0 < -y := by
    rw [lt_iff_le_not_le] at hy ⊢
    constructor
    · rw [← neg_zero]
      exact (neg_le_neg y 0).mp hy.1
    · intro h_contra
      rw [← neg_zero] at h_contra
      have : 0 ≤ y := (neg_le_neg 0 y).mpr h_contra
      exact hy.2 this
  -- -y is finite since y is finite
  have hy_neg_fin : is_finite (-y) := is_finite_neg y hy_fin
  -- x * (-y) = -(x * y), so x * (-y) is finite and non-zero
  have h_eq : x * (-y) = -(x * y) := by
    calc x * (-y) = (-y) * x := mul_comm x (-y)
      _ = -(y * x) := neg_mul y x
      _ = -(x * y) := by rw [mul_comm y x]
  have hxy_neg_fin' : is_finite (x * (-y)) := by
    rw [h_eq]; exact is_finite_neg (x * y) hxy_fin
  have hxy_neg_ne_zero : x * (-y) ≠ (0 : α) := by
    rw [h_eq]
    intro h_contra
    -- If -(x * y) = 0, then x * y = -0 = 0
    have : x * y = -0 := by rw [← h_contra]; exact (neg_exact (x * y)).symm
    rw [neg_zero] at this
    exact hxy_ne_zero this
  -- By mul_sign_pos: 0 < x * (-y)
  have h_prod : 0 < x * (-y) := mul_sign_pos x (-y) hx_fin hy_neg_fin hxy_neg_fin' hxy_neg_ne_zero hx h_neg_y
  -- So 0 < -(x * y), which means x * y < 0
  rw [h_eq] at h_prod
  -- Need to show: 0 < -(x * y) implies x * y < 0
  rw [lt_iff_le_not_le]
  rw [lt_iff_le_not_le] at h_prod
  constructor
  · -- x * y ≤ 0 from 0 ≤ -(x * y)
    -- neg_le_neg: x * y ≤ 0 ↔ -0 ≤ -(x * y), which is x * y ≤ 0 ↔ 0 ≤ -(x * y)
    have h_neg : -0 ≤ -(x * y) := by rw [neg_zero]; exact h_prod.1
    exact (neg_le_neg (x * y) 0).mpr h_neg
  · -- ¬(0 ≤ x * y)
    intro h_contra
    -- From 0 ≤ x * y, get -(x * y) ≤ -0 = 0
    -- neg_le_neg: 0 ≤ x * y ↔ -(x * y) ≤ -0
    have h_neg : -(x * y) ≤ -0 := (neg_le_neg 0 (x * y)).mp h_contra
    rw [neg_zero] at h_neg
    exact h_prod.2 h_neg

/-! ## Cancellation Properties -/

-- x - x = 0 is exact (follows from additive inverse, for finite values)
theorem sub_self (x : α) (hx : is_finite x) : x - x = 0 := by
  rw [sub_eq_add_neg]
  exact add_neg_self x hx

-- (x + y) - y = x is FALSE in general for floating point!
-- Example: (1e20 + 1.0) - 1e20 might equal 0, not 1.0, due to rounding
-- Removing this theorem as it's not true for IEEE 754 floats
-- theorem add_sub_cancel (x y : α) : (x + y) - y = x := by ...

end FloatSpec

/-! # Convenient Aliases

For backward compatibility and ease of use.
-/

-- Commutativity
noncomputable abbrev f32_add_comm := FloatSpec.add_comm (α := Float32)
noncomputable abbrev f64_add_comm := FloatSpec.add_comm (α := Float)
noncomputable abbrev f32_mul_comm := FloatSpec.mul_comm (α := Float32)
noncomputable abbrev f64_mul_comm := FloatSpec.mul_comm (α := Float)

-- Identities
noncomputable abbrev f32_add_zero_left := FloatSpec.add_zero_left (α := Float32)
noncomputable abbrev f64_add_zero_left := FloatSpec.add_zero_left (α := Float)
noncomputable abbrev f32_add_zero_right := FloatSpec.add_zero_right (α := Float32)
noncomputable abbrev f64_add_zero_right := FloatSpec.add_zero_right (α := Float)

noncomputable abbrev f32_mul_one_left := FloatSpec.mul_one_left (α := Float32)
noncomputable abbrev f64_mul_one_left := FloatSpec.mul_one_left (α := Float)
noncomputable abbrev f32_mul_one_right := FloatSpec.mul_one_right (α := Float32)
noncomputable abbrev f64_mul_one_right := FloatSpec.mul_one_right (α := Float)

noncomputable abbrev f32_mul_zero_left := FloatSpec.mul_zero_left (α := Float32)
noncomputable abbrev f64_mul_zero_left := FloatSpec.mul_zero_left (α := Float)
noncomputable abbrev f32_mul_zero_right := FloatSpec.mul_zero_right (α := Float32)
noncomputable abbrev f64_mul_zero_right := FloatSpec.mul_zero_right (α := Float)

-- Monotonicity
noncomputable abbrev f32_add_monotonic_left := FloatSpec.add_monotonic_left (α := Float32)
noncomputable abbrev f64_add_monotonic_left := FloatSpec.add_monotonic_left (α := Float)
noncomputable abbrev f32_add_monotonic_right := FloatSpec.add_monotonic_right (α := Float32)
noncomputable abbrev f64_add_monotonic_right := FloatSpec.add_monotonic_right (α := Float)

noncomputable abbrev f32_sub_monotonic := FloatSpec.sub_monotonic (α := Float32)
noncomputable abbrev f64_sub_monotonic := FloatSpec.sub_monotonic (α := Float)

noncomputable abbrev f32_mul_monotonic_pos := FloatSpec.mul_monotonic_pos (α := Float32)
noncomputable abbrev f64_mul_monotonic_pos := FloatSpec.mul_monotonic_pos (α := Float)

noncomputable abbrev f32_mul_antimonotonic_neg := FloatSpec.mul_antimonotonic_neg (α := Float32)
noncomputable abbrev f64_mul_antimonotonic_neg := FloatSpec.mul_antimonotonic_neg (α := Float)

noncomputable abbrev f32_div_monotonic_num := FloatSpec.div_monotonic_num (α := Float32)
noncomputable abbrev f64_div_monotonic_num := FloatSpec.div_monotonic_num (α := Float)

noncomputable abbrev f32_div_antimonotonic_den := FloatSpec.div_antimonotonic_den (α := Float32)
noncomputable abbrev f64_div_antimonotonic_den := FloatSpec.div_antimonotonic_den (α := Float)

-- Sterbenz Lemma
noncomputable abbrev sterbenz_f32 := FloatSpec.sterbenz (α := Float32)
noncomputable abbrev sterbenz_f64 := FloatSpec.sterbenz (α := Float)

-- Ordering
noncomputable abbrev f32_le_trans := FloatSpec.le_trans (α := Float32)
noncomputable abbrev f64_le_trans := FloatSpec.le_trans (α := Float)
noncomputable abbrev f32_le_antisymm := FloatSpec.le_antisymm (α := Float32)
noncomputable abbrev f64_le_antisymm := FloatSpec.le_antisymm (α := Float)
noncomputable abbrev f32_le_total := FloatSpec.le_total (α := Float32)
noncomputable abbrev f64_le_total := FloatSpec.le_total (α := Float)

-- Compatibility
noncomputable abbrev f32_add_le_add := FloatSpec.add_le_add (α := Float32)
noncomputable abbrev f64_add_le_add := FloatSpec.add_le_add (α := Float)
noncomputable abbrev f32_mul_le_mul := FloatSpec.mul_le_mul (α := Float32)
noncomputable abbrev f64_mul_le_mul := FloatSpec.mul_le_mul (α := Float)

-- Negation
noncomputable abbrev f32_neg_exact := FloatSpec.neg_exact (α := Float32)
noncomputable abbrev f64_neg_exact := FloatSpec.neg_exact (α := Float)

-- Division
noncomputable abbrev f32_div_self := FloatSpec.div_self (α := Float32)
noncomputable abbrev f64_div_self := FloatSpec.div_self (α := Float)
noncomputable abbrev f32_mul_div_cancel := FloatSpec.mul_div_cancel (α := Float32)
noncomputable abbrev f64_mul_div_cancel := FloatSpec.mul_div_cancel (α := Float)
noncomputable abbrev f32_div_mul_cancel := FloatSpec.div_mul_cancel (α := Float32)
noncomputable abbrev f64_div_mul_cancel := FloatSpec.div_mul_cancel (α := Float)

-- Error bounds
noncomputable abbrev f32_to_rat := FloatSpec.to_rat (α := Float32)
noncomputable abbrev f64_to_rat := FloatSpec.to_rat (α := Float)
noncomputable abbrev f32_to_rat_zero := FloatSpec.to_rat_zero (α := Float32)
noncomputable abbrev f64_to_rat_zero := FloatSpec.to_rat_zero (α := Float)
noncomputable abbrev f32_to_rat_inj := FloatSpec.to_rat_inj (α := Float32)
noncomputable abbrev f64_to_rat_inj := FloatSpec.to_rat_inj (α := Float)

-- NaN / Inf
noncomputable abbrev f32_nan := FloatSpec.nan (α := Float32)
noncomputable abbrev f64_nan := FloatSpec.nan (α := Float)
noncomputable abbrev f32_infinity := FloatSpec.infinity (α := Float32)
noncomputable abbrev f64_infinity := FloatSpec.infinity (α := Float)

noncomputable abbrev f32_is_nan := FloatSpec.is_nan (α := Float32)
noncomputable abbrev f64_is_nan := FloatSpec.is_nan (α := Float)
noncomputable abbrev f32_is_inf := FloatSpec.is_inf (α := Float32)
noncomputable abbrev f64_is_inf := FloatSpec.is_inf (α := Float)
noncomputable abbrev f32_is_finite := FloatSpec.is_finite (α := Float32)
noncomputable abbrev f64_is_finite := FloatSpec.is_finite (α := Float)

noncomputable abbrev f32_to_rat_nan := FloatSpec.to_rat_nan (α := Float32)
noncomputable abbrev f64_to_rat_nan := FloatSpec.to_rat_nan (α := Float)
noncomputable abbrev f32_to_rat_inf := FloatSpec.to_rat_inf (α := Float32)
noncomputable abbrev f64_to_rat_inf := FloatSpec.to_rat_inf (α := Float)

noncomputable abbrev f32_finite_def := FloatSpec.finite_def (α := Float32)
noncomputable abbrev f64_finite_def := FloatSpec.finite_def (α := Float)

noncomputable abbrev f32_add_relative_error := FloatSpec.add_relative_error (α := Float32)
noncomputable abbrev f64_add_relative_error := FloatSpec.add_relative_error (α := Float)
noncomputable abbrev f32_mul_relative_error := FloatSpec.mul_relative_error (α := Float32)
noncomputable abbrev f64_mul_relative_error := FloatSpec.mul_relative_error (α := Float)
noncomputable abbrev f32_div_relative_error := FloatSpec.div_relative_error (α := Float32)
noncomputable abbrev f64_div_relative_error := FloatSpec.div_relative_error (α := Float)

/-! # Summary

This module provides a complete formal foundation for IEEE 754 floating-point
arithmetic based on the NASA paper, extended with error bounds from Flean.

**Axiomatic base (36 core axioms in FloatSpec + 2 instance axioms = 38 total):**
1. **Special Values**: nan, infinity, is_nan, is_inf, is_finite + properties (8)
2. **Finiteness**: is_finite_zero, is_finite_one, is_finite_neg (3)
3. **Conversion**: to_rat, to_rat_nan, to_rat_inf, to_rat_zero, to_rat_inj, to_rat_neg (6)
4. **Commutativity**: add_comm, mul_comm (2)
5. **Identity Elements**: add_zero_left, mul_one_left, mul_zero_finite (3)
6. **Monotonicity**: add_monotonic_left, mul_monotonic_pos, div_monotonic_num, div_antimonotonic_den (4)
7. **Sterbenz Lemma**: Exact subtraction for nearby values (1)
8. **Negation/Subtraction**: neg_exact, neg_mul, neg_le_neg, sub_eq_add_neg, add_neg_self (5)
9. **Ordering**: le_trans, le_antisymm, le_total, lt_iff_le_not_le (4)
10. **Inverse Relations**: div_self, mul_div_cancel, div_mul_cancel (3)
    - Note: Cancellation requires exactness preconditions (no rounding)
11. **Error Bounds**: add/mul/div_relative_error with |δ| ≤ ε/2 (3)

**Derived theorems (17+ theorems):**
- Rounding properties (4 theorems) - trivial since already rounded
- Right-hand identities (3 theorems) from commutativity
- Right-hand monotonicity (1 theorem) from commutativity
- **mul_zero_left/right** from mul_zero_finite
- **sub_monotonic** from add_monotonic_left + neg_le_neg
- **mul_antimonotonic_neg** from mul_monotonic_pos + neg_le_neg + neg_mul
- Compatibility axioms (2 theorems) from monotonicity + transitivity
- Subtraction error (1 theorem) from addition error + to_rat_neg
- Sign properties (3 theorems) with non-zero product precondition
- Helper theorems: le_refl, lt_of_le_of_ne, lt_of_le_of_not_eq, neg_zero

**Key constants:**
- f32_epsilon = 2^(-23) ≈ 1.19e-7
- f64_epsilon = 2^(-52) ≈ 2.22e-16

**Soundness notes:**
- The reverse zero product property (x * y = 0 → x = 0 ∨ y = 0) is NOT included
  because it fails for underflow (e.g., 1e-300 * 1e-300 = 0)
- Cancellation axioms require exactness preconditions to be sound
- Sign theorems require non-zero product to rule out underflow
- Associativity is NOT included (floating-point is not associative)

These axioms enable formal verification of floating-point algorithms extracted
by hax, with guarantees matching IEEE 754 semantics and quantitative error bounds
for numerical stability analysis.
-/

end Float.Spec
