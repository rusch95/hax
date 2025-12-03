import Hax.Lib
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Hax.Float.Spec
import Hax.Float.ExampleHelpers

-- Disable native_decide lint for this file - we intentionally use native_decide
-- to prove computational facts about IEEE 754 Float behavior
set_option linter.style.nativeDecide false

namespace Float.Examples

open Float.Spec
open Float.ExampleHelpers

/-!
# Valid Floating-Point Properties

The following examples demonstrate properties of IEEE 754 floating-point arithmetic
that hold for the `Float` type in Lean (which maps to C `double`).

These are a subset of the axioms from `Spec.lean`, filtered to exclude those
that are false due to Signed Zeros, Infinity, NaN, or Rounding.
-/

variable (x y z : Float)

-- Use the FloatSpec implementation of to_rat
noncomputable abbrev to_rat (x : Float) : Rat := FloatSpec.to_rat x

-- 1. Conversion to Rational
-- Mapping 0 to 0
example : to_rat (0 : Float) = 0 := FloatSpec.to_rat_zero (α := Float)

-- Preserves negation
example : to_rat (-x) = -(to_rat x) := FloatSpec.to_rat_neg x

-- 2. Commutativity
-- Holds for all values including NaN, Inf, -0.0 (assuming symmetric NaN payload propagation)
example : x + y = y + x := FloatSpec.add_comm x y
example : x * y = y * x := FloatSpec.mul_comm x y

-- 3. Identities
-- mul_one_left holds (1 * x = x)
example : (1 : Float) * x = x := FloatSpec.mul_one_left x
example : x * (1 : Float) = x := FloatSpec.mul_one_right x

-- 4. Negation
-- Double negation holds (exact bitwise operation)
example : -(-x) = x := FloatSpec.neg_exact x

-- Negation distributes over multiplication
example : (-x) * y = -(x * y) := FloatSpec.neg_mul x y

-- Subtraction is defined as addition of negation
example : x - y = x + (-y) := FloatSpec.sub_eq_add_neg x y

-- 5. Ordering
-- Transitivity holds
example : x <= y → y <= z → x <= z := FloatSpec.le_trans x y z

-- Strict inequality characterization
example : x < y ↔ x <= y ∧ ¬(y <= x) := FloatSpec.lt_iff_le_not_le x y

-- 6. Error Bounds
-- These are the core properties for numerical analysis.
-- Note: These require finiteness preconditions to avoid NaN/Inf edge cases.

-- Machine epsilon for Float (double precision) is 2^-52
-- Uses FloatSpec.epsilon and Rat.divPow2 from Spec.lean

-- Addition relative error (for finite inputs with finite result)
example (hx : FloatSpec.is_finite x) (hy : FloatSpec.is_finite y) (hxy : FloatSpec.is_finite (x + y)) :
  ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 (FloatSpec.epsilon (α := Float)) 1 ∧
    FloatSpec.to_rat (x + y) = (FloatSpec.to_rat x + FloatSpec.to_rat y) * (1 + δ) :=
  FloatSpec.add_relative_error x y hx hy hxy

-- Multiplication relative error (for finite inputs with finite result)
example (hx : FloatSpec.is_finite x) (hy : FloatSpec.is_finite y) (hxy : FloatSpec.is_finite (x * y)) :
  ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 (FloatSpec.epsilon (α := Float)) 1 ∧
    FloatSpec.to_rat (x * y) = (FloatSpec.to_rat x * FloatSpec.to_rat y) * (1 + δ) :=
  FloatSpec.mul_relative_error x y hx hy hxy

-- Division relative error (for finite inputs with finite result)
example (hx : FloatSpec.is_finite x) (hy : FloatSpec.is_finite y) (hxy : FloatSpec.is_finite (x / y)) :
  y ≠ (0 : Float) →
  ∃ δ : Rat, Rat.abs δ ≤ Rat.divPow2 (FloatSpec.epsilon (α := Float)) 1 ∧
    FloatSpec.to_rat (x / y) = (FloatSpec.to_rat x / FloatSpec.to_rat y) * (1 + δ) :=
  FloatSpec.div_relative_error x y hx hy hxy


/-!
# Invalid Properties (Counterexamples)

The following properties from the original spec are FALSE for IEEE 754.
We prove these using `native_decide` on BEq comparisons since Float
doesn't have DecidableEq for propositional equality.

Note: For Float, `==` follows IEEE 754 semantics (NaN ≠ NaN), while
propositional equality `=` is reflexive. We use BEq where appropriate.
-/

-- 1. Additive Identity fails for NaN (0.0 + NaN ≠ NaN in IEEE comparison)
-- Even though propositionally they might be equal, IEEE comparison says no
example : (0.0 + nan == nan) = false := by native_decide

-- 2. Zero Product fails for Underflow
-- 1e-300 * 1e-300 = 0.0 (underflow), but inputs are non-zero
example : (small * small == 0.0) = true := by native_decide
example : (small == 0.0) = false := by native_decide

-- 3. Reflexivity of <= fails for NaN
-- NaN <= NaN is False in IEEE 754
example : ¬(nan <= nan) := by native_decide

-- 4. Totality of <= fails for NaN
-- Neither NaN <= 0.0 nor 0.0 <= NaN holds
example : ¬(nan <= zero) := by native_decide
example : ¬(zero <= nan) := by native_decide

-- 5. Antisymmetry: 0.0 and -0.0 are both <= each other but == returns true
-- In IEEE 754, 0.0 == -0.0 is true, so antisymmetry holds for signed zeros
example : (zero == neg_zero) = true := by native_decide
example : zero <= neg_zero := by native_decide
example : neg_zero <= zero := by native_decide

-- 6. Additive Inverse fails for Infinity
-- Inf + (-Inf) = NaN, which is not 0.0
example : (inf + (-inf) == 0.0) = false := by native_decide
example : Float.isNaN (inf + (-inf)) = true := by native_decide

-- 7. Division by Self fails for Infinity and NaN
-- Inf / Inf = NaN, NaN / NaN = NaN. Neither equals 1.0
example : (inf / inf == 1.0) = false := by native_decide
example : (nan / nan == 1.0) = false := by native_decide
example : Float.isNaN (inf / inf) = true := by native_decide

-- 8. Multiplication by Zero fails for NaN
-- NaN * 0.0 = NaN, which is not 0.0
example : (nan * 0.0 == 0.0) = false := by native_decide
example : Float.isNaN (nan * 0.0) = true := by native_decide

-- 9. Subtraction of Self fails for Infinity and NaN
-- Inf - Inf = NaN, NaN - NaN = NaN. Neither is 0.0
example : (inf - inf == 0.0) = false := by native_decide
example : (nan - nan == 0.0) = false := by native_decide
example : Float.isNaN (inf - inf) = true := by native_decide

-- 10. Injectivity of to_rat fails for NaN
-- to_rat maps NaN to 0, same as 0.0, but NaN ≠ 0.0
-- (Cannot prove propositionally without DecidableEq, but we can show IEEE comparison)
example : (nan == zero) = false := by native_decide

-- 11. Addition Monotonicity fails with NaN
-- 0.0 <= 0.0 holds, but (0.0 + nan) <= (0.0 + nan) fails because NaN <= NaN is false
example : zero <= zero := by native_decide
example : ¬(zero + nan <= zero + nan) := by native_decide

-- 12. Sterbenz Lemma: the existential formulation trivially holds (z can be anything)
-- The real Sterbenz property is about EXACT subtraction, which we capture in the spec

-- 13. Addition is NOT associative
-- (big + neg_big) + one = 0 + 1 = 1
-- big + (neg_big + one) = big + neg_big = 0 (because neg_big + one rounds to neg_big)
example : ((big + neg_big) + one == big + (neg_big + one)) = false := by native_decide

-- 14. Distributive law does NOT hold
-- d1 * (d2 + d3) vs d1 * d2 + d1 * d3 where d1 = 1e16, d2 = 1, d3 = -1e16
-- Left side: 1e16 * (1 + (-1e16)) = 1e16 * (-1e16 + 1) ≈ 1e16 * (-1e16) = -1e32
-- Right side: 1e16 * 1 + 1e16 * (-1e16) = 1e16 - 1e32 (different due to rounding)
example : (d1 * (d2 + d3) == d1 * d2 + d1 * d3) = false := by native_decide

-- 15. Not all non-zero floats have multiplicative inverses
-- For infinity: 1/inf = 0, so inf * (1/inf) = inf * 0 = NaN ≠ 1
example : (inf * (1.0 / inf) == 1.0) = false := by native_decide
example : Float.isNaN (inf * (1.0 / inf)) = true := by native_decide

-- For tiny denormals: 1/tiny = inf, so tiny * (1/tiny) = tiny * inf = inf ≠ 1
example : Float.isInf (1.0 / tiny) = true := by native_decide
example : (tiny * (1.0 / tiny) == 1.0) = false := by native_decide

/-!
# Axiom Inconsistencies

The following axioms in FloatSpec are FALSE for IEEE 754 floats.
These need preconditions restricting to finite, non-extreme values.
-/

-- 16. mul_eq_zero is FALSE
-- Underflow: small * small = 0, but small ≠ 0
example : (small * small == 0.0) = true := by native_decide
example : (small == 0.0) = false := by native_decide
-- NaN: NaN * 0 = NaN ≠ 0
example : (nan * 0.0 == 0.0) = false := by native_decide

-- 17. add_neg_self is FALSE for Infinity
-- Inf + (-Inf) = NaN ≠ 0
example : (inf + neg_inf == 0.0) = false := by native_decide
example : Float.isNaN (inf + neg_inf) = true := by native_decide
-- NaN + (-NaN) = NaN ≠ 0
example : (nan + (-nan) == 0.0) = false := by native_decide

-- 18. mul_div_cancel is FALSE due to overflow/underflow
-- Overflow: (huge * huge) / huge = Inf / huge = Inf ≠ huge
example : Float.isInf (huge * huge) = true := by native_decide
example : ((huge * huge) / huge == huge) = false := by native_decide
-- Underflow: (small * small) / small = 0 / small = 0 ≠ small
example : ((small * small) / small == small) = false := by native_decide

-- 19. div_mul_cancel is FALSE due to underflow
-- (small / huge) * huge: small/huge underflows to 0, then 0 * huge = 0 ≠ small
example : ((small / huge) * huge == small) = false := by native_decide

end Float.Examples
