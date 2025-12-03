import Hax.Lib
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Hax.Float.Spec

namespace Float.ExampleHelpers

open Float.Spec

/-!
## Helpers for Valid Properties
-/

-- Helper to access the FloatSpec instance for Float
-- noncomputable def spec := FloatSpec_Float

/-!
## Helpers for Invalid Properties (Counterexamples)
-/

-- Witnesses for counterexamples
-- Use concrete values for native_decide to work
def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0
def neg_inf : Float := -1.0 / 0.0
def zero := 0.0
def neg_zero := -0.0
def small := 1.0e-300

-- Constants for associativity/distributivity counterexamples
def big : Float := 1.0e20
def neg_big : Float := -1.0e20
def one : Float := 1.0
def tiny : Float := 5.0e-324  -- smallest positive denormal

-- Constants for overflow/underflow counterexamples
def huge : Float := 1.0e300  -- large enough to overflow when squared

-- Constants for distributivity counterexample
def d1 : Float := 1.0e16
def d2 : Float := 1.0
def d3 : Float := -1.0e16

-- Generic theorems to prove negation of universal quantifiers by providing a witness
theorem not_forall_of_exists_not {α : Type} {p : α → Prop} (x : α) (h : ¬ p x) : ¬ (∀ x, p x) :=
  fun all_p => h (all_p x)

theorem not_forall2_of_exists_not {α : Type} {p : α → α → Prop} (x y : α) (h : ¬ p x y) : ¬ (∀ x y, p x y) :=
  fun all_p => h (all_p x y)

theorem not_forall3_of_exists_not {α : Type} {p : α → α → α → Prop} (x y z : α) (h : ¬ p x y z) : ¬ (∀ x y z, p x y z) :=
  fun all_p => h (all_p x y z)

end Float.ExampleHelpers
