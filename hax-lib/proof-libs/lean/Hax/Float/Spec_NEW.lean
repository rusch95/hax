/-
Hax Lean Backend - Cryspen

NEW VERSION: Rat with Quotient Types

This is a prototype showing how quotient types solve the normalization problem.
-/

import Hax.Lib

namespace Float.Spec

/-! # Rational Type with Quotient

This version uses quotient types to get proper mathematical equality.
Key insight: ⟨0,5⟩ = ⟨0,1⟩ via quotient equality.
-/

/-- Underlying representation of a rational number -/
structure RatRepr where
  num : Int
  den : Nat
  den_pos : den > 0

namespace RatRepr

/-- Two rationals are equivalent if they represent the same value -/
def equiv (q r : RatRepr) : Prop :=
  q.num * (r.den : Int) = r.num * (q.den : Int)

/-- Equivalence is reflexive -/
theorem equiv_refl (q : RatRepr) : equiv q q := rfl

/-- Equivalence is symmetric -/
theorem equiv_symm {q r : RatRepr} : equiv q r → equiv r q := Eq.symm

/-- Equivalence is transitive -/
theorem equiv_trans {q r s : RatRepr} : equiv q r → equiv r s → equiv q s := by
  intro hqr hrs
  unfold equiv at *
  -- Multiply and rearrange to cancel r.den
  have h : q.num * (r.den : Int) * (s.den : Int) = s.num * (q.den : Int) * (r.den : Int) := by
    calc q.num * (r.den : Int) * (s.den : Int)
        = (q.num * (r.den : Int)) * (s.den : Int) := by ac_rfl
      _ = (r.num * (q.den : Int)) * (s.den : Int) := by rw [hqr]
      _ = r.num * (q.den : Int) * (s.den : Int) := by ac_rfl
      _ = (r.num * (s.den : Int)) * (q.den : Int) := by ac_rfl
      _ = (s.num * (r.den : Int)) * (q.den : Int) := by rw [hrs]
      _ = s.num * (q.den : Int) * (r.den : Int) := by ac_rfl
  -- Cancel r.den (which is positive, hence nonzero)
  have rden_pos : (0 : Int) < (r.den : Int) := Int.ofNat_pos.mpr r.den_pos
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt rden_pos) h

instance : Setoid RatRepr where
  r := equiv
  iseqv := {
    refl := equiv_refl
    symm := @equiv_symm
    trans := @equiv_trans
  }

end RatRepr

/-- Rational number type with quotient equality -/
def Rat := Quotient (α := RatRepr) RatRepr.instSetoidRatRepr

namespace Rat

/-- Construct a Rat from num/den -/
def mk (num : Int) (den : Nat) (den_pos : den > 0) : Rat :=
  Quotient.mk RatRepr.instSetoidRatRepr ⟨num, den, den_pos⟩

/-- Zero -/
def zero : Rat := mk 0 1 (by decide)

/-- One -/
def one : Rat := mk 1 1 (by decide)

/-- Example: ⟨0,5⟩ = ⟨0,1⟩ with quotient equality -/
example : mk 0 5 (by decide) = mk 0 1 (by decide) := by
  apply Quotient.sound
  unfold RatRepr.equiv
  simp

/-- Negation respects equivalence -/
theorem neg_sound : ∀ q r : RatRepr, q ≈ r → RatRepr.mk (-q.num) q.den q.den_pos ≈ RatRepr.mk (-r.num) r.den r.den_pos := by
  intro q r h
  unfold RatRepr.equiv at *
  simp
  calc -q.num * (r.den : Int)
      = -(q.num * (r.den : Int)) := by ring
    _ = -(r.num * (q.den : Int)) := by rw [h]
    _ = -r.num * (q.den : Int) := by ring

/-- Negation -/
def neg (q : Rat) : Rat :=
  Quotient.lift
    (fun qr => mk (-qr.num) qr.den qr.den_pos)
    (fun q r h => Quotient.sound (neg_sound q r h))
    q

/-- Multiplication respects equivalence -/
theorem mul_sound : ∀ q r q' r' : RatRepr,
    q ≈ q' → r ≈ r' →
    RatRepr.mk (q.num * r.num) (q.den * r.den) (Nat.mul_pos q.den_pos r.den_pos) ≈
    RatRepr.mk (q'.num * r'.num) (q'.den * r'.den) (Nat.mul_pos q'.den_pos r'.den_pos) := by
  intro q r q' r' hq hr
  unfold RatRepr.equiv at *
  -- Need: (q.num * r.num) * (q'.den * r'.den) = (q'.num * r'.num) * (q.den * r.den)
  calc (q.num * r.num) * ((q'.den : Int) * (r'.den : Int))
      = (q.num * (q'.den : Int)) * (r.num * (r'.den : Int)) := by ring
    _ = (q'.num * (q.den : Int)) * (r.num * (r'.den : Int)) := by rw [hq]
    _ = (q'.num * (q.den : Int)) * (r'.num * (r.den : Int)) := by rw [hr]
    _ = (q'.num * r'.num) * ((q.den : Int) * (r.den : Int)) := by ring

/-- Multiplication -/
def mul (q r : Rat) : Rat :=
  Quotient.lift₂
    (fun qr rr => mk (qr.num * rr.num) (qr.den * rr.den) (Nat.mul_pos qr.den_pos rr.den_pos))
    (fun q r q' r' hq hr => Quotient.sound (mul_sound q r q' r' hq hr))
    q r

instance : Mul Rat where
  mul := mul

instance : Neg Rat where
  neg := neg

instance : Zero Rat where
  zero := zero

instance : One Rat where
  one := one

/-- KEY THEOREM: This now works! -/
theorem zero_mul (q : Rat) : zero * q = zero := by
  -- Use quotient induction
  apply Quotient.ind
  intro qr
  apply Quotient.sound
  unfold RatRepr.equiv
  simp [mk]
  -- Goal: 0 * qr.den = 0 * 1
  omega

end Rat
end Float.Spec
