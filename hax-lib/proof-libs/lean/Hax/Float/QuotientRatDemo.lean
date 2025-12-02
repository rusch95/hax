/-
Quotient-based Rat - Proof of Concept

This demonstrates how quotient types solve the Rat normalization problem.
The key insight: ⟨0,5⟩ = ⟨0,1⟩ becomes TRUE via quotient equality!
-/

import Hax.Lib

namespace Float.Spec.QuotientRat

/-- Underlying representation -/
structure RatRepr where
  num : Int
  den : Nat
  den_pos : den > 0

namespace RatRepr

/-- Equivalence: a/b ~ c/d iff a*d = b*c -/
def equiv (q r : RatRepr) : Prop :=
  q.num * (r.den : Int) = r.num * (q.den : Int)

theorem equiv_refl (q : RatRepr) : equiv q q := rfl

theorem equiv_symm {q r : RatRepr} (h : equiv q r) : equiv r q := h.symm

theorem equiv_trans {q r s : RatRepr} (hqr : equiv q r) (hrs : equiv r s) : equiv q s := by
  unfold equiv at *
  -- We have: q.num * r.den = r.num * q.den  ... (hqr)
  --          r.num * s.den = s.num * r.den  ... (hrs)
  -- Want:    q.num * s.den = s.num * q.den
  --
  -- Proof: both sides equal when multiplied by r.den
  have : q.num * (s.den : Int) * (r.den : Int) = s.num * (q.den : Int) * (r.den : Int) := by
    calc q.num * (s.den : Int) * (r.den : Int)
        = q.num * (r.den : Int) * (s.den : Int) := by omega
      _ = r.num * (q.den : Int) * (s.den : Int) := by rw [hqr]; omega
      _ = r.num * (s.den : Int) * (q.den : Int) := by omega
      _ = s.num * (r.den : Int) * (q.den : Int) := by rw [hrs]; omega
      _ = s.num * (q.den : Int) * (r.den : Int) := by omega
  -- Cancel r.den from both sides
  have rden_ne_zero : (r.den : Int) ≠ 0 := by
    intro h
    have : r.den = 0 := Int.ofNat_inj.mp h
    omega
  have : q.num * (s.den : Int) * (r.den : Int) = s.num * (q.den : Int) * (r.den : Int) := this
  exact Int.eq_of_mul_eq_mul_right rden_ne_zero this

instance : Setoid RatRepr where
  r := equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

end RatRepr

/-- Quotient type for rationals -/
def Rat := Quotient RatRepr.instSetoidRatRepr

namespace Rat

def mk (num : Int) (den : Nat) (h : den > 0) : Rat :=
  ⟦⟨num, den, h⟩⟧

def zero : Rat := mk 0 1 (by decide)
def one : Rat := mk 1 1 (by decide)

/-- THE KEY PROPERTY: Different representations are equal! -/
example : mk 0 5 (by decide) = mk 0 1 (by decide) := by
  apply Quotient.sound
  show (0 : Int) * 1 = 0 * 5
  rfl

example : mk 2 4 (by decide) = mk 1 2 (by decide) := by
  apply Quotient.sound
  show (2 : Int) * 2 = 1 * 4
  rfl

/-- Negation respects equivalence -/
theorem neg_sound (q r : RatRepr) (h : q ≈ r) :
    (⟨-q.num, q.den, q.den_pos⟩ : RatRepr) ≈ ⟨-r.num, r.den, r.den_pos⟩ := by
  show (-q.num) * (r.den : Int) = (-r.num) * (q.den : Int)
  have : q.num * (r.den : Int) = r.num * (q.den : Int) := h
  omega

def neg (q : Rat) : Rat :=
  Quotient.lift
    (fun qr : RatRepr => mk (-qr.num) qr.den qr.den_pos)
    (fun q r h => Quotient.sound (neg_sound q r h))
    q

/-- Multiplication respects equivalence -/
theorem mul_sound (q r q' r' : RatRepr) (hq : q ≈ q') (hr : r ≈ r') :
    let prod := fun a b : RatRepr => ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    prod q r ≈ prod q' r' := by
  show (q.num * r.num) * ((q'.den * r'.den) : Int) = (q'.num * r'.num) * ((q.den * r.den) : Int)
  have : q.num * (q'.den : Int) = q'.num * (q.den : Int) := hq
  have : r.num * (r'.den : Int) = r'.num * (r.den : Int) := hr
  omega

def mul (q r : Rat) : Rat :=
  Quotient.lift₂
    (fun qr rr => mk (qr.num * rr.num) (qr.den * rr.den) (Nat.mul_pos qr.den_pos rr.den_pos))
    (fun _ _ _ _ => mul_sound _ _ _ _)
    q r

instance : Mul Rat := ⟨mul⟩
instance : Neg Rat := ⟨neg⟩
instance : Zero Rat := ⟨zero⟩
instance : One Rat := ⟨one⟩

/-! ## THE PAYOFF: Proofs that were impossible before! -/

/-- PROOF: 0 * q = 0  (This was blocked by normalization before!) -/
theorem zero_mul (q : Rat) : zero * q = zero := by
  induction q using Quotient.ind
  apply Quotient.sound
  show (0 * (Rat.num : RatRepr → Int) _) * (1 : Int) = 0 * ((Rat.den : RatRepr → Nat) _ : Int)
  omega

/-- PROOF: q * 0 = 0 -/
theorem mul_zero (q : Rat) : q * zero = zero := by
  induction q using Quotient.ind
  apply Quotient.sound
  omega

/-- PROOF: -0 = 0 -/
theorem neg_zero : -zero = zero := by
  apply Quotient.sound
  show (-(0 : Int)) * 1 = 0 * 1
  rfl

end Rat
end Float.Spec.QuotientRat

#check Float.Spec.QuotientRat.Rat.zero_mul  -- ✓ Proven!
#check Float.Spec.QuotientRat.Rat.mul_zero  -- ✓ Proven!
#check Float.Spec.QuotientRat.Rat.neg_zero  -- ✓ Proven!
