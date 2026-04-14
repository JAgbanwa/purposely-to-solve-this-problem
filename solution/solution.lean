-- solution.lean
-- Lean 4 formalization of necessary conditions for the Diophantine equation
--   (3x - 1) * y^2 + x * z^2 = x^3 - 2
-- under the hypotheses x ≡ 2 (mod 16) and x ≡ 1 (mod 3).
--
-- We formalize the modular arithmetic lemmas (Steps 1–6 in the LaTeX write-up)
-- using ZMod + decide for finite checks, and omega/linarith for linear arithmetic.
--
-- NOTE: This file requires Mathlib (via the Lake project in the repo root).
-- Run `lake exe cache get` from the repo root to download prebuilt Mathlib .oleans.

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

open Int

/-! ## Main equation and hypotheses -/

/-- The Diophantine equation we study. -/
def IsTriple (x y z : ℤ) : Prop :=
  (3 * x - 1) * y ^ 2 + x * z ^ 2 = x ^ 3 - 2

/-- The problem's modular hypotheses, combined via CRT into x ≡ 34 (mod 48). -/
def Hyp (x : ℤ) : Prop :=
  x % 16 = 2 ∧ x % 3 = 1

theorem hyp_crt (x : ℤ) : Hyp x ↔ x % 48 = 34 := by
  constructor
  · intro ⟨h16, h3⟩; omega
  · intro h; constructor <;> omega

/-! ## ZMod casting helpers -/

/-- Cast the ℤ-equation `IsTriple x y z` to `ZMod n`. -/
private lemma cast_to_zmod (n : ℕ) [NeZero n] (x y z : ℤ) (heq : IsTriple x y z) :
    (3 * (x : ZMod n) - 1) * (y : ZMod n) ^ 2 + (x : ZMod n) * (z : ZMod n) ^ 2 =
    (x : ZMod n) ^ 3 - 2 := by
  have h := congr_arg (Int.cast (R := ZMod n)) heq
  push_cast at h; ring_nf at h ⊢; exact h

/-- If `x % n = r`, then `(x : ZMod n) = (r : ZMod n)`. -/
private lemma int_cast_mod {x : ℤ} {n : ℕ} [NeZero n] {r : ℤ} (h : x % n = r) :
    (x : ZMod n) = (r : ZMod n) := by
  have : ((x % n : ℤ) : ZMod n) = (x : ZMod n) := by push_cast; simp
  rw [← h]; exact this.symm

/-! ## Step 1 — Modulo 2 and 4: y is even, z is odd -/

/-- Under the hypotheses, y must be even. -/
theorem y_even (x y z : ℤ) (heq : IsTriple x y z) (hx16 : x % 16 = 2) :
    y % 2 = 0 := by
  have hx2 : (x : ZMod 2) = 0 := int_cast_mod (by omega : x % 2 = 0)
  have hmod := cast_to_zmod 2 x y z heq
  rw [hx2] at hmod
  have hsq : (y : ZMod 2) ^ 2 = 0 := by
    have key : ∀ b c : ZMod 2,
        (3 * (0 : ZMod 2) - 1) * b ^ 2 + 0 * c ^ 2 = (0 : ZMod 2) ^ 3 - 2 → b ^ 2 = 0 := by
      decide
    exact key _ (z : ZMod 2) (by simpa using hmod)
  have hy2 : (y : ZMod 2) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero] at hy2

/-- Under the hypotheses, z must be odd. -/
theorem z_odd (x y z : ℤ) (heq : IsTriple x y z) (hx16 : x % 16 = 2) :
    z % 2 = 1 ∨ z % 2 = -1 := by
  obtain ⟨b, hb⟩ : ∃ b : ℤ, y = 2 * b := ⟨y / 2, by have := y_even x y z heq hx16; omega⟩
  subst hb
  have hx4 : (x : ZMod 4) = 2 := int_cast_mod (by omega : x % 4 = 2)
  have hmod4 := cast_to_zmod 4 x (2 * b) z heq
  rw [hx4] at hmod4; push_cast at hmod4
  have key : ∀ b c : ZMod 4,
      (3 * (2 : ZMod 4) - 1) * (2 * b) ^ 2 + 2 * c ^ 2 = (2 : ZMod 4) ^ 3 - 2 →
      c = 1 ∨ c = 3 := by decide
  rcases key (b : ZMod 4) (z : ZMod 4) (by simpa using hmod4) with hz | hz
  · left
    have h : z ≡ 1 [ZMOD 4] := (ZMod.intCast_eq_intCast_iff z 1 4).mp hz
    simp [Int.ModEq] at h; omega
  · left
    have h : z ≡ 3 [ZMOD 4] := (ZMod.intCast_eq_intCast_iff z 3 4).mp hz
    simp [Int.ModEq] at h; omega

/-! ## Step 2 — Modulo 3: 3 ∣ z, 3 ∤ y -/

/-- Under the hypotheses, 3 ∣ z. -/
theorem three_dvd_z (x y z : ℤ) (heq : IsTriple x y z) (hx3 : x % 3 = 1) :
    z % 3 = 0 := by
  have hx3z : (x : ZMod 3) = 1 := int_cast_mod hx3
  have hmod3 := cast_to_zmod 3 x y z heq
  rw [hx3z] at hmod3
  have key : ∀ b c : ZMod 3,
      (3 * (1 : ZMod 3) - 1) * b ^ 2 + 1 * c ^ 2 = (1 : ZMod 3) ^ 3 - 2 → c = 0 := by decide
  have hcz : (z : ZMod 3) = 0 := key _ _ (by simpa using hmod3)
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero] at hcz

/-- Under the hypotheses, 3 does not divide y. -/
theorem three_not_dvd_y (x y z : ℤ) (heq : IsTriple x y z) (hx3 : x % 3 = 1) :
    y % 3 ≠ 0 := by
  have hx3z : (x : ZMod 3) = 1 := int_cast_mod hx3
  have hmod3 := cast_to_zmod 3 x y z heq
  rw [hx3z] at hmod3
  have key : ∀ b c : ZMod 3,
      (3 * (1 : ZMod 3) - 1) * b ^ 2 + 1 * c ^ 2 = (1 : ZMod 3) ^ 3 - 2 → b ≠ 0 := by decide
  intro hy3
  have : (y : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast Int.dvd_of_emod_eq_zero hy3
  exact key _ _ (by simpa using hmod3) this

/-! ## Step 3 — Substitution: y = 2b, z = 3w -/

lemma even_iff_exists_half (y : ℤ) : y % 2 = 0 ↔ ∃ b : ℤ, y = 2 * b :=
  ⟨fun h => ⟨y / 2, by omega⟩, fun ⟨b, hb⟩ => by omega⟩

lemma div3_iff_exists (z : ℤ) : z % 3 = 0 ↔ ∃ w : ℤ, z = 3 * w :=
  ⟨fun h => ⟨z / 3, by omega⟩, fun ⟨w, hw⟩ => by omega⟩

/-- Ring identity: substituting y = 2b, z = 3w gives Eq. A. -/
theorem equation_A (x b w : ℤ) (heq : IsTriple x (2 * b) (3 * w)) :
    4 * (3 * x - 1) * b ^ 2 + 9 * x * w ^ 2 = x ^ 3 - 2 := by
  unfold IsTriple at heq; ring_nf at heq ⊢; linarith

/-! ## Step 4 — Modulo 9: b² ≡ 1, b ≡ ±1 (mod 9) -/

/-- Under the hypotheses, b² ≡ 1 (mod 9). -/
theorem b_sq_mod9 (x b w : ℤ)
    (hA : 4 * (3 * x - 1) * b ^ 2 + 9 * x * w ^ 2 = x ^ 3 - 2)
    (hx3 : x % 3 = 1) :
    b ^ 2 % 9 = 1 := by
  have hmod9 : 4 * (3 * (x : ZMod 9) - 1) * (b : ZMod 9) ^ 2 +
      9 * (x : ZMod 9) * (w : ZMod 9) ^ 2 = (x : ZMod 9) ^ 3 - 2 := by
    have h := congr_arg (Int.cast (R := ZMod 9)) hA
    push_cast at h; ring_nf at h ⊢; exact h
  have hx9 : (x : ZMod 9) = 1 ∨ (x : ZMod 9) = 4 ∨ (x : ZMod 9) = 7 := by
    rcases (show x % 9 = 1 ∨ x % 9 = 4 ∨ x % 9 = 7 by omega) with h | h | h
    · exact Or.inl (int_cast_mod h)
    · exact Or.inr (Or.inl (int_cast_mod h))
    · exact Or.inr (Or.inr (int_cast_mod h))
  have key : ∀ xm bm wm : ZMod 9,
      4 * (3 * xm - 1) * bm ^ 2 + 9 * xm * wm ^ 2 = xm ^ 3 - 2 →
      (xm = 1 ∨ xm = 4 ∨ xm = 7) → bm ^ 2 = 1 := by decide
  have hbsq : (b : ZMod 9) ^ 2 = 1 := key _ _ _ hmod9 hx9
  have hbsq_cast : ((b ^ 2 : ℤ) : ZMod 9) = 1 := by push_cast; exact hbsq
  have : b ^ 2 ≡ 1 [ZMOD 9] := (ZMod.intCast_eq_intCast_iff _ 1 9).mp hbsq_cast
  simp [Int.ModEq] at this; omega

/-- b ≡ 1 or 8 (mod 9) (i.e. b ≡ ±1 mod 9). -/
theorem b_mod9 (x b w : ℤ)
    (hA : 4 * (3 * x - 1) * b ^ 2 + 9 * x * w ^ 2 = x ^ 3 - 2)
    (hx3 : x % 3 = 1) :
    b % 9 = 1 ∨ b % 9 = 8 := by
  have hbsq9 := b_sq_mod9 x b w hA hx3
  have hbzmod : (b : ZMod 9) ^ 2 = 1 := by
    have hbsq_cast : ((b ^ 2 : ℤ) : ZMod 9) = 1 :=
      (ZMod.intCast_eq_intCast_iff (b ^ 2) 1 9).mpr (by simp [Int.ModEq]; omega)
    push_cast at hbsq_cast; exact hbsq_cast
  have key : ∀ bm : ZMod 9, bm ^ 2 = 1 → bm = 1 ∨ bm = 8 := by decide
  rcases key _ hbzmod with h | h
  · left
    have : b ≡ 1 [ZMOD 9] := (ZMod.intCast_eq_intCast_iff b 1 9).mp h
    simp [Int.ModEq] at this; omega
  · right
    have : b ≡ 8 [ZMOD 9] := (ZMod.intCast_eq_intCast_iff b 8 9).mp h
    simp [Int.ModEq] at this; omega

/-! ## Step 5 — Modulo 27: key parity constraint -/

/-- e = (b² - 1) / 9 is an integer by b_sq_mod9. -/
def eVal (b : ℤ) : ℤ := (b ^ 2 - 1) / 9

/-- Under the hypotheses, w² + 2·e ≡ 2 (mod 3).
    Proof: substitute x = 3k+1 and b² = 9e+1 into Eq. A, expand, then omega. -/
theorem mod27_constraint (x b w : ℤ)
    (hA : 4 * (3 * x - 1) * b ^ 2 + 9 * x * w ^ 2 = x ^ 3 - 2)
    (hx3 : x % 3 = 1)
    (hbmod9 : b ^ 2 % 9 = 1) :
    (w ^ 2 + 2 * eVal b) % 3 = 2 := by
  have hbexp : b ^ 2 = 9 * eVal b + 1 := by unfold eVal; omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x = 3 * k + 1 := ⟨x / 3, by omega⟩
  rw [hk, hbexp] at hA; ring_nf at hA; omega

/-- If e ≡ 0 (mod 3), we would need w² ≡ 2 (mod 3), which is impossible
    since squares mod 3 are 0 or 1. -/
theorem e_not_zero_mod3 (x b w : ℤ)
    (hA : 4 * (3 * x - 1) * b ^ 2 + 9 * x * w ^ 2 = x ^ 3 - 2)
    (hx3 : x % 3 = 1)
    (hbmod9 : b ^ 2 % 9 = 1)
    (he0 : eVal b % 3 = 0) : False := by
  have hconstr := mod27_constraint x b w hA hx3 hbmod9
  have key : ∀ c : ZMod 3, c ^ 2 = 0 ∨ c ^ 2 = 1 := by decide
  rcases key (w : ZMod 3) with h | h
  · have : ((w ^ 2 : ℤ) : ZMod 3) = 0 := by push_cast; exact h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have : w ^ 2 % 3 = 0 := Int.emod_eq_zero_of_dvd this
    omega
  · have hc : ((w ^ 2 : ℤ) : ZMod 3) = 1 := by push_cast; exact h
    have hmod : w ^ 2 ≡ 1 [ZMOD 3] := (ZMod.intCast_eq_intCast_iff _ 1 3).mp hc
    simp [Int.ModEq] at hmod; omega

/-! ## Step 6 — Equation ★ and X ≡ 2 (mod 9) -/

/-- Ring identity: the factored form (Eq. ★). -/
theorem equation_star (X b w : ℤ) (heq : IsTriple (2*X) (2*b) (3*w)) :
    X * (2*X - 3*w) * (2*X + 3*w) = 2*(6*X-1)*b^2 + 1 := by
  unfold IsTriple at heq; ring_nf at heq ⊢; linarith

/-- Under the hypotheses, a solution forces X ≡ 2 (mod 9).
    Non-linear identity — formal proof pending. -/
theorem X_mod9 (X b w : ℤ)
    (hstar : X * (2*X - 3*w) * (2*X + 3*w) = 2*(6*X-1)*b^2 + 1)
    (hX3 : X % 3 = 2)
    (hbmod9 : b ^ 2 % 9 = 1) :
    X % 9 = 2 := by
  sorry

/-! ## Main necessary-conditions theorem -/

theorem necessary_conditions (x y z : ℤ)
    (heq : IsTriple x y z)
    (hx16 : x % 16 = 2)
    (hx3 : x % 3 = 1) :
    y % 2 = 0 ∧
    (z % 2 = 1 ∨ z % 2 = -1) ∧
    z % 3 = 0 ∧
    y % 3 ≠ 0 :=
  ⟨y_even x y z heq hx16, z_odd x y z heq hx16,
   three_dvd_z x y z heq hx3, three_not_dvd_y x y z heq hx3⟩

/-! ## Conjecture: non-existence -/

/-- The main claim: no integer triple satisfies both the equation and the given
    hypotheses. A complete analytic proof is an open problem. -/
theorem no_solution (x y z : ℤ)
    (heq : IsTriple x y z)
    (hx16 : x % 16 = 2)
    (hx3 : x % 3 = 1) : False := by
  obtain ⟨hy_even, _, hz3, _⟩ := necessary_conditions x y z heq hx16 hx3
  obtain ⟨b, hb⟩ := (even_iff_exists_half y).mp hy_even
  obtain ⟨w, hw⟩ := (div3_iff_exists z).mp hz3
  subst hb; subst hw
  have hA := equation_A x b w heq
  have _hb9 := b_sq_mod9 x b w hA hx3
  sorry
