/-
What Tesla Saw (Jeromie Beasley): Tesla's own circuit laws, as he stated them, and what follows
from them exactly.

Each law is written as a definition. It is Tesla's stated law, taken as given: nothing here
derives the period law, the energy law or the magnification rule from electromagnetism. What is
proved is what those laws imply, over the real numbers and with every hypothesis written out.

* `freq L C = 1/(2π√(LC))`, his period law (the Colorado Springs Notes).
* `energy C V = CV²/2`, the energy held by a condenser.
* `mag p L R = pL/R`, his magnification rule; `decay L R = R/(2L)`, the decay rate of a lossy
  circuit.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace WhatTeslaSaw

open Real

/-! ## His laws, as definitions -/

/-- Tesla's period law: a circuit of self-induction `L` and capacity `C` vibrates at
`n = 1/(2π√(LC))`. -/
noncomputable def freq (L C : ℝ) : ℝ := 1 / (2 * π * √(L * C))

/-- The energy held by a condenser of capacity `C` at voltage `V`. -/
noncomputable def energy (C V : ℝ) : ℝ := C * V ^ 2 / 2

/-- Tesla's magnification rule `m = pL/R`. -/
noncomputable def mag (p L R : ℝ) : ℝ := p * L / R

/-- The decay rate `γ = R/(2L)` of a circuit with resistance `R` and self-induction `L`. -/
noncomputable def decay (L R : ℝ) : ℝ := R / (2 * L)

/-! ## The period law: tuning and the octave -/

/-- A circuit with positive `LC` has a positive frequency. -/
theorem freq_pos {L C : ℝ} (h : 0 < L * C) : 0 < freq L C := by
  have hs : 0 < √(L * C) := Real.sqrt_pos.mpr h
  unfold freq
  positivity

/-- **His tuning rule.** Two circuits vibrate at the same frequency exactly when they have the
same product `LC`. -/
theorem tuning_rule {L₁ C₁ L₂ C₂ : ℝ} (h₁ : 0 < L₁ * C₁) (h₂ : 0 < L₂ * C₂) :
    freq L₁ C₁ = freq L₂ C₂ ↔ L₁ * C₁ = L₂ * C₂ := by
  constructor
  · intro h
    unfold freq at h
    rw [one_div, one_div, inv_inj] at h
    have hπ : (2 : ℝ) * π ≠ 0 := by positivity
    have hs : √(L₁ * C₁) = √(L₂ * C₂) := mul_left_cancel₀ hπ h
    exact (Real.sqrt_inj h₁.le h₂.le).mp hs
  · intro h
    unfold freq
    rw [h]

/-- **His octave rule.** A quarter of the capacity, at the same self-induction, doubles the
frequency. -/
theorem octave_quarter_capacity {L C : ℝ} (h : 0 < L * C) :
    freq L (C / 4) = 2 * freq L C := by
  have hq : √(L * (C / 4)) = √(L * C) / 2 := by
    rw [show L * (C / 4) = (L * C) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hs : 0 < √(L * C) := Real.sqrt_pos.mpr h
  unfold freq
  rw [hq]
  field_simp

/-- **The octave, exactly.** At fixed self-induction, a circuit sounds the octave of another
exactly when it has a quarter of the capacity: "an octave would require only 12 jars on each
side" instead of 48. -/
theorem octave_iff {L C C' : ℝ} (hL : 0 < L) (hC : 0 < C) (hC' : 0 < C') :
    freq L C' = 2 * freq L C ↔ C' = C / 4 := by
  have h₁ : 0 < L * C' := mul_pos hL hC'
  have h₂ : 0 < L * (C / 4) := by positivity
  rw [← octave_quarter_capacity (mul_pos hL hC), tuning_rule h₁ h₂]
  constructor
  · intro h
    exact mul_left_cancel₀ hL.ne' h
  · intro h
    rw [h]

/-- More capacity lowers the frequency: at fixed `L > 0`, the frequency strictly falls as `C`
grows. -/
theorem freq_strictAntiOn {L : ℝ} (hL : 0 < L) : StrictAntiOn (freq L) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < L * a := mul_pos hL ha
  have hb' : 0 < L * b := mul_pos hL hb
  have hs : √(L * a) < √(L * b) :=
    Real.sqrt_lt_sqrt ha'.le (mul_lt_mul_of_pos_left hab hL)
  have hsa : 0 < √(L * a) := Real.sqrt_pos.mpr ha'
  unfold freq
  apply one_div_lt_one_div_of_lt
  · positivity
  · have hπ : 0 < 2 * π := by positivity
    exact mul_lt_mul_of_pos_left hs hπ

/-! ## Energy -/

/-- "the octave vibration had only 1/4 of the energy" (Notes, 3 July 1899): at the same voltage, a quarter of the
capacity holds a quarter of the energy. -/
theorem energy_quarter_capacity (C V : ℝ) : energy (C / 4) V = energy C V / 4 := by
  unfold energy
  ring

/-- Energy grows as the square of the voltage: at fixed capacity, the ratio of energies is the
square of the ratio of voltages. -/
theorem energy_ratio {C V₁ V₂ : ℝ} (hC : C ≠ 0) (hV : V₁ ≠ 0) :
    energy C V₂ / energy C V₁ = (V₂ / V₁) ^ 2 := by
  unfold energy
  field_simp

/-! ## Magnification -/

/-- **His magnification rule, cooled.** Halving the resistance doubles the magnification. -/
theorem halving_resistance_doubles_mag (p L : ℝ) {R : ℝ} (hR : R ≠ 0) :
    mag p L (R / 2) = 2 * mag p L R := by
  unfold mag
  field_simp

/-- The magnification falls strictly as the resistance grows (for `pL > 0`). -/
theorem mag_strictAntiOn {p L : ℝ} (h : 0 < p * L) : StrictAntiOn (mag p L) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold mag
  exact div_lt_div_of_pos_left h ha hab

/-- The magnification is proportional to the frequency `p`. -/
theorem mag_proportional_to_tone (c p L R : ℝ) : mag (c * p) L R = c * mag p L R := by
  unfold mag
  ring

/-- **His magnification as tone over decay.** `m = pL/R = p/(2γ)` with `γ = R/(2L)`. -/
theorem mag_eq_tone_over_twice_decay (p : ℝ) {L R : ℝ} (hL : L ≠ 0) (hR : R ≠ 0) :
    mag p L R = p / (2 * decay L R) := by
  unfold mag decay
  field_simp

/-! ## His equal-split law (US 416,194) -/

/-- With a fixed total, the product of the two parts is greatest when they are equal:
`4ab ≤ (a + b)²` for all real `a`, `b`. -/
theorem equal_split (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The product reaches its greatest value only when the parts are equal. -/
theorem equal_split_eq_iff (a b : ℝ) : 4 * a * b = (a + b) ^ 2 ↔ a = b := by
  constructor
  · intro h
    have h2 : (a - b) ^ 2 = 0 := by linear_combination -h
    have h3 : a - b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    linarith
  · intro h
    rw [h]
    ring

/-! ## The turbine (US 1,061,206 and 1,209,359) -/

/-- The square-law identity: `4v³ − 27u(v − u)² = (3u − v)²(4v − 3u)`. -/
theorem turbine_square_law_identity (u v : ℝ) :
    4 * v ^ 3 - 27 * u * (v - u) ^ 2 = (3 * u - v) ^ 2 * (4 * v - 3 * u) := by
  ring

/-- **The square drag law peaks at one third.** If the drag grows as the square of the relative
speed, the work `u(v − u)²` done at runner speed `u` (with fluid speed `v`, `0 ≤ u ≤ v`) never
exceeds its value at `u = v/3`. -/
theorem turbine_square_law_third {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u * (v - u) ^ 2 ≤ (v / 3) * (v - v / 3) ^ 2 := by
  have h4 : 0 ≤ 4 * v - 3 * u := by linarith
  nlinarith [mul_nonneg (sq_nonneg (3 * u - v)) h4]

/-- ... and only there. -/
theorem turbine_square_law_eq_iff {u v : ℝ} (hv : 0 < v) (huv : u ≤ v) :
    u * (v - u) ^ 2 = (v / 3) * (v - v / 3) ^ 2 ↔ u = v / 3 := by
  constructor
  · intro h
    have hprod : (3 * u - v) ^ 2 * (4 * v - 3 * u) = 0 := by
      linear_combination (-27 : ℝ) * h
    have h4 : 4 * v - 3 * u ≠ 0 := by
      have : 0 < 4 * v - 3 * u := by linarith
      exact this.ne'
    rcases mul_eq_zero.mp hprod with h1 | h1
    · have : 3 * u - v = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      linarith
    · exact absurd h1 h4
  · intro h
    rw [h]

/-- **The linear drag law peaks at one half.** If the drag grows linearly with the relative speed,
the work `u(v − u)` never exceeds its value at `u = v/2`... -/
theorem turbine_linear_law_half (u v : ℝ) : u * (v - u) ≤ (v / 2) * (v - v / 2) := by
  nlinarith [sq_nonneg (u - v / 2)]

/-- ... and only there. -/
theorem turbine_linear_law_eq_iff (u v : ℝ) :
    u * (v - u) = (v / 2) * (v - v / 2) ↔ u = v / 2 := by
  constructor
  · intro h
    have h2 : (u - v / 2) ^ 2 = 0 := by linear_combination -h
    have h3 : u - v / 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    linarith
  · intro h
    rw [h]

/-! ## Two tuned circuits, coupled -/

/-- **The coupled pair's determinant.** Two circuits tuned by his rule, `L₁C₁ = L₂C₂ = a`, and
coupled with `M² = k²L₁L₂`: the determinant of the pair at `y = ω²` factors as
`(1 − ya(1 + k))(1 − ya(1 − k))`. -/
theorem coupled_determinant {L₁ C₁ L₂ C₂ M a k y : ℝ} (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0)
    (h₁ : L₁ * C₁ = a) (h₂ : L₂ * C₂ = a) (hM : M ^ 2 = k ^ 2 * (L₁ * L₂)) :
    C₁ * C₂ * ((1 / C₁ - y * L₁) * (1 / C₂ - y * L₂) - (y * M) ^ 2)
      = (1 - y * a * (1 + k)) * (1 - y * a * (1 - k)) := by
  have e : C₁ * C₂ * ((1 / C₁ - y * L₁) * (1 / C₂ - y * L₂) - (y * M) ^ 2)
      = (1 - y * (L₁ * C₁)) * (1 - y * (L₂ * C₂)) - y ^ 2 * M ^ 2 * (C₁ * C₂) := by
    field_simp
  rw [e, hM]
  subst h₁
  linear_combination (-y * (1 - y * (L₁ * C₁)) - y ^ 2 * k ^ 2 * (L₁ * C₁)) * h₂

/-- **The pair rings at two tones.** For `0 < k < 1` the determinant vanishes exactly at
`y = 1/(a(1 + k))` and `y = 1/(a(1 − k))`. -/
theorem coupled_two_tones {a k y : ℝ} (ha : 0 < a) (hk₀ : 0 < k) (hk₁ : k < 1) :
    (1 - y * a * (1 + k)) * (1 - y * a * (1 - k)) = 0 ↔
      y = 1 / (a * (1 + k)) ∨ y = 1 / (a * (1 - k)) := by
  have hplus : a * (1 + k) ≠ 0 := by positivity
  have hminus : a * (1 - k) ≠ 0 := by
    have : 0 < 1 - k := by linarith
    positivity
  rw [mul_eq_zero, eq_div_iff hplus, eq_div_iff hminus]
  constructor
  · rintro (h | h)
    · left
      linear_combination -h
    · right
      linear_combination -h
  · rintro (h | h)
    · left
      linear_combination -h
    · right
      linear_combination -h

/-- **Never at the single tuned tone.** At `y = 1/a` the determinant is `−k²`, so a coupled pair
with `k ≠ 0` does not ring at the tone each circuit has alone. -/
theorem coupled_not_at_tuned_tone {a k : ℝ} (ha : a ≠ 0) :
    (1 - (1 / a) * a * (1 + k)) * (1 - (1 / a) * a * (1 - k)) = -k ^ 2 := by
  field_simp
  ring

/-- The two tones are an exact octave apart only at `k = 3/5`: the squared ratio of the two
values of `ω²` is `(1 + k)/(1 − k)`, which equals `4` exactly when `k = 3/5`. -/
theorem coupled_octave_iff {k : ℝ} (hk₁ : k < 1) : (1 + k) / (1 - k) = 4 ↔ k = 3 / 5 := by
  have h : (1 : ℝ) - k ≠ 0 := by
    have : 0 < 1 - k := by linarith
    exact this.ne'
  rw [div_eq_iff h]
  constructor
  · intro h'
    linarith
  · intro h'
    rw [h']
    norm_num

/-! ## The quarter wave -/

/-- **A quarter-wave wire rings only at odd tones.** For a wire of length `ℓ` with wave speed `v`
whose tone `f` satisfies the quarter-wave boundary condition `cos(2πfℓ/v) = 0`, the condition
holds exactly when `4ℓf` is an odd multiple of `v`. -/
theorem quarter_wave_odd_tones {ℓ v f : ℝ} (hv : 0 < v) :
    Real.cos (2 * π * f * ℓ / v) = 0 ↔ ∃ k : ℤ, 4 * ℓ * f = (2 * k + 1) * v := by
  rw [Real.cos_eq_zero_iff]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp at hk
    linear_combination hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp
    linear_combination hk

/-- **One end at zero, the other at the maximum.** On a wire a quarter wave long, `ℓ = v/(4f)`,
the standing-wave profile `sin(2πfx/v)` is zero at the grounded end `x = 0` and reaches its
greatest value, `1`, at the free end `x = ℓ`, where the quarter-wave condition holds: "at one
terminal the potential would be zero and at the other maximum" (US 593,138). -/
theorem quarter_wave_ends {v f : ℝ} (hv : 0 < v) (hf : 0 < f) :
    Real.sin (2 * π * f * 0 / v) = 0 ∧ Real.sin (2 * π * f * (v / (4 * f)) / v) = 1 ∧
      Real.cos (2 * π * f * (v / (4 * f)) / v) = 0 := by
  have e : 2 * π * f * (v / (4 * f)) / v = π / 2 := by
    field_simp
    ring
  rw [e, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp

/-- **Even multiples are forbidden.** No even multiple of the lowest tone `v/(4ℓ)` satisfies the
quarter-wave condition. -/
theorem quarter_wave_even_forbidden {ℓ v : ℝ} (hℓ : 0 < ℓ) (hv : 0 < v) (j : ℕ) :
    Real.cos (2 * π * ((2 * j) * (v / (4 * ℓ))) * ℓ / v) ≠ 0 := by
  rw [Ne, quarter_wave_odd_tones hv]
  rintro ⟨k, hk⟩
  have h : (2 * (j : ℝ)) * v = (2 * k + 1) * v := by
    rw [← hk]
    field_simp
  have h' : (2 * (j : ℝ)) = 2 * k + 1 := mul_right_cancel₀ hv.ne' h
  have h'' : (2 * (j : ℤ)) = 2 * k + 1 := by exact_mod_cast h'
  omega

end WhatTeslaSaw
