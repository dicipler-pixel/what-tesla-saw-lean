/-
What Tesla Saw (Jeromie Beasley): the numbers in Tesla's own work, checked exactly over the real
numbers. Each statement is an arithmetic check of figures he wrote down (or, where marked, of the
paper's reading of them). Arithmetic checks are not derivations: what each number means physically
is the paper's account, not something proved here.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace WhatTeslaSaw

/-! ## His patents, 1887–1897 -/

/-- US 359,748 (1887): six inches of iron in a twelve-inch core cut the eddy currents to fifty per
cent. -/
theorem eddy_fifty_percent : (6 : ℝ) / 12 * 100 = 50 := by norm_num

/-- US 390,721 (1888): poles turned 2,000 times and the armature 800 times; the motor turns 1,200
times. -/
theorem motor_speed : (2000 : ℝ) - 800 = 1200 := by norm_num

/-- US 416,194 (1889): field 90 and armature 10 give 900; 50 and 50 give 2,500, from the same
total of 100. -/
theorem equal_split_numbers :
    (90 : ℝ) * 10 = 900 ∧ (50 : ℝ) * 50 = 2500 ∧ (90 : ℝ) + 10 = 50 + 50 := by norm_num

/-- US 487,796 (1892): twelve reversals a turn on a six-pole motor give two motor turns per
generator turn. -/
theorem motor_turns_per_generator_turn : (12 : ℝ) / 6 = 2 := by norm_num

/-- US 512,340 (1894): raising the difference between neighbouring turns from 0.1 V to 50 V stores
`(50/0.1)² = 250,000` times the energy (energy grows as the square of the voltage:
`WhatTeslaSaw.energy_ratio`). -/
theorem bifilar_energy_ratio : ((50 : ℝ) / 0.1) ^ 2 = 250000 := by norm_num

/-- US 593,138 (1897): at 185,000 miles a second and 925 vibrations a second the waves are 200
miles long, and the quarter wave is 50 miles. -/
theorem quarter_wave_1897 : (185000 : ℝ) / 925 = 200 ∧ (200 : ℝ) / 4 = 50 := by norm_num

/-! ## Colorado Springs, 1899 -/

/-- Notes, 3 July 1899: 48 jars at the fundamental, 12 at the octave (a quarter of the capacity:
`WhatTeslaSaw.octave_iff`). -/
theorem octave_jars : (48 : ℝ) / 4 = 12 := by norm_num

/-- His November 1899 coils, first reading: with `L₁ = 230,945` cm, `L₂ = 9,023,000` cm and
`M = 851,021` cm, the coupling `k = M/√(L₁L₂)` lies between 0.589 and 0.590. -/
theorem coupling_his_first_M :
    (0.589 : ℝ) < 851021 / √(230945 * 9023000) ∧ 851021 / √(230945 * 9023000) < (0.590 : ℝ) := by
  have e : (851021 : ℝ) / √(230945 * 9023000) = √(851021 ^ 2 / (230945 * 9023000)) := by
    rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [e]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- The second reading, `M = 863,313` cm, gives a coupling between 0.598 and 0.599. -/
theorem coupling_his_second_M :
    (0.598 : ℝ) < 863313 / √(230945 * 9023000) ∧ 863313 / √(230945 * 9023000) < (0.599 : ℝ) := by
  have e : (863313 : ℝ) / √(230945 * 9023000) = √(863313 ^ 2 / (230945 * 9023000)) := by
    rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [e]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- So `1 − k²` is 0.65 for the first reading and 0.64 for the second, to two places. -/
theorem coupling_one_minus_k_sq :
    (0.65 : ℝ) < 1 - 851021 ^ 2 / (230945 * 9023000) ∧
      1 - 851021 ^ 2 / (230945 * 9023000) < (0.655 : ℝ) ∧
    (0.64 : ℝ) < 1 - 863313 ^ 2 / (230945 * 9023000) ∧
      1 - 863313 ^ 2 / (230945 * 9023000) < (0.645 : ℝ) := by
  norm_num

/-- Tuning by his rule with `C₂ = 622` cm needs `C₁ = L₂C₂/L₁`, which is between 30 and 30.02 of
his 0.0009 mfd bottles (one bottle = 810 cm). -/
theorem thirty_bottles :
    (30 : ℝ) ≤ 9023000 * 622 / 230945 / 810 ∧ (9023000 : ℝ) * 622 / 230945 / 810 ≤ 30.02 := by
  norm_num

/-! ## The earth (US 787,412) -/

/-- "471,240 kilometers per second" is `(π/2)·c` with his `π = 3.1416` and `c = 300,000` km/s. -/
theorem earth_surface_speed : (3.1416 : ℝ) / 2 * 300000 = 471240 := by norm_num

/-- "0.08484 of a second" is `2D/c` for a diameter `D = 12,726` km. The diameter is the paper's
inference: it is the value that makes his time exact, not a figure in Tesla's text. -/
theorem earth_round_trip : 2 * (12726 : ℝ) / 300000 = 0.08484 := by norm_num

/-- In that time a point moving at `(p/2)·c` covers `p·D`, half the circumference for `p = π`:
for any `p`, `D` and `c ≠ 0`, `((p/2)·c)·(2D/c) = p·D`. -/
theorem earth_once_round (p D : ℝ) {c : ℝ} (hc : c ≠ 0) : (p / 2 * c) * (2 * D / c) = p * D := by
  field_simp

/-- With his figures the identity reads `471,240 × 0.08484 = 3.1416 × 12,726` exactly. -/
theorem earth_once_round_numbers : (471240 : ℝ) * 0.08484 = 3.1416 * 12726 := by norm_num

/-- "The lowest frequency would appear to be six per second": `1/(2 × 0.08484) = c/(4D)` lies
between 5.89 and 5.9. -/
theorem earth_lowest_tone :
    1 / (2 * (0.08484 : ℝ)) = 300000 / (4 * 12726) ∧
      (5.89 : ℝ) < 300000 / (4 * 12726) ∧ (300000 : ℝ) / (4 * 12726) < 5.9 := by
  norm_num

/-! ## The storm (Notes, 3–4 July 1899): on the half-wave (nodal) reading -/

/-- On the half-wave reading the paper draws from his words about nodal points (each restart,
about every half hour, is the storm moving on half a wave), half a wave per half hour is a whole
wave per hour. -/
theorem storm_half_wave_reading (wave : ℝ) : (wave / 2) / (1 / 2) = wave := by
  field_simp

/-- Waves of 25 to 70 km at 300,000 km/s vibrate 12,000 and about 4,286 times a second (the
paper's "4,300 to 12,000"). -/
theorem storm_wave_numbers :
    (300000 : ℝ) / 25 = 12000 ∧ (4285 : ℝ) < 300000 / 70 ∧ (300000 : ℝ) / 70 < 4286 := by
  norm_num

end WhatTeslaSaw
