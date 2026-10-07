# Provenance

## `TeslaCore_v3.lean`

Byte-identical to `TeslaCore_v3.lean` of 28 September 2026 (Jeromie Beasley's Google Drive, and
the same file inside `What_Tesla_Saw_research_v1.zip`, `proofs/TeslaCore_v3.lean`), which the
paper prints in full in its Evidence section.

| File | SHA-256 |
| :--- | :--- |
| `TeslaCore_v3.lean` | `5e5193475bdf657a7b89892a1c6620836f09782dc4e85469fe04b889580b7ceb` |

It was written for core Lean 4.24 (no Mathlib). On 7 October 2026 it was compiled unchanged with
Lean 4.24.0 and with Lean 4.34.1; all 31 theorems were accepted, and `#print axioms` reported only
`propext`, `Classical.choice` and `Quot.sound` (17 theorems use no axiom at all, under both versions). Here it is built
with Lean 4.34.1 on every push.

## `WhatTeslaSaw/`

New in this repository (7 October 2026): the paper's claims restated over the real numbers, with
Tesla's laws as definitions, every hypothesis explicit, and both directions of each "exactly when"
proved where the paper claims it. The correspondence with the original file:

| `TeslaCore_v3` | `WhatTeslaSaw` |
| :--- | :--- |
| `tuning_rule` (ℕ, one direction) | `Laws.tuning_rule` (ℝ, both directions) |
| `octave_quarter_capacity`, `octave_jars` | `Laws.octave_quarter_capacity`, `Laws.octave_iff`, `Numbers.octave_jars` |
| `energy_scales_with_capacity` (no ½) | `Laws.energy_quarter_capacity`, `Laws.energy_ratio` |
| `cooling_doubles_magnification` | `Laws.halving_resistance_doubles_mag`, `Laws.mag_strictAntiOn` |
| `magnification_is_tone_over_decay` | `Laws.mag_eq_tone_over_twice_decay` |
| `equal_split` (ℕ, bound only), `equal_split_numbers` | `Laws.equal_split`, `Laws.equal_split_eq_iff`, `Numbers.equal_split_numbers` |
| `turbine_square_law_*` (ℤ) | `Laws.turbine_square_law_identity`, `_third`, `_eq_iff` |
| `turbine_linear_law_*` (ℤ) | `Laws.turbine_linear_law_half`, `_eq_iff` |
| `coupled_pair_two_tones` (ℤ identity) | `Laws.coupled_determinant`, `coupled_two_tones`, `coupled_not_at_tuned_tone`, `coupled_octave_iff` |
| `quarter_wave_odd_tones` (condition assumed) | `Laws.quarter_wave_odd_tones` (iff), `Laws.quarter_wave_even_forbidden`, `Laws.quarter_wave_ends` |
| worked numbers (ℕ, scaled) | `Numbers.*` (exact over ℝ) |
| `nine_ten_jets`, `eight_ten_jets`, `meetings` | `Jets.*` (same definition) |
| `storm_speed` | `Numbers.storm_half_wave_reading`, `Numbers.storm_wave_numbers` |
| `sq_nonneg'` | Mathlib's `sq_nonneg` |

## Sources

The paper: *What Tesla Saw. His laws, his numbers, and what they fix: the Colorado Springs Notes,
all 112 of his US patents, his own accounts, and the Belgrade archive*, Jeromie Beasley,
September 2026 (`what_tesla_saw_v1.pdf`, 28 September 2026).
