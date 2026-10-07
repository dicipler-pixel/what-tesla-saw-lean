<div align="center">

# What Tesla Saw — Lean proofs

**Tesla's own circuit laws, and the numbers he wrote down, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/what-tesla-saw-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/what-tesla-saw-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-76-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Mathlib](https://img.shields.io/badge/uses-Mathlib-8A2BE2)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## The idea in one line

Tesla stated his circuit laws himself: the period law `n = 1/(2π√(LC))`, his tuning rule, the
octave at a quarter of the capacity, and the magnification `m = pL/R`. He also wrote his numbers
down, in the Colorado Springs Notes and in his patents. The paper walks his record and checks each
step against his own laws. Here Lean proves what those laws imply, with every hypothesis written
out and both directions of every "exactly when", and checks his arithmetic exactly over the real
numbers. It does not prove the laws themselves or the paper's physical readings.

## What is proved

The first column follows the paper's own "Lean list" (in *What his records fix, what stays open,
and the Lean list*) and its section names.

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Lean list 1; Notes, 3 July 1899 | **The octave.** At the same self-induction, a quarter of the capacity doubles the frequency, and only a quarter does; more capacity always lowers the tone; 48 jars become 12 | `octave_quarter_capacity`, `octave_iff`, `freq_strictAntiOn`, `octave_jars` |
| Lean list 2 | **Tuning.** Two circuits vibrate at the same frequency exactly when `L₁C₁ = L₂C₂` | `tuning_rule` |
| Lean list 3; US 512,340 | **Energy** `CV²/2`. A quarter of the capacity holds a quarter of the energy (his octave "had only 1/4 of the energy"); the ratio of energies is the square of the ratio of voltages, and `(50/0.1)² = 250,000` | `energy_quarter_capacity`, `energy_ratio`, `bifilar_energy_ratio` |
| Lean list 4; US 685,012 | **Magnification** `m = pL/R`. Halving the resistance doubles it; it falls strictly as the resistance grows; it equals `p/(2γ)` with decay rate `γ = R/(2L)` | `halving_resistance_doubles_mag`, `mag_strictAntiOn`, `mag_eq_tone_over_twice_decay` |
| Lean list 5; US 593,138 | **The quarter wave.** The condition `cos(2πfℓ/v) = 0` holds exactly when `4ℓf` is an odd multiple of `v`, so even multiples of the lowest tone never satisfy it; on a quarter-wave wire one end is at zero and the other at the maximum; 185,000 ÷ 925 = 200 miles, a quarter of it 50 | `quarter_wave_odd_tones`, `quarter_wave_even_forbidden`, `quarter_wave_ends`, `quarter_wave_1897` |
| Lean list 6; US 787,412 | **The earth.** 471,240 km/s is `(3.1416/2) × 300,000`; 0.08484 s is `2 × 12,726 ÷ 300,000`; in that time the surface point goes exactly once round (`471,240 × 0.08484 = 3.1416 × 12,726`); the lowest tone `1 ÷ (2 × 0.08484)` lies between 5.89 and 5.9 | `earth_surface_speed`, `earth_round_trip`, `earth_once_round`, `earth_once_round_numbers`, `earth_lowest_tone` |
| Lean list 7; US 416,194 | **Equal split.** `4ab ≤ (a + b)²`, with equality exactly when `a = b`: 900 against 2,500 from the same total of 100 | `equal_split`, `equal_split_eq_iff`, `equal_split_numbers` |
| Lean list 9; US 609,246 | **Jets.** 9 and 10 jets meet at 90 separate instants a turn; 8 and 10 at only 40 | `nine_ten_jets`, `eight_ten_jets` |
| Lean list 10; US 1,061,206 and 1,209,359 | **The turbine.** Under a square drag law the work `u(v − u)²` peaks at one third of the fluid speed, and only there; under a linear law `u(v − u)` peaks at one half, and only there | `turbine_square_law_third`, `turbine_square_law_eq_iff`, `turbine_linear_law_half`, `turbine_linear_law_eq_iff` |
| His two coupled circuits | **Two tones.** For two tuned circuits coupled at `k`, the determinant factors as `(1 − ya(1 + k))(1 − ya(1 − k))`; for `0 < k < 1` the pair rings exactly at `ω² = 1/(a(1 ± k))`, never at the single tuned tone; the two tones are an exact octave only at `k = 3/5` | `coupled_determinant`, `coupled_two_tones`, `coupled_not_at_tuned_tone`, `coupled_octave_iff` |
| His two coupled circuits; Notes, November 1899 | **His coils.** His measured `L₁`, `L₂` and `M` give `k` between 0.589 and 0.590, and between 0.598 and 0.599 (both just under 3/5); `1 − k²` is 0.65 and 0.64; tuning needs 30 of his bottles | `coupling_his_first_M`, `coupling_his_second_M`, `coupling_one_minus_k_sq`, `thirty_bottles` |
| Before Colorado, 1886–1898 | Fifty per cent (US 359,748); 2,000 − 800 = 1,200 turns (US 390,721); two motor turns per generator turn (US 487,796) | `eddy_fifty_percent`, `motor_speed`, `motor_turns_per_generator_turn` |
| The storm: Notes, 3–4 July 1899, and US 787,412 | On the half-wave reading, half a wave per half hour is a wave per hour; waves of 25 to 70 km vibrate 12,000 and about 4,286 times a second | `storm_half_wave_reading`, `storm_wave_numbers` |

**Not yet proved:** Lean list 8, the constant period (a force proportional to the displacement
gives a period independent of the amplitude), and the general jet count of Lean list 9 (`n` and
`n + 1` jets meet `n(n + 1)` times). What is not proved, and why, is in
[`LIMITATIONS.md`](LIMITATIONS.md).

Files: [`WhatTeslaSaw/Laws.lean`](WhatTeslaSaw/Laws.lean) (25 theorems: his laws, as
definitions, and what follows from them), [`WhatTeslaSaw/Numbers.lean`](WhatTeslaSaw/Numbers.lean)
(18 theorems: his figures, exact over the real numbers) and
[`WhatTeslaSaw/Jets.lean`](WhatTeslaSaw/Jets.lean) (2 theorems).

## The file printed in the paper

[`TeslaCore_v3.lean`](TeslaCore_v3.lean) is the file the paper prints in its Evidence section,
kept byte-identical (31 theorems, core Lean, no Mathlib). It is built and checked here on every
push too. Its statements are over whole numbers with quantities scaled to whole units; the
`WhatTeslaSaw` library restates them over the real numbers, in both directions where the paper
says "exactly". The correspondence, and the file's hash, are in [`PROVENANCE.md`](PROVENANCE.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build** against Lean v4.34.1 and Mathlib v4.34.1.
2. **Independent replay** of every module in Lean's separate kernel checker.
3. **Axiom audit**: every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
4. **False controls**: three deliberately false statements must fail, for a mathematical reason:
   half the capacity as the octave, one half as the square-law turbine's best speed, and 6 × 9 = 54
   meetings for six and nine jets.

## The paper

*What Tesla Saw. His laws, his numbers, and what they fix: the Colorado Springs Notes, all 112 of
his US patents, his own accounts, and the Belgrade archive*, Jeromie Beasley, September 2026.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
