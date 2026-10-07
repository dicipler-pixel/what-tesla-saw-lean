# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **Tesla's laws are taken as given.** The period law `n = 1/(2π√(LC))`, the energy `CV²/2`, the
  magnification rule `m = pL/R` and the decay rate `γ = R/(2L)` are definitions in
  `WhatTeslaSaw/Laws.lean`. Nothing here derives them from electromagnetism. The theorems are what
  those laws imply.
* **Worked numbers are arithmetic checks.** `WhatTeslaSaw/Numbers.lean` checks the figures Tesla
  wrote down. It does not show that his measurements were right or what they mean physically.
  * The earth diameter `D = 12,726 km` in `earth_round_trip` is the paper's inference: it is the
    value that makes his 0.08484 s exact. It is not a figure in Tesla's text.
  * The storm theorems use the half-wave (nodal) reading: each restart is the storm moving on half
    a wave. The paper draws that reading from his words about nodal points; his records do not
    state the count directly, and the paper also tabulates the full-wave alternative.
* **The quarter-wave theorems assume the boundary condition.** `quarter_wave_odd_tones` shows that
  the condition `cos(2πfℓ/v) = 0` holds exactly at odd multiples of the lowest tone. The wave
  equation on the wire, and why a grounded-and-free wire obeys that condition, are not formalized.
* **The coupled pair is the lossless model.** `coupled_determinant` and `coupled_two_tones` work
  with the determinant of two lossless tuned circuits. Losses and the dynamics are not formalized.
* **The jet counts are two cases.** `nine_ten_jets` and `eight_ten_jets` compute the meetings for
  9 and 10 jets and for 8 and 10. The general count is not proved: neither the paper's rule that
  `n` and `n + 1` jets meet `n(n + 1)` times, nor the full count of `lcm(a, b)` meetings.
* **Not yet formalized** (listed in the paper):
  * isochronism: that every motion under a force proportional to the displacement repeats with a
    period independent of the amplitude (this needs the calculus of `cos`, planned for a later
    version);
  * the complex tone `ω = √(p² − γ²) − iγ` of a lossy circuit. The paper says Tesla's
    magnification is "the ratio of the real to the imaginary part" of `ω`; that is not right as
    written. Since `|ω| = p` and `Im ω = −γ`, his rule gives `m = p/(2γ) = |ω|/(2|Im ω|)`
    (`mag_eq_tone_over_twice_decay`), while `Re ω/|Im ω| = √(p² − γ²)/γ` is close to `2m` for small
    losses;
  * frequency values computed with the true `π` (for example 251,646 per second for US 645,576);
  * his other worked figures listed in the paper's §13–§14 that are not in `Numbers.lean`.
* **The original file.** `TeslaCore_v3.lean` is kept byte-identical to the file printed in the
  paper. Its statements are over natural numbers and integers with quantities scaled to whole
  units, so they are special cases of the real statements; several are one direction of what the
  real library proves in both directions, and `storm_speed` there is an identity about natural
  numbers that checks no storm figure. Use `WhatTeslaSaw` for the full statements.
* No physical interpretation is formalized. The readings in the paper (the storm, the earth's
  diameter crossing, the non-Hermitian language, his own accounts) are the paper's, not Lean's.

Formalization is evidence for the mathematics, not for the physical interpretation.
