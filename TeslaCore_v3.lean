/-
  SCRIPT: TESLA_CORE_LEAN_V3
  Tesla's own laws and worked numbers, from his Colorado Springs Notes (1899-1900) and US patents.
  Core Lean 4 only (no Mathlib), kernel-checked. Exact statements over natural numbers:
  quantities are scaled to whole units so every step is exact.
-/
namespace Tesla

/-! ## His worked numbers, checked exactly -/

/-- 359,748 (1887): 6 inches of iron in a 12-inch core cuts the eddy currents to fifty per cent. -/
theorem eddy_fifty_percent : 6 * 100 / 12 = 50 := by decide

/-- 390,721 (1888): poles turned 2,000 times, armature 800 times, motor 1,200 times. -/
theorem motor_speed : 2000 - 800 = 1200 := by decide

/-- 416,194 (1889): field 90 and armature 10 give 900; 50 and 50 give 2,500. -/
theorem equal_split_numbers : 90 * 10 = 900 ∧ 50 * 50 = 2500 ∧ 90 + 10 = 50 + 50 := by decide

/-- 512,340 (1894): 0.1 V to 50 V between neighbouring turns stores (50 / 0.1)^2 = 250,000 times the energy.
    In tenths of a volt: 1 to 500. -/
theorem bifilar_energy_ratio : (500 / 1) ^ 2 = 250000 := by decide

/-- 487,796 (1892): twelve reversals a turn on a six-pole motor gives two motor turns per generator turn. -/
theorem motor_turns_per_generator_turn : 12 / 6 = 2 := by decide

/-! ## His equal-split law (416,194), in general -/

/-- With a fixed total, the product of the two parts is greatest when they are equal:
    4ab ≤ (a + b)^2 for all whole numbers. -/
theorem equal_split (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (a + (a + d)) * (a + (a + d)) = 4 * (a * (a + d)) + d * d := by
      have hc := Nat.mul_comm d a
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (b + d + b) * (b + d + b) = 4 * ((b + d) * b) + d * d := by
      have hc := Nat.mul_comm d b
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega

/-! ## His octave rule (Notes, 3 Jul 1899) -/

/-- Period law in squared form: n^2 * L * C is the same constant K for every circuit.
    If a circuit at frequency n and one at 2n share L, the second needs a quarter of the capacity:
    "An octave would require only 12 jars on each side" instead of 48. -/
theorem octave_quarter_capacity (n L C₁ C₂ K : Nat) (hn : 0 < n) (hL : 0 < L)
    (h₁ : n * n * (L * C₁) = K) (h₂ : (2 * n) * (2 * n) * (L * C₂) = K) : C₁ = 4 * C₂ := by
  have hpos : 0 < n * n * L := Nat.mul_pos (Nat.mul_pos hn hn) hL
  have e : n * n * L * C₁ = n * n * L * (4 * C₂) := by
    have h₂' : (2 * n) * (2 * n) * (L * C₂) = n * n * L * (4 * C₂) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [← Nat.mul_assoc] at h₁
    omega
  exact Nat.eq_of_mul_eq_mul_left hpos e

/-- His 3 July numbers: 48 jars at the fundamental, 12 at the octave. -/
theorem octave_jars : 48 = 4 * 12 := by decide

/-- "the octave vibration had only 1/4 of the energy": energy ∝ C V^2, so four times the capacity at the
    same voltage holds four times the energy. -/
theorem energy_scales_with_capacity (c V : Nat) : (4 * c) * (V * V) = 4 * (c * (V * V)) := by
  rw [Nat.mul_assoc]

/-! ## His tuning rule L₁C₁ = L₂C₂ -/

/-- Two circuits share a period exactly when they share L·C (period law n^2·L·C = K, n > 0). -/
theorem tuning_rule (n₁ n₂ L₁ C₁ L₂ C₂ K : Nat)
    (h₁ : n₁ * n₁ * (L₁ * C₁) = K) (h₂ : n₂ * n₂ * (L₂ * C₂) = K) (hK : 0 < K) :
    n₁ = n₂ → L₁ * C₁ = L₂ * C₂ := by
  intro h
  subst h
  have hn : 0 < n₁ * n₁ := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · subst h0; simp at h₁; omega
    · exact Nat.mul_pos h0 h0
  exact Nat.eq_of_mul_eq_mul_left hn (h₁.trans h₂.symm)

/-! ## His magnification rule m = pL/R (Notes; 462,418; 685,012) -/

/-- Halving the resistance doubles the magnification: if m·(2r) = pL and m'·r = pL then m' = 2m. -/
theorem cooling_doubles_magnification (m m' r pL : Nat) (hr : 0 < r)
    (h : m * (2 * r) = pL) (h' : m' * r = pL) : m' = 2 * m := by
  have e : m' * r = (2 * m) * r := by
    rw [h', ← h, Nat.mul_left_comm, Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_right hr e

/-! ## His quarter-wave rule (593,138; 649,621; 787,412) -/

/-- A wire grounded at one end and free at the other rings when its length is an odd number of
    quarter waves: 4·ℓ·f = (2k+1)·v. With the fundamental 4·ℓ·f₀ = v, every tone is an odd multiple:
    f = (2k+1)·f₀. The same law with the earth's diameter for ℓ is his rule in 787,412. -/
theorem quarter_wave_odd_tones (ℓ v f f₀ k : Nat) (hℓ : 0 < ℓ)
    (hf : 4 * ℓ * f = (2 * k + 1) * v) (h₀ : 4 * ℓ * f₀ = v) : f = (2 * k + 1) * f₀ := by
  have hpos : 0 < 4 * ℓ := Nat.mul_pos (by decide) hℓ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hf, ← h₀]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- 593,138 (1897): 185,000 miles a second at 925 a second gives 200-mile waves and a 50-mile quarter wave. -/
theorem quarter_wave_1897 : 185000 / 925 = 200 ∧ 200 / 4 = 50 := by decide

/-! ## His circuit controller (609,246) -/

/-- Meeting instants of two symmetric sets of a and b jets turning past each other, counted in
    units of 1/(a·b) of a turn: the distinct values of (b·i + (a·b - a)·j) mod (a·b). -/
def meetings (a b : Nat) : List Nat :=
  ((List.range a).flatMap fun i => (List.range b).map fun j => (b * i + (a * b - a) * j) % (a * b)).eraseDups

/-- "nine and ... ten. Then by one revolution ... there will be ninety makes and breaks." -/
theorem nine_ten_jets : (meetings 9 10).length = 90 := by decide

/-- Counts sharing a factor meet two at a time: 8 and 10 jets give only 40 separate instants. -/
theorem eight_ten_jets : (meetings 8 10).length = 40 := by decide

/-! ## The storm (Notes 3-4 Jul 1899; 787,412; 1904) -/

/-- Restarts every half hour, each one half a wave: waves of 25 to 70 km give 25 to 70 km per hour.
    In km per hour: (λ / 2) per half hour = λ per hour. -/
theorem storm_speed : (25 / 2) * 2 + (25 % 2) = 25 ∧ (70 / 2) * 2 = 70 := by decide


theorem sq_nonneg' (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at this

/-- 1,061,206: work = force × runner speed u, fluid speed v. If the drag grows as the SQUARE of the
    relative speed, work ∝ u·(v-u)². Identity: 4v³ - 27u(v-u)² = (3u - v)²·(4v - 3u). -/
theorem turbine_square_law_identity (u v : Int) :
    4 * (v * v * v) - 27 * u * ((v - u) * (v - u)) = (3*u - v) * (3*u - v) * (4*v - 3*u) := by
  grind

/-- So with 0 ≤ u ≤ v, 27·u·(v-u)² ≤ 4·v³: the square law's best runner speed is one third. -/
theorem turbine_square_law_third (u v : Int) (hu : 0 ≤ u) (huv : u ≤ v) :
    27 * u * ((v - u) * (v - u)) ≤ 4 * (v * v * v) := by
  have h := turbine_square_law_identity u v
  have h3 : 0 ≤ (3*u - v) * (3*u - v) * (4*v - 3*u) :=
    Int.mul_nonneg (sq_nonneg' _) (by omega)
  omega

/-- ... reached exactly at u = v/3: v = 3w, u = w. -/
theorem turbine_square_law_attained (w : Int) :
    27 * w * ((3*w - w) * (3*w - w)) = 4 * ((3*w) * (3*w) * (3*w)) := by
  grind

/-- Drag LINEAR in relative speed (his 1,209,359 finding): work ∝ u·(v-u), and 4·u·(v-u) ≤ v²,
    reached at u = v/2: the best runner speed is one half, as 1,061,206 states. -/
theorem turbine_linear_law_half (u v : Int) : 4 * (u * (v - u)) ≤ v * v := by
  have h : v * v - 4 * (u * (v - u)) = (v - 2*u) * (v - 2*u) := by grind
  have := sq_nonneg' (v - 2*u)
  omega

theorem turbine_linear_law_attained (w : Int) : 4 * (w * (2*w - w)) = (2*w) * (2*w) := by
  grind



/-! ## His earth numbers (787,412): exact with π = 3.1416, c = 300,000 km/s, D = 12,726 km -/

/-- Surface speed "471,240 kilometers per second" = (π/2)·c with π = 3.1416: 31416·300000 = 471240·20000. -/
theorem earth_surface_speed : 31416 * 300000 = 471240 * 20000 := by decide

/-- Wave-train time "0.08484 of a second" = 2D/c with D = 12,726 km (time in units of 10⁻⁵ s). -/
theorem earth_round_trip : 2 * 12726 * 100000 = 8484 * 300000 := by decide

/-- In that time the surface footprint covers πD, once round the earth: 471,240 × 0.08484 = 3.1416 × 12,726. -/
theorem earth_once_round : 471240 * 8484 = 31416 * 12726 * 10 := by decide

/-- "The lowest frequency would appear to be six per second": 1/(2 × 0.08484) lies between 5 and 6. -/
theorem earth_lowest_tone : 5 * 16968 < 100000 ∧ 100000 < 6 * 16968 := by decide

/-! ## His circuits as lossy (non-Hermitian) systems -- our language, his laws -/

/-- His magnifying factor is the ratio of a lossy circuit's tone to twice its decay rate:
    from m·R = p·L (his m = pL/R) and 2·L·γ = R (decay rate γ = R/2L), m·(2γ) = p. -/
theorem magnification_is_tone_over_decay (m p L R γ : Nat) (hL : 0 < L)
    (hm : m * R = p * L) (hγ : 2 * L * γ = R) : m * (2 * γ) = p := by
  subst hγ
  apply Nat.eq_of_mul_eq_mul_left hL
  rw [Nat.mul_comm L p, ← hm]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Two circuits tuned by his rule L₁C₁ = L₂C₂ = a and coupled with k² = M²/(L₁L₂):
    the determinant (1 − y·a)² − (k·y·a)² (y = ω²) splits into two factors, so the pair
    rings at two tones, y·a = 1/(1+k) and y·a = 1/(1−k), never at the single tuned tone. -/
theorem coupled_pair_two_tones (a y k : Int) :
    (1 - y*a) * (1 - y*a) - (k*y*a) * (k*y*a) = (1 - y*a*(1+k)) * (1 - y*a*(1-k)) := by
  grind

/-- His November 1899 coils: L₁ = 230,945 cm, L₂ = 9,023,000 cm, M = 851,021 cm.
    The coupling squared k² = M²/(L₁L₂) lies between 0.34 and 0.36. -/
theorem coupling_his_first_M :
    34 * (230945 * 9023000) < 100 * (851021 * 851021) ∧
    100 * (851021 * 851021) < 36 * (230945 * 9023000) := by decide

/-- The same with his second reading M = 863,313 cm. -/
theorem coupling_his_second_M :
    34 * (230945 * 9023000) < 100 * (863313 * 863313) ∧
    100 * (863313 * 863313) < 36 * (230945 * 9023000) := by decide

/-- Tuning by his rule with C₂ = 622 cm needs C₁ = L₂C₂/L₁, which lies between 30 and 30.02 of his
    0.0009 mfd bottles (one bottle = 810 cm): 230945·24300 ≤ 9023000·622 ≤ 230945·24316. -/
theorem thirty_bottles :
    230945 * (30 * 810) ≤ 9023000 * 622 ∧ 9023000 * 622 ≤ 230945 * 24316 := by decide

end Tesla
