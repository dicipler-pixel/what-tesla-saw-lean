import WhatTeslaSaw.Laws
-- Deliberately false: under the square drag law the best runner speed is not one half of the
-- fluid speed. At v = 1 the work at u = 1/3 (4/27) exceeds the work at u = 1/2 (1/8).
example : (1 / 3 : ℝ) * (1 - 1 / 3) ^ 2 ≤ (1 / 2) * (1 - 1 / 2) ^ 2 := by norm_num
