import WhatTeslaSaw.Jets
-- Deliberately false: two sets of jets do not always meet a × b separate times a turn. Six and
-- nine share the factor 3 and meet only 18 times, not 6 × 9 = 54. His rule, one more nozzle in one
-- set than in the other, rules out a shared factor.
example : (WhatTeslaSaw.meetings 6 9).length = 54 := by decide
