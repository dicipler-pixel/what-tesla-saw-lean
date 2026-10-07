import WhatTeslaSaw.Laws
-- Deliberately false: half the capacity does not give the octave (it raises the tone by √2);
-- the octave needs a quarter (`WhatTeslaSaw.octave_iff`).
example : WhatTeslaSaw.freq 1 (1 / 2) = 2 * WhatTeslaSaw.freq 1 1 := by
  unfold WhatTeslaSaw.freq
  norm_num
