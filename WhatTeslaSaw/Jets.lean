/-
What Tesla Saw (Jeromie Beasley): Tesla's circuit controller (US 609,246, 1898).

Two symmetric sets of `a` and `b` jets turning past each other meet at instants that, counted in
units of `1/(ab)` of a turn, are the distinct values of `(b·i + (ab − a)·j) mod ab`. The list
`meetings a b` enumerates them; the theorems count them for his two cases by computation in the
kernel. The general count (`lcm a b` meetings) is not proved here.
-/
import Mathlib.Data.List.Basic

namespace WhatTeslaSaw

/-- The meeting instants of `a` and `b` jets, in units of `1/(ab)` of a turn. -/
def meetings (a b : ℕ) : List ℕ :=
  ((List.range a).flatMap fun i =>
    (List.range b).map fun j => (b * i + (a * b - a) * j) % (a * b)).eraseDups

/-- "Nine and ... ten. Then by one revolution ... there will be ninety makes and breaks." -/
theorem nine_ten_jets : (meetings 9 10).length = 90 := by decide

/-- Counts sharing a factor meet two at a time: 8 and 10 jets give only 40 separate instants. -/
theorem eight_ten_jets : (meetings 8 10).length = 40 := by decide

end WhatTeslaSaw
