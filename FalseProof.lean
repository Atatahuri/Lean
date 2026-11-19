import Mathlib

example : (2 : ℤ) + 3 = 5 := by
  norm_num

example (a b : ℤ) (h : a = b) : a - b = 0 := by
  rw [h]
  ring

example (a b : ℤ) (h : a = b) :
    (a - b) * (a + b) = b * (a - b) := by
  calc
    (a - b) * (a + b) = a^2 - b^2 := by
      ring
    _ = a * b - b^2 := by
      rw [h]
      ring
    _ = b * (a - b) := by
      ring

example (x y z : ℤ) (hx : x ≠ 0)
    (h : x * y = x * z) : y = z := by
  exact mul_left_cancel₀ hx h

example (a b : ℤ) (h : a = b) : a + b = b := by
  have hproduct :
      (a - b) * (a + b) = (a - b) * b := by
    calc
      (a - b) * (a + b) = a^2 - b^2 := by
        ring
      _ = a * b - b^2 := by
        rw [h]
        ring
      _ = (a - b) * b := by
        ring

  have hnonzero : a - b ≠ 0 := by
    -- rw [h]
    -- simp
    sorry

  exact mul_left_cancel₀ hnonzero hproduct


  -- Nice! Here, I tried to prove that 2 = 1, by false proof of saying, a = b implies
-- (a - b) * (a + b) =  a^2 - b^2 = ab - b^2 = b * (a - b)
-- Then we cancel a -b, and we get a + b = b, so 2b = b, canceling b, we have 2 = 1.
--But Lean understood that a - b cannot be canceled, because both are zero.
