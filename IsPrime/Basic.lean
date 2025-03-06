namespace Nat

def isPrime.loop (n divisor : Nat) (h₁ : n ≥ 2) (h₂ : divisor ≥ 2) : Bool :=
  if divisor ^ 2 ≤ n then
    if divisor ∣ n then
      false
    else
      loop n (divisor + 1) h₁ (Nat.le_trans h₂ (Nat.le_succ divisor))
  else
    true
termination_by n - divisor
decreasing_by
  next hpw2 _ =>
  have hltp : divisor < divisor ^ 2 := by
    conv => left; rw [← Nat.mul_one divisor]
    rw [Nat.pow_two]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_succ_le h₂) (Nat.lt_of_lt_of_le Nat.two_pos h₂)
  have hltn : divisor < n := Nat.lt_of_lt_of_le hltp hpw2
  simp only [sub_add_eq]
  exact sub_one_lt <| ne_of_gt (Nat.sub_pos_of_lt hltn)

/-- `Nat.isPrime` tests whether a natural number is prime. -/
def isPrime (n : Nat) : Bool :=
  if h : n ≤ 1 then
    false
  else
    isPrime.loop n 2 (gt_of_not_le h) (Nat.le_refl 2)

end Nat
