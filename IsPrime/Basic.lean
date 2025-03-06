namespace Nat

def isPrime.loop (divisor n : Nat) (h₁ : divisor ≥ 2) (h₂ : n ≥ 2) : Bool :=
  if divisor ∣ n then
    false
  else if divisor ^ 2 ≤ n then
    loop (divisor + 1) n (Nat.le_trans h₁ (Nat.le_succ divisor)) h₂
  else
    true
termination_by n - divisor
decreasing_by
  next hpw2 =>
  have hltp : divisor < divisor ^ 2 := by
    conv => left; rw [← Nat.mul_one divisor]
    rw [Nat.pow_two]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_succ_le h₁) (Nat.lt_of_lt_of_le Nat.two_pos h₁)
  have hltn : divisor < n := Nat.lt_of_lt_of_le hltp hpw2
  simp [Nat.sub_add_eq]
  exact Nat.sub_one_lt <| Nat.ne_of_gt (Nat.sub_pos_of_lt hltn)

/-- `isPrime` tests whether a natural number is prime. -/
def isPrime (n : Nat) : Bool :=
  if h : n ≤ 1 then
    false
  else
    isPrime.loop 2 n (Nat.le_refl 2) (Nat.gt_of_not_le h)

end Nat
