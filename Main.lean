import IsPrime

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "Enter a natural number."
  let input ← stdin.getLine

  match input.trim.toNat? with
  | some n =>
    if Nat.isPrime n then
      stdout.putStrLn s!"{n} is a prime number."
    else
      stdout.putStrLn s!"{n} isn't a prime number."
  | none =>
    stdout.putStrLn s!"You didn't enter a natural number."
