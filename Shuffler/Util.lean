-- pair the result with the equation that produced it.
def Except.attach (x : Except ε α) : Except ε { a // x = .ok a } :=
  match x with
  | .ok a => .ok ⟨a, rfl⟩
  | .error e => .error e
