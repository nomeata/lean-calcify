import Calcify.Basic

section issue9

axiom coe  : Nat → Int
axiom cast_mul : (m n : Nat) → coe (m * n) = coe m * coe n
axiom Gamma : Int → Int
axiom fact: Nat → Nat
axiom Gamma_nat_eq_factorial (n : Nat) : Gamma (coe n + 1) = coe (fact n)


/--
info: Try this: calc
    Gamma (coe n + 1) * Gamma (coe n + 1)
    _ = coe (fact n) * Gamma (coe n + 1) := (congrArg (fun x => x * Gamma (coe n + 1)) (Gamma_nat_eq_factorial n))
    _ = coe (fact n) * coe (fact n) := (congrArg (fun x => coe (fact n) * x) (Gamma_nat_eq_factorial n))
    _ = coe (fact n * fact n) := Calcify.Tests._auxLemma.1 (fact n) (fact n)
-/
#guard_msgs in
example (n : Nat) : Gamma (coe n + 1) * Gamma (coe n + 1) = coe (fact n * fact n) := by
  calcify simp only [← cast_mul, Gamma_nat_eq_factorial]

end issue9
