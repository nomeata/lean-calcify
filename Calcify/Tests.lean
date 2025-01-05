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
    _ = coe (fact n * fact n) := (cast_mul (fact n) (fact n)).symm
    _ = coe (fact n) * coe (fact n) := cast_mul (fact n) (fact n)
-/
#guard_msgs in
example (n : Nat) : Gamma (coe n + 1) * Gamma (coe n + 1) = coe (fact n) * coe (fact n) := by
  calcify simp only [← cast_mul, Gamma_nat_eq_factorial]

end issue9

section issue10


-- could be improved

/--
info: Try this: ⏎
  conv =>
    tactic =>
      calc
        True ∧ True ↔ True
        _ = (True ↔ True) := congrArg (fun x => x ↔ True) (and_self True)
  refine of_eq_true (iff_self True)
-/
#guard_msgs in
example : (True ∧ True) ↔ True := by
  calcify simp

/--
info: Try this: calc
    True ∧ True
    _ = True := and_self True
-/
#guard_msgs in
example : (True ∧ True) = True := by
  calcify simp

/-- info: Try this: exact of_eq_true (iff_self True) -/
#guard_msgs in
example : True ↔ True := by
  show_term simp -- Expected proof of equality


end issue10
