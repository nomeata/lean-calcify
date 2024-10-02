import Calcify.Basic

/--
info: Try this: calc
    x
    _ = x * x * (x * (x * x)) := (h x (x * x))
    _ = x * x * x := congrArg (fun a'2521 => x * x * a'2521) (Eq.symm (h x x))
-/
#guard_msgs in
theorem Equation14_implies_Equation232 (G: Type _) [inst : Mul G]
   (h: ∀ x y : G, x = y * (x * y)) : ∀ x : G, x = (x * x) * x := by
  intro x
  calcify
  exact @Eq.trans G x (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x x) (@HMul.hMul G G G (@instHMul G inst) x (@HMul.hMul G G G (@instHMul G inst) x x))) (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x x) x) (h x (@HMul.hMul G G G (@instHMul G inst) x x)) (@eq_of_heq G (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x x) (@HMul.hMul G G G (@instHMul G inst) x (@HMul.hMul G G G (@instHMul G inst) x x))) (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x x) x) ((fun (α : Type u_1) (α' : Type u_1) (e_1 : @Eq (Type u_1) α α') => @Eq.ndrec (Type u_1) α (fun (α' : Type u_1) => forall (β : Type u_1) (β' : Type u_1), (@Eq (Type u_1) β β') -> (forall (γ : Type u_1) (γ' : Type u_1), (@Eq (Type u_1) γ γ') -> (forall (self : HMul.{u_1, u_1, u_1} α β γ) (self' : HMul.{u_1, u_1, u_1} α' β' γ'), (@HEq (HMul.{u_1, u_1, u_1} α β γ) self (HMul.{u_1, u_1, u_1} α' β' γ') self') -> (forall (a2519 : α) (a'2519 : α'), (@HEq α a2519 α' a'2519) -> (forall (a2521 : β) (a'2521 : β'), (@HEq β a2521 β' a'2521) -> (@HEq γ (@HMul.hMul α β γ self a2519 a2521) γ' (@HMul.hMul α' β' γ' self' a'2519 a'2521))))))) (fun (β : Type u_1) (β' : Type u_1) (e_2 : @Eq (Type u_1) β β') => @Eq.ndrec (Type u_1) β (fun (β' : Type u_1) => forall (γ : Type u_1) (γ' : Type u_1), (@Eq (Type u_1) γ γ') -> (forall (self : HMul.{u_1, u_1, u_1} α β γ) (self' : HMul.{u_1, u_1, u_1} α β' γ'), (@HEq (HMul.{u_1, u_1, u_1} α β γ) self (HMul.{u_1, u_1, u_1} α β' γ') self') -> (forall (a2519 : α) (a'2519 : α), (@HEq α a2519 α a'2519) -> (forall (a2521 : β) (a'2521 : β'), (@HEq β a2521 β' a'2521) -> (@HEq γ (@HMul.hMul α β γ self a2519 a2521) γ' (@HMul.hMul α β' γ' self' a'2519 a'2521)))))) (fun (γ : Type u_1) (γ' : Type u_1) (e_3 : @Eq (Type u_1) γ γ') => @Eq.ndrec (Type u_1) γ (fun (γ' : Type u_1) => forall (self : HMul.{u_1, u_1, u_1} α β γ) (self' : HMul.{u_1, u_1, u_1} α β γ'), (@HEq (HMul.{u_1, u_1, u_1} α β γ) self (HMul.{u_1, u_1, u_1} α β γ') self') -> (forall (a2519 : α) (a'2519 : α), (@HEq α a2519 α a'2519) -> (forall (a2521 : β) (a'2521 : β), (@HEq β a2521 β a'2521) -> (@HEq γ (@HMul.hMul α β γ self a2519 a2521) γ' (@HMul.hMul α β γ' self' a'2519 a'2521))))) (fun (self : HMul.{u_1, u_1, u_1} α β γ) (self' : HMul.{u_1, u_1, u_1} α β γ) (e_4 : @HEq (HMul.{u_1, u_1, u_1} α β γ) self (HMul.{u_1, u_1, u_1} α β γ) self') => @Eq.ndrec (HMul.{u_1, u_1, u_1} α β γ) self (fun (self' : HMul.{u_1, u_1, u_1} α β γ) => forall (a2519 : α) (a'2519 : α), (@HEq α a2519 α a'2519) -> (forall (a2521 : β) (a'2521 : β), (@HEq β a2521 β a'2521) -> (@HEq γ (@HMul.hMul α β γ self a2519 a2521) γ (@HMul.hMul α β γ self' a'2519 a'2521)))) (fun (a2519 : α) (a'2519 : α) (e_5 : @HEq α a2519 α a'2519) => @Eq.ndrec α a2519 (fun (a'2519 : α) => forall (a2521 : β) (a'2521 : β), (@HEq β a2521 β a'2521) -> (@HEq γ (@HMul.hMul α β γ self a2519 a2521) γ (@HMul.hMul α β γ self a'2519 a'2521))) (fun (a2521 : β) (a'2521 : β) (e_6 : @HEq β a2521 β a'2521) => @Eq.ndrec β a2521 (fun (a'2521 : β) => @HEq γ (@HMul.hMul α β γ self a2519 a2521) γ (@HMul.hMul α β γ self a2519 a'2521)) (@HEq.refl γ (@HMul.hMul α β γ self a2519 a2521)) a'2521 (@eq_of_heq β a2521 a'2521 e_6)) a'2519 (@eq_of_heq α a2519 a'2519 e_5)) self' (@eq_of_heq (HMul.{u_1, u_1, u_1} α β γ) self self' e_4)) γ' e_3) β' e_2) α' e_1) G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G) (@instHMul G inst) (@instHMul G inst) (@HEq.refl (HMul.{u_1, u_1, u_1} G G G) (@instHMul G inst)) (@HMul.hMul G G G (@instHMul G inst) x x) (@HMul.hMul G G G (@instHMul G inst) x x) (@HEq.refl G (@HMul.hMul G G G (@instHMul G inst) x x)) (@HMul.hMul G G G (@instHMul G inst) x (@HMul.hMul G G G (@instHMul G inst) x x)) x (@heq_of_eq G (@HMul.hMul G G G (@instHMul G inst) x (@HMul.hMul G G G (@instHMul G inst) x x)) x (@Eq.symm G x (@HMul.hMul G G G (@instHMul G inst) x (@HMul.hMul G G G (@instHMul G inst) x x)) (h x x)))))
