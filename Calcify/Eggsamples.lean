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

/--
info: Try this: calc
    x * (y * (y * z * z))
    _ = x * y * x * (x * y * y) * (y * (y * z * z)) := (congrArg (fun a' => a' * (y * (y * z * z))) (h x (x * y) y))
    _ = x * y * x * (x * y * y) * (x * y * y * (y * z * z) * (y * z * z)) :=
      (congrArg (fun x_1 => x * y * x * (x * y * y) * (x_1 * (y * z * z))) (h y (x * y) z))
    _ = x * y * y := (h (x * y * y) (x * y * x) (y * z * z)).symm
-/
#guard_msgs in
theorem helper_lemma (G: Type _) [inst : Mul G] (h: ∀ x y z : G, x = (y * x) * ((x * z) * z)) : ∀ x y z : G, x * (y * ((y * z) * z)) = (x * y) * y := by
  intro x y z
  calcify
  exact
    @Eq.trans G
      (@HMul.hMul G G G (@instHMul G inst) x
        (@HMul.hMul G G G (@instHMul G inst) y
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
      (@HMul.hMul G G G (@instHMul G inst)
        (@HMul.hMul G G G (@instHMul G inst)
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
        (@HMul.hMul G G G (@instHMul G inst)
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
      (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
      (@Eq.trans G
        (@HMul.hMul G G G (@instHMul G inst) x
          (@HMul.hMul G G G (@instHMul G inst) y
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
        (@HMul.hMul G G G (@instHMul G inst)
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
          (@HMul.hMul G G G (@instHMul G inst) y
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
        (@HMul.hMul G G G (@instHMul G inst)
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
        (@eq_of_heq G
          (@HMul.hMul G G G (@instHMul G inst) x
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
          ((fun α α' e_1 =>
              @Eq.ndrec (Type u_1) α
                (fun α' =>
                  ∀ (β β' : Type u_1),
                    @Eq (Type u_1) β β' →
                      ∀ (γ γ' : Type u_1),
                        @Eq (Type u_1) γ γ' →
                          ∀ (self : HMul α β γ) (self' : HMul α' β' γ'),
                            @HEq (HMul α β γ) self (HMul α' β' γ') self' →
                              ∀ (a : α) (a' : α'),
                                @HEq α a α' a' →
                                  ∀ (a_1 : β) (a'_1 : β'),
                                    @HEq β a_1 β' a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α' β' γ' self' a' a'_1))
                (fun β β' e_2 =>
                  @Eq.ndrec (Type u_1) β
                    (fun β' =>
                      ∀ (γ γ' : Type u_1),
                        @Eq (Type u_1) γ γ' →
                          ∀ (self : HMul α β γ) (self' : HMul α β' γ'),
                            @HEq (HMul α β γ) self (HMul α β' γ') self' →
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 : β) (a'_1 : β'),
                                    @HEq β a_1 β' a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α β' γ' self' a' a'_1))
                    (fun γ γ' e_3 =>
                      @Eq.ndrec (Type u_1) γ
                        (fun γ' =>
                          ∀ (self : HMul α β γ) (self' : HMul α β γ'),
                            @HEq (HMul α β γ) self (HMul α β γ') self' →
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α β γ' self' a' a'_1))
                        (fun self self' e_4 =>
                          @Eq.ndrec (HMul α β γ) self
                            (fun self' =>
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self' a' a'_1))
                            (fun a a' e_5 =>
                              @Eq.ndrec α a
                                (fun a' =>
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self a' a'_1))
                                (fun a_1 a' e_6 =>
                                  @Eq.ndrec β a_1
                                    (fun a' =>
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self a a'))
                                    (@HEq.refl γ (@HMul.hMul α β γ self a a_1)) a'
                                    (@eq_of_heq β a_1 a' e_6))
                                a' (@eq_of_heq α a a' e_5))
                            self' (@eq_of_heq (HMul α β γ) self self' e_4))
                        γ' e_3)
                    β' e_2)
                α' e_1)
            G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G)
            (@instHMul G inst) (@instHMul G inst) (@HEq.refl (HMul G G G) (@instHMul G inst)) x
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@heq_of_eq G x
              (@HMul.hMul G G G (@instHMul G inst)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
              (h x (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            (@HEq.refl G
              (@HMul.hMul G G G (@instHMul G inst) y
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z)
                  z)))))
        (@eq_of_heq G
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
          ((fun α α' e_1 =>
              @Eq.ndrec (Type u_1) α
                (fun α' =>
                  ∀ (β β' : Type u_1),
                    @Eq (Type u_1) β β' →
                      ∀ (γ γ' : Type u_1),
                        @Eq (Type u_1) γ γ' →
                          ∀ (self : HMul α β γ) (self' : HMul α' β' γ'),
                            @HEq (HMul α β γ) self (HMul α' β' γ') self' →
                              ∀ (a : α) (a' : α'),
                                @HEq α a α' a' →
                                  ∀ (a_1 : β) (a'_1 : β'),
                                    @HEq β a_1 β' a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α' β' γ' self' a' a'_1))
                (fun β β' e_2 =>
                  @Eq.ndrec (Type u_1) β
                    (fun β' =>
                      ∀ (γ γ' : Type u_1),
                        @Eq (Type u_1) γ γ' →
                          ∀ (self : HMul α β γ) (self' : HMul α β' γ'),
                            @HEq (HMul α β γ) self (HMul α β' γ') self' →
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 : β) (a'_1 : β'),
                                    @HEq β a_1 β' a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α β' γ' self' a' a'_1))
                    (fun γ γ' e_3 =>
                      @Eq.ndrec (Type u_1) γ
                        (fun γ' =>
                          ∀ (self : HMul α β γ) (self' : HMul α β γ'),
                            @HEq (HMul α β γ) self (HMul α β γ') self' →
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                        (@HMul.hMul α β γ' self' a' a'_1))
                        (fun self self' e_4 =>
                          @Eq.ndrec (HMul α β γ) self
                            (fun self' =>
                              ∀ (a a' : α),
                                @HEq α a α a' →
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self' a' a'_1))
                            (fun a a' e_5 =>
                              @Eq.ndrec α a
                                (fun a' =>
                                  ∀ (a_1 a'_1 : β),
                                    @HEq β a_1 β a'_1 →
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self a' a'_1))
                                (fun a_1 a' e_6 =>
                                  @Eq.ndrec β a_1
                                    (fun a' =>
                                      @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                        (@HMul.hMul α β γ self a a'))
                                    (@HEq.refl γ (@HMul.hMul α β γ self a a_1)) a'
                                    (@eq_of_heq β a_1 a' e_6))
                                a' (@eq_of_heq α a a' e_5))
                            self' (@eq_of_heq (HMul α β γ) self self' e_4))
                        γ' e_3)
                    β' e_2)
                α' e_1)
            G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G)
            (@instHMul G inst) (@instHMul G inst) (@HEq.refl (HMul G G G) (@instHMul G inst))
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
            (@HEq.refl G
              (@HMul.hMul G G G (@instHMul G inst)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)))
            (@HMul.hMul G G G (@instHMul G inst) y
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            ((fun α α' e_1 =>
                @Eq.ndrec (Type u_1) α
                  (fun α' =>
                    ∀ (β β' : Type u_1),
                      @Eq (Type u_1) β β' →
                        ∀ (γ γ' : Type u_1),
                          @Eq (Type u_1) γ γ' →
                            ∀ (self : HMul α β γ) (self' : HMul α' β' γ'),
                              @HEq (HMul α β γ) self (HMul α' β' γ') self' →
                                ∀ (a : α) (a' : α'),
                                  @HEq α a α' a' →
                                    ∀ (a_1 : β) (a'_1 : β'),
                                      @HEq β a_1 β' a'_1 →
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                          (@HMul.hMul α' β' γ' self' a' a'_1))
                  (fun β β' e_2 =>
                    @Eq.ndrec (Type u_1) β
                      (fun β' =>
                        ∀ (γ γ' : Type u_1),
                          @Eq (Type u_1) γ γ' →
                            ∀ (self : HMul α β γ) (self' : HMul α β' γ'),
                              @HEq (HMul α β γ) self (HMul α β' γ') self' →
                                ∀ (a a' : α),
                                  @HEq α a α a' →
                                    ∀ (a_1 : β) (a'_1 : β'),
                                      @HEq β a_1 β' a'_1 →
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                          (@HMul.hMul α β' γ' self' a' a'_1))
                      (fun γ γ' e_3 =>
                        @Eq.ndrec (Type u_1) γ
                          (fun γ' =>
                            ∀ (self : HMul α β γ) (self' : HMul α β γ'),
                              @HEq (HMul α β γ) self (HMul α β γ') self' →
                                ∀ (a a' : α),
                                  @HEq α a α a' →
                                    ∀ (a_1 a'_1 : β),
                                      @HEq β a_1 β a'_1 →
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ'
                                          (@HMul.hMul α β γ' self' a' a'_1))
                          (fun self self' e_4 =>
                            @Eq.ndrec (HMul α β γ) self
                              (fun self' =>
                                ∀ (a a' : α),
                                  @HEq α a α a' →
                                    ∀ (a_1 a'_1 : β),
                                      @HEq β a_1 β a'_1 →
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                          (@HMul.hMul α β γ self' a' a'_1))
                              (fun a a' e_5 =>
                                @Eq.ndrec α a
                                  (fun a' =>
                                    ∀ (a_1 a'_1 : β),
                                      @HEq β a_1 β a'_1 →
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                          (@HMul.hMul α β γ self a' a'_1))
                                  (fun a_1 a' e_6 =>
                                    @Eq.ndrec β a_1
                                      (fun a' =>
                                        @HEq γ (@HMul.hMul α β γ self a a_1) γ
                                          (@HMul.hMul α β γ self a a'))
                                      (@HEq.refl γ (@HMul.hMul α β γ self a a_1)) a'
                                      (@eq_of_heq β a_1 a' e_6))
                                  a' (@eq_of_heq α a a' e_5))
                              self' (@eq_of_heq (HMul α β γ) self self' e_4))
                          γ' e_3)
                      β' e_2)
                  α' e_1)
              G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G) G G (@Eq.refl (Type u_1) G)
              (@instHMul G inst) (@instHMul G inst) (@HEq.refl (HMul G G G) (@instHMul G inst)) y
              (@HMul.hMul G G G (@instHMul G inst)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
              (@heq_of_eq G y
                (@HMul.hMul G G G (@instHMul G inst)
                  (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
                  (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
                (h y (@HMul.hMul G G G (@instHMul G inst) x y) z))
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)
              (@HEq.refl G
                (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z)
                  z))))))
      (@Eq.symm G (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
        (@HMul.hMul G G G (@instHMul G inst)
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y))
          (@HMul.hMul G G G (@instHMul G inst)
            (@HMul.hMul G G G (@instHMul G inst)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
              (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z))
            (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
        (h (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) y)
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) x y) x)
          (@HMul.hMul G G G (@instHMul G inst) (@HMul.hMul G G G (@instHMul G inst) y z) z)))
