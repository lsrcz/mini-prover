Inductive True : Type :=
  | I : True.

Inductive False : Type :=.

Definition not (A:Type) : Type :=
  A -> False.

Inductive and (A:Type) (B:Type) : Type :=
  | conj : A -> B -> and A B.

Definition proj1 (A:Type) (B:Type) (H:and A B) : A :=
  match H as H0 in and _ _ return A with
  | conj _ _ HA HB => HA
  end.

Definition proj2 (A:Type) (B:Type) (H:and A B) : B :=
  match H as H0 in and _ _ return B with
  | conj _ _ HA HB => HB
  end.

Inductive or (A:Type) (B:Type) : Type :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

Definition iff (A:Type) (B:Type) : Type :=
  and (A -> B) (B -> A).

Definition iff_refl (A:Type) : iff A A :=
  conj
  (A -> A)
  (A -> A)
  (fun (a:A) => a)
  (fun (a:A) => a).

Definition iff_trans (A:Type) (B:Type) (C:Type) (HAB:iff A B) (HBC:iff B C) : (iff A C) :=
  match HAB as HAB0 in and _ _ return iff A C with
  | conj _ _ fAB fBA => 
    match HBC as HBC0 in and _ _ return iff A C with
      | conj _ _ fBC fCB =>
          conj (A -> C) (C -> A)
          (fun (a:A) => fBC (fAB a))
          (fun (c:C) => fBA (fCB c))
      end
  end.

Definition iff_sym (A:Type) (B:Type) (H:iff A B) : (iff B A) :=
  match H as H0 in and _ _ return iff B A with
  | conj _ _ Hl Hr =>
      conj (B -> A) (A -> B) Hr Hl
  end.

Definition and_iff_compat_l (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (and A B) (and A C) :=
  match H as H0 in and _ _ return iff (and A B) (and A C) with
  | conj _ _ Hl Hr =>
      conj
        (and A B -> and A C)
        (and A C -> and A B)
        (fun (H0 : and A B) =>
          match H0 as H1 in and _ _ return and A C with
          | conj _ _ H1 H2 => conj A C H1 (Hl H2)
          end)
        (fun (H0 : and A C) =>
          match H0 as H1 in and _ _ return and A B with
          | conj _ _ H1 H2 => conj A B H1 (Hr H2)
          end)
  end.

Definition and_iff_compat_r (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (and B A) (and C A) :=
  match H as H0 in and _ _ return iff (and B A) (and C A) with
  | conj _ _ Hl Hr =>
      conj
        (and B A -> and C A)
        (and C A -> and B A)
        (fun (H0 : and B A) =>
          match H0 as H1 in and _ _ return and C A with
          | conj _ _ H1 H2 => conj C A (Hl H1) H2
          end)
        (fun (H0 : and C A) =>
          match H0 as H1 in and _ _ return and B A with
          | conj _ _ H1 H2 => conj B A (Hr H1) H2
          end)
  end.

Definition or_iff_compat_l (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (or A B) (or A C) :=
  match H as H0 in and _ _ return iff (or A B) (or A C) with
  | conj _ _ Hl Hr =>
      conj
        (or A B -> or A C)
        (or A C -> or A B)
        (fun (H0 : or A B) =>
          match H0 as H1 in or _ _ return or A C with
          | or_introl _ _ H1 => or_introl A C H1
          | or_intror _ _ H1 => or_intror A C (Hl H1)
          end)
        (fun (H0 : or A C) =>
          match H0 as H1 in or _ _ return or A B with
          | or_introl _ _ H1 => or_introl A B H1
          | or_intror _ _ H1 => or_intror A B (Hr H1)
          end)
  end.

Definition or_iff_compat_r (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (or B A) (or C A) :=
  match H as H0 in and _ _ return iff (or B A) (or C A) with
  | conj _ _ Hl Hr =>
      conj
        (or B A -> or C A)
        (or C A -> or B A)
        (fun (H0 : or B A) =>
          match H0 as H1 in or _ _ return or C A with
          | or_introl _ _ H1 => or_introl C A (Hl H1)
          | or_intror _ _ H1 => or_intror C A H1
          end)
        (fun (H0 : or C A) =>
          match H0 as H1 in or _ _ return or B A with
          | or_introl _ _ H1 => or_introl B A (Hr H1)
          | or_intror _ _ H1 => or_intror B A H1
          end)
  end.

Definition imp_iff_compat_l (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (A -> B) (A -> C) :=
  match H as H0 in and _ _ return iff (A -> B) (A -> C) with
  | conj _ _ Hl Hr =>
      conj ((A -> B) -> (A -> C)) ((A -> C) -> (A -> B))
      (fun (H0:A -> B) (H1:A) => Hl (H0 H1))
      (fun (H0:A -> C) (H1:A) => Hr (H0 H1))
  end.

Definition imp_iff_compat_r (A:Type) (B:Type) (C:Type) (H:iff B C) : iff (B -> A) (C -> A) :=
  match H as H0 in and _ _ return iff (B -> A) (C -> A) with
  | conj _ _ Hl Hr =>
      conj ((B -> A) -> (C -> A)) ((C -> A) -> (B -> A))
      (fun (H0:B -> A) (H1:C) => H0 (Hr H1))
      (fun (H0:C -> A) (H1:B) => H0 (Hl H1))
  end.

Definition not_imp_compat (A:Type) (B:Type) (H:iff A B) : iff (not A) (not B) := 
  imp_iff_compat_r False A B H.

Definition neg_false (A:Type) : iff (not A) (iff A False) :=
  conj (not A -> iff A False) (iff A False -> not A)
  (fun (H:not A) =>
    conj (A -> False) (False -> A) H
    (fun (H1 : False) => False_rect (fun (H2:False) => A) H1))
  (fun (H:iff A False) =>
    match H as H0 in and _ _ return not A with
    | conj _ _ H0 H1 => H0
    end).

Definition and_comm (A:Type) (B:Type) : iff (and A B) (and B A) :=
  conj (and A B -> and B A) (and B A -> and A B)
  (fun (H : and A B) => match H as H0 in and _ _ return and B A with
                     | conj _ _ H0 H1 => conj B A H1 H0
                     end)
  (fun (H : and B A) => match H as H0 in and _ _ return and A B with
                     | conj _ _ H0 H1 => conj A B H1 H0
                     end).
                  
Definition and_assoc (A:Type) (B:Type) (C:Type) : iff (and (and A B) C) (and A (and B C)) :=
  conj
  (and (and A B) C -> and A (and B C))
  (and A (and B C) -> and (and A B) C)
  (fun (H : and (and A B) C) =>
    match H as H0 in and _ _ return and A (and B C) with
    | conj _ _ H0 x =>
        match H0 as H1 in and _ _ return C -> and A (and B C) with
        | conj _ _ H1 H2 => fun (H3 : C) => conj A (and B C) H1 (conj B C H2 H3)
        end x
    end)
  (fun (H : and A (and B C)) =>
    match H as H0 in and _ _ return and (and A B) C with
    | conj _ _ H0 H1 => 
        match H1 as H2 in and _ _ return and (and A B) C with
        | conj _ _ H2 H3 => conj (and A B) C (conj A B H0 H2) H3
        end
    end).

Definition or_comm (A : Type) (B : Type) : iff (or A B) (or B A) :=
  conj
  (or A B -> or B A)
  (or B A -> or A B)
  (fun (H : or A B) =>
    match H as H0 in or _ _ return or B A with
    | or_introl _ _ H0 => or_intror B A H0
    | or_intror _ _ H0 => or_introl B A H0
    end)
  (fun (H : or B A) =>
    match H as H0 in or _ _ return or A B with
    | or_introl _ _ H0 => or_intror A B H0
    | or_intror _ _ H0 => or_introl A B H0
    end).

Definition or_assoc (A : Type) (B : Type) (C : Type) : iff (or (or A B) C) (or A (or B C)) :=
  conj
  (or (or A B) C -> or A (or B C))
  (or A (or B C) -> or (or A B) C)
  (fun (H : (or (or A B) C)) =>
    match H as H0 in or _ _ return or A (or B C) with
    | or_introl _ _ HAB =>
        match HAB as HAB0 in or _ _ return or A (or B C) with
        | or_introl _ _ HA => or_introl A (or B C) HA
        | or_intror _ _ HB => or_intror A (or B C) (or_introl B C HB)
        end
    | or_intror _ _ HC => or_intror A (or B C) (or_intror B C HC)
    end)
  (fun (H : or A (or B C)) =>
    match H as H0 in or _ _ return or (or A B) C with
    | or_introl _ _ HA => or_introl (or A B) C (or_introl A B HA)
    | or_intror _ _ HBC =>
        match HBC as HBC0 in or _ _ return or (or A B) C with
        | or_introl _ _ HB => or_introl (or A B) C (or_intror A B HB)
        | or_intror _ _ HC => or_intror (or A B) C HC
        end
    end).

Definition iff_and (A:Type) (B:Type) (H:iff A B) : and (A -> B) (B -> A) :=
  H.

Definition iff_to_and (A:Type) (B:Type) : iff (iff A B) (and (A -> B) (B -> A)) :=
  conj
  (iff A B -> and (A -> B) (B -> A))
  (and (A -> B) (B -> A) -> iff A B)
  (fun (H : iff A B) =>
    match H as H0 in and _ _ return and (A -> B) (B -> A) with
    | conj _ _ Hl Hr =>
        conj (A -> B) (B -> A) (fun (H0 : A) => Hl H0) (fun (H0 : B) => Hr H0)
    end)
  (fun (H : and (A -> B) (B -> A)) =>
    match H as H0 in and _ _ return iff A B with
    | conj _ _ Hl Hr =>
        conj (A -> B) (B -> A) (fun (H0 : A) => Hl H0) (fun (H0 : B) => Hr H0)
    end).

Definition IF_then_else (P:Type) (Q:Type) (R:Type) : Type := or (and P Q) (and (not P) Q).

Inductive ex (A:Type) (P:A -> Type) : Type :=
  | ex_intro : forall (x:A), P x -> ex A P.

Inductive ex2 (A:Type) (P:A -> Type) (Q:A -> Type) : Type :=
  | ex_intro2 : forall (x:A), P x -> Q x -> ex2 A P Q.

Definition all (A:Type) (P:A -> Type) : Type := forall (x:A), P x.

Definition inst (A:Type) (P:A -> Type) (x:A) (H:all A (fun (x:A) => P x)) : P x :=
  H x.

Definition gen (A:Type) (P:A -> Type) (B:Type) (f:forall (y:A), B -> P y) (b:B) : all A P :=
  (fun (x:A) => f x b).

Inductive eq (A:Type) (x:A) : A -> Type :=
  | eq_refl : eq A x x.

Definition absurd (A : Type) (B : Type) (H1 : A) (H2 : not A) : B :=
  let f : False := H2 H1 in
    match f as f0 in False return B with end.

Definition eq_sym (A:Type) (x:A) (y:A) (H:eq A x y) : eq A y x :=
  match H as H0 in eq _ _ y0 return eq A y0 x with
  | eq_refl _ _ => eq_refl A x
  end.

Definition eq_trans (A:Type) (x:A) (y:A) (z:A) (H1:eq A x y) (H2:eq A y z) : eq A x z :=
  match H2 as H in eq _ _ y0 return eq A x y0 with
  | eq_refl _ _ => H1
  end.

Definition f_equal (A:Type) (B:Type) (f:A -> B) (x:A) (y:A) (H:eq A x y) : eq B (f x) (f y) := 
  match H as H0 in eq _ _ y0 return eq B (f x) (f y0) with
  | eq_refl _ _ => eq_refl B (f x)
  end.

Definition noteq (A:Type) (x:A) (y:A) : Type := eq A x y -> False.

Definition not_eq_sym (A:Type) (x:A) (y:A) (H:noteq A x y) : noteq A y x :=
  (fun (H1:eq A y x) =>
    H
    ( match H1 as H2 in eq _ _ x0 return noteq A x0 y -> eq A x0 y with
      | eq_refl _ _ => fun (H2:noteq A y y) => eq_refl A y
      end H)).

Definition eq_rect_r (A:Type) (x:A) (P:forall (a: A), eq A x a -> Type)
  (H:P x (eq_refl A x)) (y:A) (H0:eq A y x) : P y (eq_sym A y x H0) :=
  eq_rect A x (fun (y0 : A) => P y0) H y (eq_sym A y x H0).

Definition f_equal2 (A1:Type) (A2:Type) (B:Type) (f:A1 -> A2 -> B) (x1:A1) (y1:A1)
  (x2:A2) (y2:A2) (H1:eq A1 x1 y1) (H2:eq A2 x2 y2) : eq B (f x1 x2) (f y1 y2) :=
  match H1 as H in eq _ _ y return eq B (f x1 x2) (f y y2) with
  | eq_refl _ _ =>
      match H2 as H in eq _ _ y return eq B (f x1 x2) (f x1 y) with
      | eq_refl _ _ => eq_refl B (f x1 x2)
      end
  end.
  
Definition f_equal3 (A1:Type) (A2:Type) (A3:Type) (B:Type) (f:A1 -> A2 -> A3 -> B)
  (x1:A1) (y1:A1) (x2:A2) (y2:A2) (x3:A3) (y3:A3)
  (H1:eq A1 x1 y1) (H2:eq A2 x2 y2) (H3:eq A3 x3 y3) : eq B (f x1 x2 x3) (f y1 y2 y3) :=
  match H1 as H in eq _ _ y return eq B (f x1 x2 x3) (f y y2 y3) with
  | eq_refl _ _ =>
      match H2 as H in eq _ _ y return eq B (f x1 x2 x3) (f x1 y y3) with
      | eq_refl _ _ =>
          match H3 as H in eq _ _ y return eq B (f x1 x2 x3) (f x1 x2 y) with
          | eq_refl _ _ => eq_refl B (f x1 x2 x3)
          end
      end
  end.

Definition f_equal4 (A1:Type) (A2:Type) (A3:Type) (A4:Type) (B:Type)
  (f:A1 -> A2 -> A3 -> A4 -> B)
  (x1:A1) (y1:A1) (x2:A2) (y2:A2) (x3:A3) (y3:A3) (x4:A4) (y4:A4)
  (H1:eq A1 x1 y1) (H2:eq A2 x2 y2) (H3:eq A3 x3 y3) (H4:eq A4 x4 y4)
    : eq B (f x1 x2 x3 x4) (f y1 y2 y3 y4) :=
  match H1 as H in eq _ _ y return eq B (f x1 x2 x3 x4) (f y y2 y3 y4) with
  | eq_refl _ _ =>
      match H2 as H in eq _ _ y return eq B (f x1 x2 x3 x4) (f x1 y y3 y4) with
      | eq_refl _ _ =>
          match H3 as H in eq _ _ y return eq B (f x1 x2 x3 x4) (f x1 x2 y y4) with
          | eq_refl _ _ =>
              match H4 as H in eq _ _ y return eq B (f x1 x2 x3 x4) (f x1 x2 x3 y) with
              | eq_refl _ _ => eq_refl B (f x1 x2 x3 x4)
              end
          end
      end
  end.

Definition f_equal5 (A1:Type) (A2:Type) (A3:Type) (A4:Type) (A5:Type)
  (B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
  (x1:A1) (y1:A1) (x2:A2) (y2:A2) (x3:A3) (y3:A3) (x4:A4) (y4:A4) (x5:A5) (y5:A5)
  (H1:eq A1 x1 y1) (H2:eq A2 x2 y2) (H3:eq A3 x3 y3) (H4:eq A4 x4 y4) (H5:eq A5 x5 y5)
    : eq B (f x1 x2 x3 x4 x5) (f y1 y2 y3 y4 y5) :=
  match H1 as H in eq _ _ y return eq B (f x1 x2 x3 x4 x5) (f y y2 y3 y4 y5) with
  | eq_refl _ _ =>
      match H2 as H in eq _ _ y return eq B (f x1 x2 x3 x4 x5) (f x1 y y3 y4 y5) with
      | eq_refl _ _ =>
          match H3 as H in eq _ _ y return eq B (f x1 x2 x3 x4 x5) (f x1 x2 y y4 y5) with
          | eq_refl _ _ =>
              match H4 as H in eq _ _ y return eq B (f x1 x2 x3 x4 x5) (f x1 x2 x3 y y5) with
              | eq_refl _ _ =>
                  match H5 as H in eq _ _ y return eq B (f x1 x2 x3 x4 x5) (f x1 x2 x3 x4 y) with
                  | eq_refl _ _ => eq_refl B (f x1 x2 x3 x4 x5)
                  end
              end
          end
      end
  end.

Definition f_equal_compose (A:Type) (B:Type) (C:Type)
  (a:A) (b:A) (f:A -> B) (g:B -> C) (e:eq A a b) :
  eq (eq C (g (f a)) (g (f b))) (f_equal B C g (f a) (f b) (f_equal A B f a b e)) (f_equal A C (fun (a:A) => g (f a)) a b e) :=
  match e as e0 in eq _ _ y
    return
      (eq (eq C (g (f a)) (g (f y)))
        (f_equal B C g (f a) (f y) (f_equal A B f a y e0))
        (f_equal A C (fun (a0 : A) => g (f a0)) a y e0))
  with
  | eq_refl _ _ => eq_refl (eq C (g (f a)) (g (f a))) (eq_refl C (g (f a)))
  end.

Definition eq_trans_refl_l (A:Type) (x:A) (y:A) (e:eq A x y) :
  eq (eq A x y) (eq_trans A x x y (eq_refl A x) e) e :=
  match e as e0 in eq _ _ y0 return eq (eq A x y0) (eq_trans A x x y0 (eq_refl A x) e0) e0 with
  | eq_refl _ _ => eq_refl (eq A x x) (eq_refl A x)
  end.

Definition eq_trans_refl_r (A:Type) (x:A) (y:A) (e:eq A x y) :
  eq (eq A x y) (eq_trans A x y y e (eq_refl A y)) e :=
  match e as e0 in eq _ _ y0 return eq (eq A x y0) (eq_trans A x y0 y0 e0 (eq_refl A y0)) e0 with
  | eq_refl _ _ => eq_refl (eq A x x) (eq_refl A x)
  end.

Definition eq_sym_involutive (A:Type) (x:A) (y:A) (e:eq A x y) :
  eq (eq A x y) (eq_sym A y x (eq_sym A x y e)) e :=
  match e as e0 in eq _ _ y0 return eq (eq A x y0) (eq_sym A y0 x (eq_sym A x y0 e0)) e0 with
  | eq_refl _ _ => eq_refl (eq A x x) (eq_refl A x)
  end.

Definition eq_trans_sym_inv_l (A:Type) (x:A) (y:A) (e:eq A x y) :
  eq (eq A y y) (eq_trans A y x y (eq_sym A x y e) e) (eq_refl A y) :=
  match
    e as e0 in eq _ _ y0
    return
      (eq (eq A y0 y0) (eq_trans A y0 x y0 (eq_sym A x y0 e0) e0)
         (eq_refl A y0))
  with
  | eq_refl _ _ => eq_refl (eq A x x) (eq_refl A x)
  end.

Definition eq_trans_sym_inv_r (A:Type) (x:A) (y:A) (e:eq A x y) :
  eq (eq A x y) e (eq_sym A y x (eq_sym A x y e)) :=
  match
    e as e0 in eq _ _ y0
    return (eq (eq A x y0) e0 (eq_sym A y0 x (eq_sym A x y0 e0)))
  with
  | eq_refl _ _ => eq_refl (eq A x x) (eq_refl A x)
  end.

Definition eq_trans_assoc (A:Type) (x:A) (y:A) (z:A) (t:A)
  (e1:eq A x y) (e2:eq A y z) (e3:eq A z t) :
  eq (eq A x t)
    (eq_trans A x y t e1 (eq_trans A y z t e2 e3))
    (eq_trans A x z t (eq_trans A x y z e1 e2) e3) :=
  match
    e3 as e in eq _ _ y0
    return
      (eq (eq A x y0) (eq_trans A x y y0 e1 (eq_trans A y z y0 e2 e))
         (eq_trans A x z y0 (eq_trans A x y z e1 e2) e))
  with
  | eq_refl _ _ => eq_refl (eq A x z) (eq_trans A x y z e1 e2)
  end.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n:nat) (m:nat) : nat :=
    match n as n0 in nat return nat with
    | O => m
    | S n1 => S (plus n1 m)
    end.

Fixpoint multiply (n:nat) (m:nat) : nat :=
    match n as n0 in nat return nat with
    | O => O
    | S n1 => plus m (multiply n1 m)
    end.

Fixpoint power (n:nat) (m:nat) : nat :=
    match m as m0 in nat return nat with
    | O => S O
    | S m1 => multiply n (power n m1)
    end.

Inductive list (T:Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.

Inductive ilist (T:Type) : nat -> Type :=
| inil : ilist T O
| icons : forall (n:nat), T -> ilist T n -> ilist T (S n).

<<<<<<< HEAD
  

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b as b0 in bool return bool with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 as b0 in bool return bool with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 as b0 in bool return bool with
  | true => true
  | false => b2
  end.

Fixpoint beq_nat (n : nat) (m : nat) : bool :=
  match n as n0 in nat return bool with
  | O => match m as m0 in nat return bool with
         | O => true
         | S m1 => false
         end
  | S n1 => match m as m0 in nat return bool with
            | O => false
            | S m1 => beq_nat n1 m1
            end
  end.

Fixpoint evenb (n:nat) : bool :=
  match n as n0 in nat return bool with
  | O => true
  | S n1 => 
    match n1 as n2 in nat return bool with
    | O => false
    | S n2 => evenb n2
    end
  end.

Definition oddb (n:nat) : bool := negb (evenb n).
=======
>>>>>>> a45ad6d3995539c8e5f1474788f75b3d19e55653
