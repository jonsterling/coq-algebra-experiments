From algebra Require Import Foundation.
From algebra.groups Require AbelianGroup.
From algebra Require Category.

Module AbGroup := AbelianGroup.
Import AbGroup.Exports.

Declare Scope ring_scope.
Delimit Scope ring_scope with ring.

Set Primitive Projections.

Module Class.
  Record axioms (A : Type) :=
    Class
      {zero : A;
       add : A → A → A;
       neg : A → A;
       one : A;
       mul : A → A → A;
       add_laws : AbGroup.Class.laws zero add neg;
       mulA : associative mul;
       mulC : commutative mul;
       mulL : left_id one mul;
       dist : left_distributive mul add}.
End Class.

Record type := Pack {sort; class : Class.axioms sort}.

Definition make_class :
  ∀ (A : Type)
    (zero : ⟨ "zero" ∷ A ⟩)
    (add : ⟨ "add" ∷ A → A → A⟩)
    (neg : ⟨ "neg" ∷ A → A ⟩)
    (one : ⟨ "one" ∷ A ⟩)
    (mul : ⟨ "mul" ∷ A → A → A⟩),
    (AbGroup.Class.laws (!zero) (!add) (!neg)
     ∧ associative (!mul)
     ∧ commutative (!mul)
     ∧ left_id (!one) (!mul)
     ∧ left_distributive (!mul) (!add))
    → Class.axioms A.
Proof.
  move=> A [zero] [add] [neg] [one] [mul] [add_laws [? [? [? ?]]]].
  unshelve econstructor;
  [exact: zero | exact: add | exact: neg | exact: one | exact: mul | ..]; eauto.
Defined.

Module SortCoercion.
  Coercion sort : type >-> Sortclass.
End SortCoercion.

Import SortCoercion.

Section Operations.
  Context {A : type}.
  Definition zero : A := Class.zero _ (class A).
  Definition one : A := Class.one _ (class A).
  Definition neg := Class.neg _ (class A).
  Definition add : A → A → A := Class.add _ (class A).
  Definition mul : A → A → A := Class.mul _ (class A).
End Operations.


Module Notation.
  Notation "0" := zero : ring_scope.
  Notation "1" := one : ring_scope.
  Infix "+" := add (left associativity, at level 50) : ring_scope.
  Infix "⋅" := mul (at level 50) : ring_scope.
End Notation.

Import Notation.

Local Open Scope ring_scope.

Section Laws.
  Context {A : type}.

  Local Definition add_laws := Class.add_laws _ (class A).
  Definition addC : commutative add := AbGroup.Class.addC _ _ _ add_laws.
  Definition addL : left_id zero add := AbGroup.Class.addL _ _ _ add_laws.
  Definition addA : associative add := AbGroup.Class.addA _ _ _ add_laws.
  Definition mulA : associative mul := Class.mulA _ (class A).
  Definition mulC : commutative mul := Class.mulC _ (class A).
  Definition mulL : left_id 1 mul := Class.mulL _ (class A).
  Definition dist : left_distributive mul add := Class.dist _ (class A).
  Definition negI : ∀ x : A, x + neg x = 0 := AbGroup.Class.negI _ _ _ add_laws.
End Laws.

Hint Rewrite @addL @addA @mulL @negI @dist @mulA : ring.

Section Theory.
  Context {A : type}.

  Fact neg0 : neg 0 = (0 : A).
  Proof. by rewrite -[neg 0] addL negI. Qed.

  Fact add_injective {a b} : ∀ (c : A), a + c = b + c → a = b.
  Proof.
    move=> c Q.
    rewrite
    -[a] addL -[b] addL
    -[0] (negI c)
    [c + neg c] addC.
    do ?rewrite -[neg c + c + _] addA.
    do ?rewrite [c + _] addC.
    by congruence.
  Qed.

  Fact mul0 : forall x : A, x ⋅ 0 = 0.
  Proof.
    move=> x.
    suff: (x ⋅ 0) + (x ⋅ 0) = (x ⋅ 0).
    - move=> Q.
      suff: (x ⋅ 0) + (neg (x ⋅ 0)) = ((x ⋅ 0) + (x ⋅ 0)) + (neg (x ⋅ 0)).
      + rewrite -addA negI => {2}->.
        by rewrite addC addL.
      + by rewrite Q.
    - by rewrite -mulC -dist addL.
  Qed.


  Fact neg_mul_neg_1 : ∀ x : A, neg x = neg 1 ⋅ x.
  Proof.
    move=> x.
    apply: (add_injective x).
    by rewrite
      [neg x + x] addC
      negI
      -{2}[x] mulL
      - dist
      [neg 1 + 1]
      addC negI mulC mul0.
  Qed.

  Fact neg_dist : ∀ x y : A, neg (x + y) = neg x + neg y.
  Proof.
    move=> x y.
    rewrite neg_mul_neg_1 mulC dist.
    do ? rewrite [_ ⋅ neg 1] mulC.
    by do ? rewrite <- neg_mul_neg_1.
  Qed.


  Fact neg_inv : ∀ x : A, neg (neg x) = x.
  Proof.
    move=> x.
    apply: (add_injective (neg x)).
    by rewrite [neg (neg _) + _] addC negI negI.
  Qed.

End Theory.

Hint Rewrite @neg0 @mul0 @neg_dist @neg_inv : ring.


Definition additive_group : type → AbGroup.type.
  move=> A.
  unshelve econstructor.
  - exact: A.
  - unshelve apply: AbGroup.make_class.
    + axiom "zero".
      apply: zero.
    + axiom "add".
      apply: add.
    + axiom "neg".
      apply: neg.
    + repeat split => *; move=> *; simpl; try by autorewrite with ring.
      apply: addC.
Defined.

Module Exports.
  Export SortCoercion.
  Export Notation.
End Exports.
