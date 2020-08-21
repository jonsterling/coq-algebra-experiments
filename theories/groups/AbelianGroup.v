From algebra Require Import Foundation.

Declare Scope group_scope.
Delimit Scope group_scope with grp.

Set Primitive Projections.

Module Class.
  Section Laws.
    Context {G : Type} (zero : G) (add : G → G → G) (neg : G → G).
    Record laws : Prop :=
      Laws
        {addC : commutative add;
         addL : left_id zero add;
         addA : associative add;
         negI : ∀ x, add x (neg x) = zero}.
  End Laws.

  Record axioms G :=
    Class
      {zero : G;
       add : G → G → G;
       neg : G → G;
       _laws : laws zero add neg}.
End Class.

Record type := Pack {sort; class : Class.axioms sort}.

Module SortCoercion.
  Coercion sort : type >-> Sortclass.
End SortCoercion.

Import SortCoercion.

Section Operations.
  Context {G : type}.
  Definition zero : G := Class.zero _ (class G).
  Definition add : G → G → G := Class.add _ (class G).
  Definition neg : G → G := Class.neg _ (class G).

  Local Fact laws : Class.laws zero add neg.
  Proof. apply: Class._laws. Defined.

  Definition addC : commutative add := Class.addC _ _ _ laws.
  Definition addL : left_id zero add := Class.addL _ _ _ laws.
  Definition addA : associative add := Class.addA _ _ _ laws.
  Definition negI : ∀ x, add x (neg x) = zero := Class.negI _ _ _ laws.
End Operations.

Definition make_class :
  ∀ (G : Type)
    (zero : ⟨ "zero" ∷ G ⟩)
    (add : ⟨ "add" ∷ G → G → G⟩)
    (neg : ⟨ "neg" ∷ G → G ⟩),
    Class.laws (!zero) (!add) (!neg)
    → Class.axioms G.
Proof.
  move=> ? [zero] [add] [neg] laws.
  econstructor; eauto.
Defined.

Ltac make_class :=
  unshelve apply: make_class.

Module Notation.
  Notation "0" := zero : group_scope.
  Infix "+" := add : group_scope.
End Notation.

Fact addR {G : type} : right_id (@zero G) add.
Proof.
  move=> x; by rewrite addC addL.
Qed.

Hint Rewrite @addL @addA @addR @negI : group.

Module Exports.
  Export SortCoercion.
  Export Notation.
End Exports.
