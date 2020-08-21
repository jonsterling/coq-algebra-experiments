From algebra Require Import Foundation.
From algebra Require Category Functor.

Set Universe Polymorphism.
Set Primitive Projections.

Import Category.Exports Functor.Exports.

Module Cat := Category.
Module Fun := Functor.

Section Class.
  Context {𝒞 𝒟 : Cat.type} (F G : [Cat] 𝒞 𝒟).

  Definition is_natural (α : ∀ x : 𝒞, 𝒟 (F # x) (G # x)) : Prop :=
    ∀ x y (f : 𝒞 x y),
      F ## f ≫ α _ = α _ ≫ G ## f.
End Class.

Section Packed.
  Context {𝒞 𝒟 : Cat.type} (F G : [Cat] 𝒞 𝒟).
  Record type := Pack {trans; naturality : is_natural F G trans}.

  Lemma extensionality : ∀ α β, trans α = trans β → α = β.
  Proof.
    move=> [α αN] [β βN] //= Q.
    induction Q.
    replace αN with βN; auto.
  Qed.
End Packed.

Arguments naturality [_] [_] [_] [_] _ [_] [_].

Instance nt_ext {𝒞 𝒟} {F G : [Cat] 𝒞 𝒟} : ExtLaw (type F G) _ :=
  {ext_law := extensionality _ _}.

Module Coercions.
  Coercion trans : type >-> Funclass.
End Coercions.

Import Coercions.

Ltac make := unshelve apply: Pack.


Section Category.
  Context (𝒞 𝒟 : Cat.type).

  Definition category : Cat.type.
  Proof.
    Cat.make.
    - exact ([Cat] 𝒞 𝒟).
    - exact type.
    - Cat.axioms.
      + axiom "idn" => F; make.
        * move=> ?; apply: Cat.idn.
        * abstract (move=> *; by autorewrite with cat).
      + axiom "seq" => F G H α β; make.
        * move=> x.
          exact: (α x ≫ β x).
        * abstract (move=> *; by rewrite -Cat.seqA naturality ?Cat.seqA naturality).
      + abstract (split=> *; ext; ext; move=> *; by autorewrite with cat).
  Defined.
End Category.

Module Notations.
  Notation "[Fun: 𝒞 , 𝒟 ]" := (category 𝒞 𝒟).
End Notations.

Import Notations.

Module Examples.
  Inductive obΔ1 := I0 | I1.

  Inductive homΔ1 (x y : obΔ1) : Prop :=
  | seg of x = I0 ∧ y = I1
  | idn of x = y.

  Example Δ1 : [Cat].
  Cat.make.
  - exact obΔ1.
  - exact homΔ1.
  - Cat.axioms.
    + axiom "idn"; firstorder.
    + axiom "seq" => ? ? ? [[-> ->] | ->]; firstorder.
    + repeat split; auto.
  Defined.

  Canonical Δ1.

  Example ArrowCat (𝒞 : [Cat]) : [Cat] :=
    [Fun: Δ1, 𝒞].

  Example cod {𝒞 : [Cat]} : [Fun: ArrowCat 𝒞, 𝒞].
  Fun.make.
  - axiom "ob" => f.
    exact: (f # I1).
  - axiom "hom" => f g α.
    apply: α.
  - done.
  Defined.

  Example dom {𝒞 : [Cat]} : [Fun: ArrowCat 𝒞, 𝒞].
  Fun.make.
  - axiom "ob" => f.
    exact (f # I0).
  - axiom "hom" => f g α.
    apply: α.
  - done.
  Defined.

  Example Pr (𝒞 : [Cat]) : Cat.type := [Fun: Cat.Op 𝒞, Cat.TYPE].

  Example OpFun : Fun.type [Cat] [Cat].
  Fun.make.
  - axiom "ob" => 𝒞.
    by apply: Cat.Op.
  - axiom "hom" => 𝒞 𝒟 F.
    Fun.make.
    + axiom "ob" => x.
      exact: (F # x).
    + axiom "hom" => x y f.
      exact: (F ## f).
    + abstract (split=> *; cbn; by autorewrite with cat).
  - abstract (split=> *; cbn; ext; by ext).
  Defined.


  Example base_change (𝒞 𝒟 : [Cat]) : Fun.type 𝒞 𝒟 → Fun.type (Pr 𝒟) (Pr 𝒞).
  move=> F.
  Fun.make.
  - axiom "ob" => X.
    exact: ((X : [Cat] _ _) ∘ OpFun ## F).
  - axiom "hom" => X Y α; make.
    + move=> ?; by apply: α.
    + move=> ? ? ?; by apply: (naturality α).
  - abstract (split => *; ext; by ext).
  Defined.

  Example yo {𝒞 : [Cat]} : Fun.type 𝒞 (Pr 𝒞).
  Fun.make.
  - axiom "ob" => x.
    Fun.make.
    + axiom "ob" => y.
      exact: (𝒞 y x).
    + axiom "hom" => *.
      apply: Cat.seq; eauto.
    + abstract (split=> *; ext => *; by autorewrite with cat).
  - axiom "hom" => ? ? f; make; cbn.
    + move=> ? g.
      exact: (g ≫ f).
    + abstract (move=> *; ext=> ?; by autorewrite with cat).
  - abstract (split=> *; ext; ext => *; ext => *; by autorewrite with cat).
  Defined.
End Examples.

Module Exports.
  Export Coercions.
  Export Notations.
End Exports.
