From algebra Require Import Foundation.
From algebra Require Category.

Set Universe Polymorphism.
Set Primitive Projections.

Import Category.Exports.

Module Cat := Category.

Module Class.
  Record axioms {𝒞 𝒟 : Cat.type} (ob : 𝒞 → 𝒟) (hom : ∀ {x y}, 𝒞 x y → 𝒟 (ob x) (ob y)) : Prop :=
    {idn : ∀ x, hom (Cat.idn x) = Cat.idn (ob x);
     seq : ∀ x y z (f : 𝒞 x y) (g : 𝒞 y z), hom (f ≫ g) = hom f ≫ hom g}.
End Class.

Module Raw.
  Record raw (𝒞 𝒟 : Cat.type) :=
    {ob : 𝒞 → 𝒟;
     hom : ∀ x y, 𝒞 x y → 𝒟 (ob x) (ob y)}.
  Arguments ob [_] [_] _.
  Arguments hom [_] [_] _ [_] [_] _.
End Raw.


Record type (𝒞 𝒟 : Cat.type) :=
  Pack
    {raw : Raw.raw 𝒞 𝒟;
     class : Class.axioms (Raw.ob raw) (Raw.hom raw)}.

Arguments raw [_] [_] _.
Arguments class [_] [_] _.

Section Operations.
  Context {𝒞 𝒟 : Cat.type} (F : type 𝒞 𝒟).
  Definition ob : 𝒞 → 𝒟 := Raw.ob (raw F).
  Definition hom : ∀ {x y} (f : 𝒞 x y), _ := Raw.hom (raw F).
End Operations.

Section Laws.
  Context {𝒞 𝒟 : Cat.type} (F : type 𝒞 𝒟).

  Fact idn : ∀ x, hom F (Cat.idn x) = Cat.idn (ob F x).
  Proof. by move=> *; rewrite /hom (Class.idn _ _ (class F)). Qed.

  Fact seq : ∀ x y z (f : 𝒞 x y) (g : 𝒞 y z), hom F (f ≫ g) = hom F f ≫ hom F g.
  Proof. by move=> *; rewrite /hom (Class.seq _ _ (class F)). Qed.
End Laws.

Hint Rewrite @idn @seq : cat.

Section Extensionality.
  Context (𝒞 𝒟 : Cat.type).

  Local Definition to_pair : type 𝒞 𝒟 → {ob : 𝒞 → 𝒟 & ∀ x y, 𝒞 x y → 𝒟 (ob x) (ob y)}.
  Proof.
    move=> [[ob hom] _].
    econstructor; auto.
  Defined.

  Lemma extensionality : ∀ F G, to_pair F = to_pair G → F = G.
  Proof.
    move=> [[obF homF] clF] [[obG homG] clG] Q.
    proj_eq Q obF obG.
    proj_eq Q homF homG.
    replace clF with clG; auto.
  Qed.
End Extensionality.

Instance functor_ext {𝒞 𝒟 : Cat.type} : ExtLaw (type 𝒞 𝒟) _ :=
  {ext_law := extensionality _ _}.


Definition make :
  ∀ (𝒞 𝒟 : Cat.type)
    (ob : ⟨ "ob" ∷ 𝒞 → 𝒟 ⟩)
    (hom : ⟨ "hom" ∷ ∀ x y, 𝒞 x y → 𝒟 (!ob x) (!ob y) ⟩)
    (axioms : Class.axioms (!ob) (!hom)),
    type 𝒞 𝒟.
Proof.
  move=> 𝒞 𝒟 [ob] [hom] ?.
  unshelve econstructor.
  - unshelve econstructor; auto.
  - eauto.
Defined.

Ltac make := unshelve apply: make.

Module Notation.
  Infix "#" := ob (at level 10).
  Infix "##" := hom (at level 10).
End Notation.

Import Notation.

Definition category : Cat.type.
  Cat.make.
  - exact Cat.type.
  - exact type.
  - Cat.axioms.
    + axiom "idn".
      move=> 𝒞; make.
      * axiom "ob"; move=> x; exact: x.
      * axiom "hom"; move=> x y f; exact: f.
      * by split.
    + axiom "seq" => 𝒞 𝒟 ℰ F G; make.
      * axiom "ob" => x.
        exact: (G # (F # x)).
      * axiom "hom" => ? ? f.
        exact (G ## (F ## f)).
      * abstract (split=> *; auto; simpl; try by autorewrite with cat).
    + abstract (split => *; ext; ext; done).
Defined.

Module Exports.
  Export Notation.
  Notation "[Cat]" := category.
End Exports.
