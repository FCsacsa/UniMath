(****************************************************************************

 Iso-inserters in bicategories

 Contents
 1. Cones
 2. The universal mapping property
 3. The universal property gives an equivalence of categories
 4. Bicategories with iso-inserters
 5. Inserters are faithful
 6. Inserters are conservative

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Categories.CatIsoInserter.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

Section IsoInserters.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}.

  (**
   1. Cones
   *)
  Definition iso_inserter_cone
    : UU
    := ∑ (i : B)
         (m : i --> b₁),
       invertible_2cell (m · f) (m · g).

  Definition make_iso_inserter_cone
             (i : B)
             (m : i --> b₁)
             (α : invertible_2cell (m · f) (m · g))
    : iso_inserter_cone
    := i ,, m ,, α.

  Coercion iso_inserter_cone_ob
           (cone : iso_inserter_cone)
    : B
    := pr1 cone.

  Definition iso_inserter_cone_pr1
             (cone : iso_inserter_cone)
    : cone --> b₁
    := pr12 cone.

  Definition iso_inserter_cone_cell
             (cone : iso_inserter_cone)
    : invertible_2cell
        (iso_inserter_cone_pr1 cone · f)
        (iso_inserter_cone_pr1 cone · g)
    := pr22 cone.

  Definition iso_inserter_1cell
             (cone₁ cone₂ : iso_inserter_cone)
    : UU
    := ∑ (k : cone₁ --> cone₂)
         (α : invertible_2cell
                (k · iso_inserter_cone_pr1 cone₂)
                (iso_inserter_cone_pr1 cone₁)),
       (k ◃ iso_inserter_cone_cell cone₂)
       • lassociator _ _ _
       • (α ▹ g)
       =
       lassociator _ _ _
       • (α ▹ f)
       • iso_inserter_cone_cell cone₁.

  Definition make_iso_inserter_1cell
             {cone₁ cone₂ : iso_inserter_cone}
             (k : cone₁ --> cone₂)
             (α : invertible_2cell
                    (k · iso_inserter_cone_pr1 cone₂)
                    (iso_inserter_cone_pr1 cone₁))
             (p : (k ◃ iso_inserter_cone_cell cone₂)
                  • lassociator _ _ _
                  • (α ▹ g)
                  =
                  lassociator _ _ _
                  • (α ▹ f)
                  • iso_inserter_cone_cell cone₁)
    : iso_inserter_1cell cone₁ cone₂
    := k ,, α ,, p.

  Coercion iso_inserter_1cell_mor
           {cone₁ cone₂ : iso_inserter_cone}
           (u : iso_inserter_1cell cone₁ cone₂)
    : cone₁ --> cone₂
    := pr1 u.

  Definition iso_inserter_1cell_pr1
             {cone₁ cone₂ : iso_inserter_cone}
             (u : iso_inserter_1cell cone₁ cone₂)
    : invertible_2cell
        (u · iso_inserter_cone_pr1 cone₂)
        (iso_inserter_cone_pr1 cone₁)
    := pr12 u.

  Definition iso_inserter_1cell_cell
             {cone₁ cone₂ : iso_inserter_cone}
             (u : iso_inserter_1cell cone₁ cone₂)
    : (_ ◃ iso_inserter_cone_cell cone₂)
       • lassociator _ _ _
       • (iso_inserter_1cell_pr1 u ▹ g)
       =
       lassociator _ _ _
       • (iso_inserter_1cell_pr1 u ▹ f)
       • iso_inserter_cone_cell cone₁
    := pr22 u.

  Definition path_iso_inserter_1cell
             {cone₁ cone₂ : iso_inserter_cone}
             (φ ψ : iso_inserter_1cell cone₁ cone₂)
             (p₁ : pr1 φ = pr1 ψ)
             (p₂ : pr112 φ = (idtoiso_2_1 _ _ p₁ ▹ _) • pr112 ψ)
    : φ = ψ.
  Proof.
    induction φ as [ φ₁ [ φ₂ φ₃ ]].
    induction ψ as [ ψ₁ [ ψ₂ ψ₃ ]].
    cbn in *.
    induction p₁.
    apply maponpaths.
    use subtypePath.
    {
      intro.
      apply cellset_property.
    }
    cbn.
    use subtypePath.
    {
      intro.
      apply isaprop_is_invertible_2cell.
    }
    cbn in p₂.
    rewrite id2_rwhisker, id2_left in p₂.
    exact p₂.
  Qed.

  (**
   2. The universal mapping property
   *)
  Section UniversalMappingProperty.
    Context (cone : iso_inserter_cone).

    Definition has_iso_inserter_ump_1
      : UU
      := ∏ (other_cone : iso_inserter_cone),
         iso_inserter_1cell other_cone cone.

    Definition has_iso_inserter_ump_2
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · iso_inserter_cone_pr1 cone
                ==>
                u₂ · iso_inserter_cone_pr1 cone)
           (p : rassociator _ _ _
                • (u₁ ◃ iso_inserter_cone_cell cone)
                • lassociator _ _ _
                • (α ▹ g)
                =
                (α ▹ f)
                • rassociator _ _ _
                • (u₂ ◃ iso_inserter_cone_cell cone)
                • lassociator _ _ _),
         ∑ (ζ : u₁ ==> u₂),
         ζ ▹ iso_inserter_cone_pr1 cone = α.

    Definition has_iso_inserter_ump_eq
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · iso_inserter_cone_pr1 cone
                ==>
                u₂ · iso_inserter_cone_pr1 cone)
           (p : rassociator _ _ _
                • (u₁ ◃ iso_inserter_cone_cell cone)
                • lassociator _ _ _
                • (α ▹ g)
                =
                (α ▹ f)
                • rassociator _ _ _
                • (u₂ ◃ iso_inserter_cone_cell cone)
                • lassociator _ _ _)
           (φ₁ φ₂ : u₁ ==> u₂)
           (q₁ : φ₁ ▹ iso_inserter_cone_pr1 cone = α)
           (q₂ : φ₂ ▹ iso_inserter_cone_pr1 cone = α),
         φ₁ = φ₂.

    Definition has_iso_inserter_ump
      : UU
      := has_iso_inserter_ump_1 × has_iso_inserter_ump_2 × has_iso_inserter_ump_eq.
  End UniversalMappingProperty.

  Section Projections.
    Context {cone : iso_inserter_cone}
            (H : has_iso_inserter_ump cone).

    Definition iso_inserter_ump_mor
               {i : B}
               (m : i --> b₁)
               (α : invertible_2cell (m · f) (m · g))
      : i --> cone
      := pr1 H (make_iso_inserter_cone i m α).

    Definition iso_inserter_ump_mor_pr1
               {i : B}
               (m : i --> b₁)
               (α : invertible_2cell (m · f) (m · g))
      : invertible_2cell
          (iso_inserter_ump_mor m α · iso_inserter_cone_pr1 cone)
          m
      := iso_inserter_1cell_pr1 (pr1 H (make_iso_inserter_cone i m α)).

    Definition iso_inserter_ump_mor_cell
               {i : B}
               (m : i --> b₁)
               (α : invertible_2cell (m · f) (m · g))
      : (_ ◃ iso_inserter_cone_cell cone)
        • lassociator _ _ _
        • (iso_inserter_ump_mor_pr1 m α ▹ g)
        =
        lassociator _ _ _
        • (iso_inserter_ump_mor_pr1 m α ▹ f)
        • α
      := iso_inserter_1cell_cell (pr1 H (make_iso_inserter_cone i m α)).

    Definition iso_inserter_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · iso_inserter_cone_pr1 cone
                    ==>
                    u₂ · iso_inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _)
      : u₁ ==> u₂
      := pr1 (pr12 H x u₁ u₂ α p).

    Definition iso_inserter_ump_cell_pr1
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · iso_inserter_cone_pr1 cone
                    ==>
                    u₂ · iso_inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _)
      : iso_inserter_ump_cell α p ▹ iso_inserter_cone_pr1 cone = α
      := pr2 (pr12 H x u₁ u₂ α p).

    Definition iso_inserter_ump_eq
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · iso_inserter_cone_pr1 cone
                    ==>
                    u₂ · iso_inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q₁ : φ₁ ▹ iso_inserter_cone_pr1 cone = α)
               (q₂ : φ₂ ▹ iso_inserter_cone_pr1 cone = α)
      : φ₁ = φ₂
      := pr22 H x u₁ u₂ α p φ₁ φ₂ q₁ q₂.

    Definition iso_inserter_ump_eq_alt
               {x : B}
               {u₁ u₂ : x --> cone}
               (φ₁ φ₂ : u₁ ==> u₂)
               (p : rassociator _ _ _
                    • (u₁ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (φ₁ ▹ iso_inserter_cone_pr1 cone ▹ g)
                    =
                    (φ₁ ▹ iso_inserter_cone_pr1 cone ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ iso_inserter_cone_cell cone)
                    • lassociator _ _ _)
               (q : φ₁ ▹ iso_inserter_cone_pr1 cone
                    =
                    φ₂ ▹ iso_inserter_cone_pr1 cone)
      : φ₁ = φ₂.
    Proof.
      use iso_inserter_ump_eq.
      - exact (φ₁ ▹ iso_inserter_cone_pr1 cone).
      - exact p.
      - apply idpath.
      - exact (!q).
    Qed.
  End Projections.

  Section Invertible2CellIso_inserterUMP.
    Context {cone : iso_inserter_cone}
            (H : has_iso_inserter_ump cone)
            {x : B}
            {u₁ u₂ : x --> cone}
            (α : u₁ · iso_inserter_cone_pr1 cone
                 ==>
                 u₂ · iso_inserter_cone_pr1 cone)
            (p : rassociator _ _ _
                 • (u₁ ◃ iso_inserter_cone_cell cone)
                 • lassociator _ _ _
                 • (α ▹ g)
                 =
                 (α ▹ f)
                 • rassociator _ _ _
                 • (u₂ ◃ iso_inserter_cone_cell cone)
                 • lassociator _ _ _)
            (Hα : is_invertible_2cell α).

    Local Lemma is_invertible_2cell_iso_inserter_ump_cell_inv_path
      : rassociator _ _ _
        • (u₂ ◃ iso_inserter_cone_cell cone)
        • lassociator _ _ _
        • (Hα ^-1 ▹ g)
        =
        (Hα ^-1 ▹ f)
        • rassociator _ _ _
        • (u₁ ◃ iso_inserter_cone_cell cone)
        • lassociator _ _ _.
    Proof.
      use vcomp_move_R_Mp ; [ is_iso | ].
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      exact (!p).
    Qed.

    Let inv : u₂ ==> u₁
      := iso_inserter_ump_cell
           H
           Hα^-1
           is_invertible_2cell_iso_inserter_ump_cell_inv_path.

    Local Lemma is_invertible_2cell_iso_inserter_ump_cell_inv_right
      : iso_inserter_ump_cell H α p • inv = id₂ _.
    Proof.
      use (iso_inserter_ump_eq_alt H).
      - rewrite <- !rwhisker_vcomp.
        rewrite !vassocr.
        unfold inv.
        rewrite !iso_inserter_ump_cell_pr1.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite !vcomp_rinv.
        rewrite !id2_rwhisker.
        rewrite id2_left, id2_right.
        apply idpath.
      - rewrite <- !rwhisker_vcomp.
        unfold inv.
        rewrite !iso_inserter_ump_cell_pr1.
        rewrite id2_rwhisker.
        apply vcomp_rinv.
    Qed.

    Local Lemma is_invertible_2cell_iso_inserter_ump_cell_inv_left
      : inv • iso_inserter_ump_cell H α p = id₂ _.
    Proof.
      use (iso_inserter_ump_eq_alt H).
      - rewrite <- !rwhisker_vcomp.
        rewrite !vassocr.
        unfold inv.
        rewrite !iso_inserter_ump_cell_pr1.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite !vcomp_linv.
        rewrite !id2_rwhisker.
        rewrite id2_left, id2_right.
        apply idpath.
      - rewrite <- !rwhisker_vcomp.
        unfold inv.
        rewrite !iso_inserter_ump_cell_pr1.
        rewrite id2_rwhisker.
        apply vcomp_linv.
    Qed.

    Definition is_invertible_2cell_iso_inserter_ump_cell
      : is_invertible_2cell (iso_inserter_ump_cell H α p).
    Proof.
      use make_is_invertible_2cell.
      - exact inv.
      - exact is_invertible_2cell_iso_inserter_ump_cell_inv_right.
      - exact is_invertible_2cell_iso_inserter_ump_cell_inv_left.
    Defined.
  End Invertible2CellIso_inserterUMP.

  Definition isaprop_has_iso_inserter_ump
             (HB_2_1 : is_univalent_2_1 B)
             (cone : iso_inserter_cone)
    : isaprop (has_iso_inserter_ump cone).
  Proof.
    use invproofirrelevance.
    intros χ₁ χ₂.
    use pathsdirprod.
    - use funextsec.
      intro q.
      use path_iso_inserter_1cell.
      + apply (isotoid_2_1 HB_2_1).
        use make_invertible_2cell.
        * use (iso_inserter_ump_cell χ₁).
          ** exact (iso_inserter_1cell_pr1 (pr1 χ₁ q) • (iso_inserter_1cell_pr1 (pr1 χ₂ q))^-1).
          ** rewrite <- !rwhisker_vcomp.
             rewrite !vassocl.
             etrans.
             {
               apply maponpaths.
               rewrite !vassocr.
               apply maponpaths_2.
               exact (iso_inserter_1cell_cell (pr1 χ₁ q)).
             }
             rewrite !vassocr.
             rewrite rassociator_lassociator.
             rewrite id2_left.
             rewrite !vassocl.
             apply maponpaths.
             use vcomp_move_R_Mp ; [ is_iso | ].
             cbn.
             rewrite !vassocl.
             refine (!_).
             etrans.
             {
               do 2 apply maponpaths.
               rewrite !vassocr.
               exact (iso_inserter_1cell_cell (pr1 χ₂ q)).
             }
             etrans.
             {
               apply maponpaths.
               rewrite !vassocr.
               rewrite rassociator_lassociator.
               rewrite id2_left.
               apply idpath.
             }
             rewrite !vassocr.
             rewrite rwhisker_vcomp.
             rewrite vcomp_linv.
             rewrite id2_rwhisker.
             apply id2_left.
        * use is_invertible_2cell_iso_inserter_ump_cell.
          is_iso.
          apply property_from_invertible_2cell.
      + rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        rewrite iso_inserter_ump_cell_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
    - use pathsdirprod.
      + use funextsec ; intro x.
        use funextsec ; intro u₁.
        use funextsec ; intro u₂.
        use funextsec ; intro φ.
        use funextsec ; intro p.
        use subtypePath.
        {
          intro.
          apply cellset_property.
        }
        use (iso_inserter_ump_eq χ₁).
        * exact φ.
        * exact p.
        * exact (pr2 ((pr12 χ₁) x u₁ u₂ φ p)).
        * exact (pr2 ((pr12 χ₂) x u₁ u₂ φ p)).
      + do 9 (use funextsec ; intro).
        apply cellset_property.
  Qed.

  (**
   3. The universal property gives an equivalence of categories
   *)
  Definition iso_inserter_cone_functor_data
             (cone : iso_inserter_cone)
             (x : B)
    : functor_data
        (hom x cone)
        (cat_iso_inserter (post_comp x f) (post_comp x g)).
  Proof.
    use make_functor_data.
    - refine (λ h, h · iso_inserter_cone_pr1 cone
                   ,,
                   _).
      use inv2cell_to_z_iso.
      use make_invertible_2cell.
      + exact (rassociator _ _ _ • (h ◃ iso_inserter_cone_cell cone) • lassociator _ _ _).
      + is_iso.
        apply property_from_invertible_2cell.
    - refine (λ x y g, g ▹ _ ,, _) ; cbn.
      abstract
        (rewrite !vassocr ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite vcomp_whisker ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite rwhisker_rwhisker ;
         apply idpath).
  Defined.

  Definition iso_inserter_cone_functor_is_functor
             (cone : iso_inserter_cone)
             (x : B)
    : is_functor (iso_inserter_cone_functor_data cone x).
  Proof.
    split.
    - intro h.
      use eq_cat_iso_inserter ; cbn.
      rewrite id2_rwhisker.
      apply idpath.
    - intros z₁ z₂ z₃ h₁ h₂.
      use eq_cat_iso_inserter ; cbn.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Definition iso_inserter_cone_functor
             (cone : iso_inserter_cone)
             (x : B)
    : hom x cone ⟶ cat_iso_inserter (post_comp x f) (post_comp x g).
  Proof.
    use make_functor.
    - exact (iso_inserter_cone_functor_data cone x).
    - exact (iso_inserter_cone_functor_is_functor cone x).
  Defined.

  Definition is_universal_iso_inserter_cone
             (cone : iso_inserter_cone)
    : UU
    := ∏ (x : B),
       adj_equivalence_of_cats (iso_inserter_cone_functor cone x).

  Section MakeUniversalIso_inserterCone.
    Context (HB_2_1 : is_univalent_2_1 B)
            (cone : iso_inserter_cone)
            (H : has_iso_inserter_ump cone)
            (x : B).

    Definition make_is_universal_iso_inserter_cone_full
      : full (iso_inserter_cone_functor cone x).
    Proof.
      intros u₁ u₂ α.
      pose (p := pr2 α).
      cbn in p.
      rewrite !vassocr in p.
      apply hinhpr.
      simple refine (_ ,, _).
      - use (iso_inserter_ump_cell H).
        + exact (pr1 α).
        + exact p.
      - use eq_cat_iso_inserter ; cbn in *.
        apply iso_inserter_ump_cell_pr1.
    Defined.

    Definition make_is_universal_iso_inserter_cone_faithful
      : faithful (iso_inserter_cone_functor cone x).
    Proof.
      intros u₁ u₂ α.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (iso_inserter_ump_eq_alt H).
      - pose (pr2 α) as p.
        cbn in p.
        rewrite !vassocr in p.
        refine (_ @ p @ _).
        + do 2 apply maponpaths.
          exact (maponpaths pr1 (pr2 φ₁)).
        + do 3 apply maponpaths_2.
          apply maponpaths.
          exact (!(maponpaths pr1 (pr2 φ₁))).
      - exact (maponpaths pr1 (pr2 φ₁) @ !(maponpaths pr1 (pr2 φ₂))).
    Qed.

    Definition make_is_universal_iso_inserter_cone_essentially_surjective
      : essentially_surjective (iso_inserter_cone_functor cone x).
    Proof.
      intros h.
      use hinhpr.
      simple refine (_ ,, _).
      - exact (iso_inserter_ump_mor H (pr1 h) (pr2 h)).
      - use z_iso_cat_iso_inserter.
        + simple refine (_ ,, _) ; cbn.
          * apply iso_inserter_ump_mor_pr1.
          * abstract
              (cbn ;
               rewrite !vassocl ;
               use vcomp_move_R_pM ; [ is_iso | ] ;
               cbn ;
               rewrite !vassocr ;
               apply iso_inserter_ump_mor_cell).
        + use is_inv2cell_to_is_z_iso.
          apply property_from_invertible_2cell.
    Defined.
  End MakeUniversalIso_inserterCone.

  Definition make_is_universal_iso_inserter_cone
             (HB_2_1 : is_univalent_2_1 B)
             (cone : iso_inserter_cone)
             (H : has_iso_inserter_ump cone)
    : is_universal_iso_inserter_cone cone.
  Proof.
    intro x.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      exact HB_2_1.
    - use full_and_faithful_implies_fully_faithful.
      split.
      + apply make_is_universal_iso_inserter_cone_full.
        apply H.
      + apply make_is_universal_iso_inserter_cone_faithful.
        apply H.
    - apply make_is_universal_iso_inserter_cone_essentially_surjective.
      apply H.
  Defined.

  Definition isaprop_is_universal_iso_inserter_cone
             (HB_2_1 : is_univalent_2_1 B)
             (cone : iso_inserter_cone)
    : isaprop (is_universal_iso_inserter_cone cone).
  Proof.
    use impred ; intro x.
    use isofhlevelweqf.
    - exact (@left_adjoint_equivalence
               bicat_of_univ_cats
               (univ_hom HB_2_1 x cone)
               (@univalent_cat_iso_inserter
                  (univ_hom HB_2_1 _ _)
                  (univ_hom HB_2_1 _ _)
                  (post_comp x f)
                  (post_comp x g))
               (iso_inserter_cone_functor cone x)).
    - exact (@adj_equiv_is_equiv_cat
               (univ_hom HB_2_1 x cone)
               (@univalent_cat_iso_inserter
                  (univ_hom HB_2_1 _ _)
                  (univ_hom HB_2_1 _ _)
                  (post_comp x f)
                  (post_comp x g))
               (iso_inserter_cone_functor cone x)).
    - apply isaprop_left_adjoint_equivalence.
      exact univalent_cat_is_univalent_2_1.
  Defined.

  Section UniversalConeHasUMP.
    Context {cone : iso_inserter_cone}
            (H : is_universal_iso_inserter_cone cone).

    Section UMP1.
      Context (q : iso_inserter_cone).

      Let alg : cat_iso_inserter (post_comp q f) (post_comp q g)
        := iso_inserter_cone_pr1 q ,, iso_inserter_cone_cell q.

      Definition universal_iso_inserter_cone_has_ump_1_mor
        : q --> cone
        := right_adjoint (H q) alg.

      Definition universal_iso_inserter_cone_has_ump_1_pr1
        : invertible_2cell
            (universal_iso_inserter_cone_has_ump_1_mor · iso_inserter_cone_pr1 cone)
            (iso_inserter_cone_pr1 q).
      Proof.
        use z_iso_to_inv2cell.
        exact (from_z_iso_cat_iso_inserter
                 (nat_z_iso_pointwise_z_iso
                    (counit_nat_z_iso_from_adj_equivalence_of_cats (H q))
                    alg)).
      Defined.

      Definition universal_iso_inserter_cone_has_ump_1_cell
        : (_ ◃ iso_inserter_cone_cell cone)
          • lassociator _ _ _
          • (universal_iso_inserter_cone_has_ump_1_pr1 ▹ g)
          =
          lassociator _ _ _
          • (universal_iso_inserter_cone_has_ump_1_pr1 ▹ f)
          • iso_inserter_cone_cell q.
      Proof.
        cbn.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(pr2 (counit_from_left_adjoint (pr1 (H q)) alg))).
        }
        cbn.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      Qed.
    End UMP1.

    Definition universal_iso_inserter_cone_has_ump_1
      : has_iso_inserter_ump_1 cone.
    Proof.
      intro q.
      use make_iso_inserter_1cell.
      - exact (universal_iso_inserter_cone_has_ump_1_mor q).
      - exact (universal_iso_inserter_cone_has_ump_1_pr1 q).
      - exact (universal_iso_inserter_cone_has_ump_1_cell q).
    Defined.

    Section UMP2.
      Context {x : B}
              {u₁ u₂ : x --> cone}
              (α : u₁ · iso_inserter_cone_pr1 cone
                   ==>
                   u₂ · iso_inserter_cone_pr1 cone)
              (p : rassociator _ _ _
                   • (u₁ ◃ iso_inserter_cone_cell cone)
                   • lassociator _ _ _
                   • (α ▹ g)
                   =
                   (α ▹ f)
                   • rassociator _ _ _
                   • (u₂ ◃ iso_inserter_cone_cell cone)
                   • lassociator _ _ _).

      Definition universal_iso_inserter_cone_has_ump_2_cell
        : u₁ ==> u₂.
      Proof.
        apply (invmap (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))).
        simple refine (_ ,, _).
        - exact α.
        - abstract
            (cbn ;
             rewrite !vassocr ;
             exact p).
      Defined.

      Definition universal_iso_inserter_cone_has_ump_2_pr1
        : universal_iso_inserter_cone_has_ump_2_cell ▹ iso_inserter_cone_pr1 cone
          =
          α.
      Proof.
        exact (maponpaths
                 pr1
                 (homotweqinvweq
                    (make_weq _ (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))
                    _)).
      Qed.
    End UMP2.

    Definition universal_iso_inserter_cone_has_ump_2
      : has_iso_inserter_ump_2 cone.
    Proof.
      intros x u₁ u₂ α p.
      simple refine (_ ,, _).
      - exact (universal_iso_inserter_cone_has_ump_2_cell α p).
      - exact (universal_iso_inserter_cone_has_ump_2_pr1 α p).
    Defined.

    Definition universal_iso_inserter_cone_has_ump_eq
      : has_iso_inserter_ump_eq cone.
    Proof.
      intros x u₁ u₂ α p φ₁ φ₂ q₁ q₂.
      use (invmaponpathsweq
             (make_weq
                _
                (fully_faithful_from_equivalence _ _ _ (H x) u₁ u₂))) ; cbn.
      use subtypePath.
      {
        intro.
        apply cellset_property.
      }
      cbn.
      exact (q₁ @ !q₂).
    Qed.

    Definition universal_iso_inserter_cone_has_ump
      : has_iso_inserter_ump cone.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact universal_iso_inserter_cone_has_ump_1.
      - exact universal_iso_inserter_cone_has_ump_2.
      - exact universal_iso_inserter_cone_has_ump_eq.
    Defined.
  End UniversalConeHasUMP.

  Definition iso_inserter_ump_weq_universal
             (HB_2_1 : is_univalent_2_1 B)
             (cone : iso_inserter_cone)
    : has_iso_inserter_ump cone ≃ is_universal_iso_inserter_cone cone.
  Proof.
    use weqimplimpl.
    - exact (make_is_universal_iso_inserter_cone HB_2_1 cone).
    - exact universal_iso_inserter_cone_has_ump.
    - exact (isaprop_has_iso_inserter_ump HB_2_1 cone).
    - exact (isaprop_is_universal_iso_inserter_cone HB_2_1 cone).
  Defined.
End IsoInserters.

Arguments iso_inserter_cone {_ _ _} _ _.

(**
 4. Bicategories with iso_inserters
 *)
Definition has_iso_inserters
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B)
       (f g : b₁ --> b₂),
     ∑ (i : B)
       (m : i --> b₁)
       (α : invertible_2cell (m · f) (m · g)),
     has_iso_inserter_ump (make_iso_inserter_cone i m α).

(**
 5. Iso_inserters are faithful
 *)
Definition iso_inserter_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : invertible_2cell (m · f) (m · g))
           (H : has_iso_inserter_ump (make_iso_inserter_cone i m α))
  : faithful_1cell m.
Proof.
  intros x g₁ g₂ β₁ β₂ p.
  use (iso_inserter_ump_eq_alt H) ; cbn.
  - abstract
      (rewrite rwhisker_rwhisker_alt ;
       rewrite !vassocl ;
       apply maponpaths ;
       rewrite rwhisker_rwhisker ;
       rewrite !vassocr ;
       apply maponpaths_2 ;
       refine (!_) ;
       apply vcomp_whisker).
  - exact p.
Defined.

(**
 6. Iso_inserters are conservative
 *)
Section Iso_inserterConservative.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}
          {i : B}
          (m : i --> b₁)
          (α : invertible_2cell (m · f) (m · g))
          (H : has_iso_inserter_ump (make_iso_inserter_cone i m α))
          {x : B}
          {g₁ g₂ : x --> i}
          (β : g₁ ==> g₂)
          (Hβ : is_invertible_2cell (β ▹ m)).

  Definition iso_inserter_conservative_inv
    : g₂ ==> g₁.
  Proof.
    use (iso_inserter_ump_cell H).
    - exact Hβ^-1.
    - abstract
        (cbn ;
         use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
         rewrite !vassocl ;
         rewrite rwhisker_rwhisker ;
         use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition iso_inserter_conservative_rinv
    : β • iso_inserter_conservative_inv = id₂ _.
  Proof.
    use (iso_inserter_ump_eq_alt H) ; cbn.
    - rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      unfold iso_inserter_conservative_inv.
      rewrite (iso_inserter_ump_cell_pr1 H).
      rewrite id2_rwhisker.
      apply vcomp_rinv.
  Qed.

  Definition iso_inserter_conservative_linv
    : iso_inserter_conservative_inv • β = id₂ _.
  Proof.
    use (iso_inserter_ump_eq_alt H) ; cbn.
    - rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      unfold iso_inserter_conservative_inv.
      rewrite (iso_inserter_ump_cell_pr1 H).
      rewrite id2_rwhisker.
      apply vcomp_linv.
  Qed.
End Iso_inserterConservative.

Definition iso_inserter_conservative
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : invertible_2cell (m · f) (m · g))
           (H : has_iso_inserter_ump (make_iso_inserter_cone i m α))
  : conservative_1cell m.
Proof.
  intros x g₁ g₂ β Hβ.
  use make_is_invertible_2cell.
  - exact (iso_inserter_conservative_inv m α H β Hβ).
  - exact (iso_inserter_conservative_rinv m α H β Hβ).
  - exact (iso_inserter_conservative_linv m α H β Hβ).
Defined.

Definition iso_inserter_discrete
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : invertible_2cell (m · f) (m · g))
           (H : has_iso_inserter_ump (make_iso_inserter_cone i m α))
  : discrete_1cell m.
Proof.
  split.
  - exact (iso_inserter_faithful m α H).
  - exact (iso_inserter_conservative m α H).
Defined.
