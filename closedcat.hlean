--Closed concrete infinity-category
import .ccat

open eq equiv is_equiv typeclass cCat

structure closedCat.{u v} extends CC:cCat.{u v} : Type.{(max u v)+1} :=
  (closed : Π {A B : obj CC} , data (arr A B))

namespace closedCat
  open function
  variables {C : closedCat}

--The internal hom
  definition hom (A B : obj C) : obj C := obj.mk (arr A B) (closed C)

--Equivalences between A → X and B → X for all X
  definition equiv_hom (A B : obj C) : Type := Π X, @cequiv C (hom A X) (hom B X)

  namespace equiv_hom

    definition deYon {A B : obj C} (e : equiv_hom A B) : @arr C B A :=
      begin
        apply equiv.to_fun (e A),
        apply id
      end

    protected definition symm [symm] {A B : obj C} (e : equiv_hom A B) : equiv_hom B A :=
      begin
        intro X,
        exact cequiv.symm (e X)
      end

--Natural isomorphisms between the functors A → - and B → -
    definition natural {A B : obj C} (e : equiv_hom A B) : Type := Π {X Y} (f : X →* Y) (g : A →* X), f ∘* e X g = e Y (f ∘* g)

    definition nat_inv {A B : obj C} {e : equiv_hom A B} (enat : natural e) : natural (equiv_hom.symm e) :=
    begin
      intro X Y f g,
      apply eq_of_fn_eq_fn (e Y),
      transitivity _,
      { symmetry,
        refine enat f ((e X)⁻¹ᵉ g) },
      { transitivity (f ∘* g),
        { apply congr_arg _ _ (λ x , f ∘* x),
          refine to_right_inv (e X) g },
        { symmetry,
          apply to_right_inv (e Y) (f ∘* g) }}
    end

  end equiv_hom open equiv_hom

  structure natiso (A B : obj C) :=
    (comp : equiv_hom A B)
    (nat : natural comp)

  attribute natiso.comp [coercion]

  namespace natiso

    protected definition symm [symm] {A B : obj C} (e : natiso A B) : natiso B A :=
      begin
        fapply natiso.mk,
        exact equiv_hom.symm e,
        apply equiv_hom.nat_inv,
        intro X Y,
        exact natiso.nat e
      end

  definition deYon_inv_deYon {A B : obj C} (e : natiso A B) :
    deYon (natiso.symm e) ∘* deYon e = id B :=
  begin
    unfold [deYon],
    transitivity _,
    apply natiso.nat e,
    { transitivity _,
      { apply congr_arg _ _ (natiso.comp e B),
        apply unitr },
      { apply to_right_inv (natiso.comp e B) (id B) }}
  end

  definition deYon_inv_deYon' {A B : obj C} (e : natiso A B) (b : B) :
    deYon (natiso.symm e) (deYon e b) = b :=
  begin
    refine congr_fun _ b,
    apply congr_arg (deYon (natiso.symm e) ∘* deYon e) _ arr.to_fun,
    apply deYon_inv_deYon
  end

  definition deYon_deYon_inv {A B : obj C} (e : natiso A B) :
    deYon e ∘* deYon (natiso.symm e) = id A :=
  begin
    unfold [deYon],
    transitivity _,
    { apply @nat_inv C A B (natiso.comp e) (@natiso.nat C A B e) },
    { transitivity _,
      { apply congr_arg _ _ (natiso.comp (natiso.symm e) A),
        apply unitr },
      { apply to_right_inv }}
  end

  definition deYon_deYon_inv' {A B : obj C} (e : natiso A B) (a : A) :
    deYon e (deYon (natiso.symm e) a) = a :=
  begin
    refine congr_fun _ a,
    apply congr_arg (deYon e ∘* deYon (natiso.symm e)) _ arr.to_fun,
    apply deYon_deYon_inv
  end

  definition yoneda {A B : obj C} (e : natiso A B) : @cequiv C A B :=
    begin
      fapply cequiv.mk,
      exact (deYon (natiso.symm e)),
      { fapply adjointify,
        exact deYon e,
        apply deYon_inv_deYon',
        apply deYon_deYon_inv' },
      apply arr.wd
    end


  definition pType₁ [constructor] : typeclass := typeclass.mk (λ X : Type, X)

  definition pType₂.{u} [constructor] : cCat.{u u} :=
  begin
    fapply cCat.mk (typeclass.data pType₁),
    { intros _ _ f, exact (f (obj.struct A) = obj.struct B) },
    { intro _, exact rfl },
    { intros _ _ _ e₀, exact ap (to_fun e)⁻¹ e₀⁻¹ ⬝ !to_left_inv },
    { intros _ _ _ _ _ g₀ f₀, exact ap g f₀ ⬝ g₀},
    { intros, esimp, exact !idp_con}
  end

open pointed

  definition pType₃.{u} : closedCat.{u u} :=
  ⦃closedCat, pType₂, closed := begin
    intros,
    fapply arr.mk,
    { exact (λ x, obj.struct B) },
    { esimp }
    end⦄

  set_option pp.universes true
  print pType₁

end natiso

end closedCat
