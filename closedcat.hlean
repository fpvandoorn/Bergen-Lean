--Closed concrete infinity-category
import .ccat

open eq equiv is_equiv typeclass cCat

structure closedCat.{u v} extends CC:cCat.{u v} : Type.{(max u v)+1} :=
  (closed : Π {A B : obj CC} , data (arr A B))

namespace closedCat
  open function
  variables {C : closedCat}

  definition hom (A B : obj C) : obj C := obj.mk (arr A B) (closed C)

  definition deYon.{u v w} {C : closedCat.{u v}} {A B : obj C} (f : Π X, @cequiv.{u v} C (hom A X) (hom B X)) : @arr C B A := 
    begin
      apply equiv.to_fun (f A),
      apply id
    end

  definition natural {A B : obj C} (e : Π X, @cequiv C (hom A X) (hom B X)) : Type := Π {X Y} (f : X →* Y) (g : A →* X), f ∘* e X g = e Y (f ∘* g)

  definition equiv_inv_nat {A B : obj C}
    (e : Π X, @cequiv C (hom A X) (hom B X))
    (enat : natural e) : natural (λ X , cequiv.symm (e X)) :=
  begin 
    intro X Y f g,
    refine equiv_inj (e Y) (f ∘* (e X)⁻¹ᵉ g) (cequiv.symm (e Y) (f ∘* g)) _,
    transitivity _,
    { symmetry,
      refine enat f ((e X)⁻¹ᵉ g) },
    { transitivity (f ∘* g),
      { apply congr_arg _ _ (λ x , f ∘* x),
        apply equiv_inv (e X) },
      { symmetry,
        apply equiv_inv (e Y) }}
  end

  definition deYon_inv {A B : obj C}
    (e : Π X , @cequiv C (hom A X) (hom B X))
    (enat : natural e) :
    deYon (λ X , cequiv.symm (e X)) ∘* deYon e = id B :=
  begin 
    unfold [deYon],
    exact calc
      cequiv.symm (e B) (id B) ∘* e A (id A) = e B (cequiv.symm (e B) (id B) ∘* id A) : enat (cequiv.symm (e B) (id B)) (id A)
      ... = e B (cequiv.symm (e B) (id B)) : congr_arg _ _ (e B) (unitr (cequiv.symm (e B) (id B)))
      ... = @id C B : to_right_inv (e B) (id B)
  end

  definition yoneda {A B : obj C} 
    (e : Π (X : obj C) , @cequiv C (hom A X) (hom B X)) 
    (enat : natural e)
    : 
    @cequiv C A B :=
    begin
      fapply cequiv.mk,
      { apply deYon,
        intro X,
        apply cequiv.symm,
        exact (e X) },
      { fapply is_equiv.mk,
        exact deYon e,
        { apply congr_fun,
          transitivity _,
          unfold [deYon], 
          apply congr_arg ((e B)⁻¹ᵉ (id B) ∘* e A (id A)) _ arr.to_fun,
          refine enat (cequiv.symm (e B) (id B)) (id A),
          { transitivity _,
            { apply congr_arg _ _ arr.to_fun,
              apply congr_arg _ _ (e B),
              apply unitr },
            { symmetry,
              refine congr_arg (id B) _ arr.to_fun _,
              apply to_eq_of_inv_eq (e B),
              reflexivity } } },
        { apply congr_fun, 
          unfold [deYon],
          },
        { } },
      { }
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

end closedCat
