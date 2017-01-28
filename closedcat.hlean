--Closed concrete infinity-category
import .ccat
import .ccatwhom
import .functor

open eq equiv is_equiv typeclass cCat

structure closedCat extends CC:cCatwHom :=
  (compr : Π {X Y Z : obj CC} (f : @cCat.arr CC Y Z) , @cCatwHom.good CC (@cCatwHom.hom CC X Y) (cCatwHom.hom X Z) (λ g , f ∘* g))
  (coh_compr_id : Π {A X}, compr (@cCat.id CC X) =[ eq_of_homotopy (λ g , unitl g) ] @cCatwHom.idwd CC (cCatwHom.hom A X))

open closedCat

definition homfo {C : closedCat} {A X Y : obj C} : @arr C X Y → @arr C (@hom C A X) (@hom C A Y) :=
begin
  intro f,
  fapply arr.mk,
  exact λ g , f ∘* g,
  apply compr
end

definition homf {C : closedCat} (A : obj C) : functor C C :=
begin
  fapply functor.mk,
  { exact (@hom C A) },
  { intro X Y,
    apply @homfo C },
  { intro X,
    fapply arr_cong,
    { apply eq_of_homotopy,
      intro f,
      apply unitl },
    { }},
  { }
end

/-- definition pType₁ [constructor] : typeclass := typeclass.mk (λ X : Type, X)

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

definition pType₃.{u} : cCatwHom.{u u} :=
  ⦃cCatwHom, pType₂, closed := begin
  intros,
  fapply arr.mk,
  { exact (λ x, obj.struct B) },
  { esimp }
end⦄

  set_option pp.universes true
  print pType₁ --/


