--Closed concrete infinity-category
import .ccatwhom

--set_option max_memory 1750

open eq cCat

structure closedCat extends CC:cCatwHom :=
  (compr : Π X {Y Z : typeclass.obj CC} (f : arr Y Z) , good (cCatwHom.hom X Y) (cCatwHom.hom X Z) (λ g , f ∘* g))

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
