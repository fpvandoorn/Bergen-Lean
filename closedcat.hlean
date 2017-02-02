--Closed concrete infinity-category
import .ccat
import .ccatwhom
import .functor
open function eq equiv is_equiv cCat cCatwHom

structure closedCat.{u v} extends CC:cCatwHom.{u v} : Type.{(max u v)+1} :=
  (_compr : Π X {Y Z : Type} (Xd : data X) {Yd : data Y} {Zd : data Z}
    (f : Y → Z) (fg : _good Y Z Yd Zd f), _good (arr (obj.mk X Xd) (obj.mk Y Yd)) (arr (obj.mk X Xd) (obj.mk Z Zd)) (_closed Xd Yd) (_closed Xd Zd) 
    (λ g , (arr.mk f fg) ∘* g))
  (_coh_compr_id : Π {A X : Type} {Ad : data A} {Xd : data X},
    pathover (_good (arr (obj.mk A Ad) (obj.mk X Xd)) (arr (obj.mk A Ad) (obj.mk X Xd)) (_closed Ad Xd) (_closed Ad Xd)) (_compr A Ad (λ x , x) (_idwd X Xd)) 
      (eq_of_homotopy unitl)
      (_idwd _ (_closed Ad Xd)))
  (_coh_compr_assoc : Π {A X Y Z : Type} {Ad : data A} {Xd : data X} {Yd : data Y} {Zd : data Z}
    (f : X → Y) (fg : _good X Y Xd Yd f) (g : Y → Z) (gg : _good Y Z Yd Zd g),
      _compwd (_compr A Ad g gg) (_compr A Ad f fg) =[ eq_of_homotopy (λ h , assoc) ] _compr A Ad (g ∘ f) (_compwd gg fg))

namespace closedCat
  variables {CC : closedCat}

  definition compr X {Y Z : obj CC} (f : Y →* Z) : good (@hom CC X Y) (hom X Z) (λ g , f ∘* g) :=
    begin
      induction X,
      induction Y,
      induction Z,
      unfold good,
      apply _compr
    end

  definition coh_compr_id {A X : obj CC} : 
    compr A (id X) =[ eq_of_homotopy unitl ] idwd (hom A X) :=
  begin
    induction A,
    induction X,
    apply _coh_compr_id
  end

  definition coh_compr_assoc {A X Y Z : obj CC} (f : X →* Y) (g : Y →* Z) :
    compwd (compr A g) (compr A f) =[ eq_of_homotopy (λ h , assoc) ] compr A (g ∘* f) :=
  begin
    induction A,
    induction X,
    induction Y,
    induction Z,
    induction f,
    induction g,
    apply _coh_compr_assoc
  end

  definition homfo {A X Y : obj CC} : @arr CC X Y → @arr CC (@hom CC A X) (@hom CC A Y) :=
  begin
    intro f,
    fapply arr.mk,
    exact λ g , f ∘* g,
    apply compr
  end

  definition homf {CC : closedCat} (A : obj CC) : functor CC CC :=
  begin
    fapply functor.mk,
    { exact (@hom CC A) },
    { intro X Y,
      apply @homfo CC },
    { intro X,
      fapply arr_cong,
      { apply eq_of_homotopy,
        intro f,
        apply unitl },
      { apply coh_compr_id }},
    { intro X Y Z f g,
      symmetry,
      fapply arr_cong,
      { apply eq_of_homotopy,
        intro h,
        apply assoc },
      { unfold homfo,
        apply coh_compr_assoc }}
  end
end closedCat

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
