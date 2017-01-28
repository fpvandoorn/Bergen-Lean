import .ccat

open eq equiv is_equiv function typeclass cCat

structure functor (C D : cCat) :=
  (fo : obj C → obj D)
  (fa : Π {X Y} , X →* Y → fo X →* fo Y)
  (fid : Π X, fa (cCat.id X) = cCat.id (fo X))
  (fcomp : Π {X Y Z} {f : X →* Y} {g : Y →* Z} , fa (g ∘* f) = (fa g ∘* fa f))

attribute functor.fo [coercion]

/--open functor

open closedCat

structure cCat' extends CC:cCat :=

namespace cCat'

structure closedCat'.{u v} extends CC:closedCat.{u v} , CC':cCat'.{u v} : Type.{(max u v)+1} :=

open closedCat'

definition homf {C : closedCat'} (A : obj C) : functor C C :=
  begin
    fapply functor.mk,
    exact λ B , @hom C A B,
    { intro X Y f,
      fapply arr.mk,
      exact λ g , f ∘* g,
      apply compr },
    { intro X,
      fapply arr_cong',
      exact eq_of_homotopy (@unitl C A X),
      exact coh_compr_id C},
    { intro X Y Z f g,
      symmetry,
      fapply arr_cong',
      { esimp,
        apply eq_of_homotopy,
        intro h,
        apply assoc },
      { }}
  end
--/
