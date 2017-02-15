import .functor
import .nateq
import .closedcat

open cCat functor cCatwHom

structure left_adjoint {C D : cCat} (F : functor C D) :=
  (lo : obj D → obj C)
  (eta : Π (Y : obj D) , Y →* fo F (lo Y))
  (lift : Π (Y : obj D) (X : obj C), (Y →* fo F X) → (lo Y →* X))
  (eta_lift : Π (Y : obj D) (X : obj C) (f : Y →* fo F X),
    fa F (lift Y X f) ∘* eta Y = f)
  (lift_unique : Π (Y : obj D) (X : obj C) (f : Y →* fo F X) (g : lo Y →* X),
    fa F g ∘* eta Y = f → g = lift Y X f)

structure strong_left_adjoint {C : closedCat} (F : functor C C) extends G : left_adjoint F :=
  (strong : Π (X Y : obj C), good (@hom C X (@fo C C F Y)) (hom (lo X) Y) (lift X Y))

namespace strong_left_adjoint

  definition Lift {C : closedCat} {F : strong_functor C} {G : strong_left_adjoint F} (X Y : obj C) : (@hom C Y (fo F X)) →* hom (lo G Y) X :=
  begin
    fapply arr.mk,
    { apply lift },
    { apply strong }
  end

  definition Lower {C : closedCat} {F : strong_functor C} {G : strong_left_adjoint F} (X Y : obj C) : (@hom C (lo G Y) X) →* (hom Y (fo F X)) :=
  begin
    fapply arr.mk,
    { intro g,
      exact fa F g ∘* eta G Y},
    { refine compwd _ (strong_functor.strong F (lo G Y) X),
      apply closedCat.compl }
  end

  definition adjunction {C : closedCat} (F : strong_functor C) (G : strong_left_adjoint F) (X : obj C) (Y : obj C) : @hom C (@left_adjoint.lo C C F G X) Y ≃* hom X (fo F Y) :=
  begin
    fapply cequiv.mk',
    { apply Lower },
    { apply Lift },
    { fapply arr_cong,
      { },
      { }},
    { }
  end

end left_adjoint
