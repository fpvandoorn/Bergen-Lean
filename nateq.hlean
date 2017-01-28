import .functor

open cCat functor

structure nateq {C D : cCat} (F G : functor C D) :=
  (comp : Π X , F X ≃* G X)
  (nat  : Π {X Y} {f : X →* Y} , 
    fa G f ∘* comp X = (comp Y ∘* fa F f))

