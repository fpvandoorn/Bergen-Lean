import .functor

open eq cCat functor

structure nateq {C D : cCat} (F G : functor C D) :=
  (comp : Π X , F X ≃* G X)
  (nat  : Π {X Y} {f : X →* Y} , 
    fa G f ∘* comp X = (comp Y ∘* fa F f))

namespace nateq
  protected definition whisker_left
    {C D E : cCat}
    {F G : functor C D} {H : functor D E} :
    nateq F G → nateq (functor.comp H F) (functor.comp H G) :=
  begin
    intro alpha,
    fapply mk,
    { intro X,
      apply ap (fo H), },
    { }
  end
end nateq
