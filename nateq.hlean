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
      apply @pres_equiv D E H,
      exact nateq.comp alpha X },
    { intro X Y f,
      exact calc
        fa H (fa G f) ∘* fa H (comp alpha X) = fa H (fa G f ∘* comp alpha X) : functor.fcomp
        ... = fa H (comp alpha Y ∘* fa F f) : ap (fa H) (nateq.nat alpha)
        ... = (fa H (comp alpha Y) ∘* fa H (fa F f)) : (functor.fcomp H)⁻¹ }
  end
end nateq
