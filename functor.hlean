import .ccat

open eq equiv is_equiv function cCat cCat.cequiv

structure functor (C D : cCat) :=
  (fo : obj C → obj D)
  (fa : Π {X Y} , X →* Y → fo X →* fo Y)
  (fid : Π X, fa (cCat.id X) = cCat.id (fo X))
  (fcomp : Π {X Y Z} {f : X →* Y} {g : Y →* Z} , fa (g ∘* f) = (fa g ∘* fa f))

attribute functor.fo [coercion]

namespace functor
  protected definition comp {C D E : cCat} : functor D E → functor C D → functor C E :=
  begin
    intro G F,
    fapply mk,
    { exact functor.fo G ∘ functor.fo F },
    { intro X Y,
      exact functor.fa G ∘ functor.fa F },
    { intro X,
      exact calc
        fa G (fa F (id X)) = fa G (id (fo F X)) : ap (fa G) (functor.fid F X)
        ... = id (fo G (fo F X)) : functor.fid G (fo F X) },
    { intro X Y Z f g,
      exact calc
        fa G (fa F (g ∘* f)) = fa G (fa F g ∘* fa F f) : ap (fa G) (functor.fcomp F)
        ... = (fa G (fa F g) ∘* fa G (fa F f)) : functor.fcomp G}
  end

  definition pres_equiv {C D : cCat} {F : functor C D} {A B : obj C} : A ≃* B → fo F A ≃* fo F B :=
  begin
    intro alpha,
    fapply cequiv.mk',
    { exact fa F alpha },
    { exact fa F (cequiv.to_arr alpha⁻¹) },
    { exact calc
      fa F (to_arr alpha⁻¹) ∘* fa F (to_arr alpha) = fa F (to_arr alpha⁻¹ ∘* to_arr alpha) : (functor.fcomp F)⁻¹
      ... = fa F (id A) : ap (fa F) (cequiv.to_left_inv alpha)
      ... = id (fo F A) : functor.fid F A},
    { exact calc
      fa F (to_arr alpha) ∘* fa F (to_arr alpha⁻¹) = fa F (to_arr alpha ∘* to_arr alpha⁻¹) : (functor.fcomp F)⁻¹
      ... = fa F (id B) : ap (fa F) (cequiv.to_right_inv alpha)
      ... = id (fo F B) : functor.fid F B} --/
  end
--Note: to_arr (pres_equiv e) is definitionally equal to fa F (to_arr e)

end functor

/--open closedCat

print closedCat
print prefix closedCat
-- structure cCat' extends CC:cCat

-- namespace cCat'

-- structure closedCat'.{u v} extends CC:closedCat.{u v} , CC':cCat'.{u v} : Type.{(max u v)+1}

-- open closedCat'

open cCatwHom
definition homf {C : closedCat} (A : obj C) : functor C C :=
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
  end --/
