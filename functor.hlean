import .ccat

open eq equiv is_equiv function cCat

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
    fapply cequiv.mk,
    { exact fa F alpha },
    { fapply is_equiv.mk,
      { exact fa F (cequiv.symm alpha) },
      { apply homotopy_of_eq,
        exact calc
          fa F alpha ∘ fa F (cequiv.symm alpha) = fa F (alpha ∘* cequiv.symm alpha) : ap arr.to_fun (inverse (@functor.fcomp C D F B A B (cequiv.symm alpha) alpha))
          ... = fa F (id B) : ap arr.to_fun (ap (fa F) _)
          ... = λ x, x : _},
      { }},
    { }
  end
end functor

open functor

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
