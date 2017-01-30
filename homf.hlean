import .closedcat

open eq typeclass cCat cCatwHom closedCat

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
    { apply coh_compr_id }},
  { intro X Y Z f g,
    symmetry,
    fapply arr_cong,
    { apply eq_of_homotopy,
      intro h,
      apply assoc },
    { }}
end

