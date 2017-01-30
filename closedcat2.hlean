import .closedcat

set_option max_memory 1500

structure closedCat₂ extends CC : closedCat :=
  (coh_compr_id : Π {A X}, eq.pathover (good (cCatwHom.hom A X) (cCatwHom.hom A X)) (compr A (cCat.id X)) (eq.eq_of_homotopy (λ g , cCat.unitl g)) (idwd (cCatwHom.hom A X)))
--  (coh_compr_assoc : Π {A X Y Z} {f : arr X Y} {g : Y →* Z}, compwd (compr A g) (compr A f) =[ eq_of_homotopy (λ h , assoc) ] compr A (g ∘* f))
