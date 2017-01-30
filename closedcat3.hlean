import .closedcat2

structure closedCat₃ extends CC:closedCat₂ :=
  (coh_compr_assoc : Π {A X Y Z} {f : cCat.arr X Y} {g : cCat.arr Y Z}, 
    eq.pathover (good (cCatwHom.hom A X) (cCatwHom.hom A Z)) 
      (compwd (compr A g) (compr A f)) (eq.eq_of_homotopy (λ h , cCat.assoc)) 
      (compr A (cCat.comp g f)))
