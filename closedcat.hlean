--Closed concrete infinity-category
import .ccatwhom

--set_option max_memory 1750

open eq cCat

structure closedCat extends CC:cCatwHom :=
  (compr : Π X {Y Z : typeclass.obj CC} (f : arr Y Z) , good (cCatwHom.hom X Y) (cCatwHom.hom X Z) (λ g , f ∘* g))
