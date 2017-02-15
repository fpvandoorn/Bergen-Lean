/-- The main theorem

Let C be a closed concrete category.  Suppose that, for all B, the functor hom(B, -) has a left adjoint, which we write as - x B.
Then A x (B x C) is isomorphic to (A x B) x C

Proof: For all D,

A x (B x C) -> D ~= A -> B x C -> D
  ~= A -> B -> C -> D
  ~= A x B -> C -> D
  ~= (A x B) x C -> D

Apply Yoneda --/

import .ccatwhom
import .closedcat
import .adjoint

namespace assoc
  open cCat closedCat cCatwHom cCat.cequiv

  variables (CC : closedCat) (Prod : Π (B : obj CC), left_adjoint (homf B))

  definition prod (A B : obj CC) : obj CC := left_adjoint.lo (Prod B) A

  definition assoc {A B C : obj CC} : prod CC Prod A (prod CC Prod B C) ≃* prod CC Prod (prod CC Prod A B) C :=
  begin
    apply @cCatwHom.nat_equiv_hom.yoneda CC,
    fapply nat_equiv_hom.mk,
    { intro D,
      exact calc
      hom (prod CC Prod A (prod CC Prod B C)) D ≃* hom A (hom (prod CC Prod B C) D) : _
      ... ≃* hom A (hom B (hom C D)) : _
      ... ≃* hom (prod CC Prod A B) (hom C D) : _
      ... ≃* hom (prod CC Prod (prod CC Prod A B) C) D : _},
    { }
  end
end assoc
