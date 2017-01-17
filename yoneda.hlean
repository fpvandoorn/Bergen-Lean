--The following special case of the Yoneda lemma:
--If A -> X ~= B -> X for all X, then A ~= B
import types.equiv
import types.pointed
import .typeclass
import .ccat

open pointed eq equiv is_equiv function typeclass cCat

--set_option pp.all true

definition pTypeC.{u} : ccCat.{u u u} :=
  begin
    fapply mk,
    {
      fapply cCat.mk, 
      {
        exact λ A , A
      },
      {
        intro A B f,
        exact f (obj.struct A) = obj.struct B
      },
      {
        intro A,
        exact refl _
      }
    },
    {
      intro A B,
      apply arr.mk,
      exact refl _
    }
  end

namespace pointed

  definition yoneda.{u} {A B : pType.{u}} (e : Π (X : pType.{u}) , (ppmap A X) ≃* (ppmap B X)) : A ≃* B :=
    begin
      fapply pequiv_of_equiv,
      { 
        fapply equiv.mk,
        { 
          apply ccCat.deYonedify pTypeC, 
          intro X,
          apply to_equiv,
          apply pequiv.symm,
          exact (e X)
        },
        { fapply is_equiv.mk, 
          {
            apply Yonedable.deYonedify pTypeY,
            intro X,
            apply to_equiv,
            exact (e X)
          },
          {
          },
          {
          },
          {
          }
        }
      },
      { 
      }
    end

end pointed
