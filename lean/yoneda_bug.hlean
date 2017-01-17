--The following special case of the Yoneda lemma:
--If A -> X ~= B -> X for all X, then A ~= B
import types.equiv
import types.pointed

open pointed eq equiv is_equiv

set_option pp.all true

structure typeclass :=
  (data : Type → Type)

namespace typeclass
  structure obj.{u v} (C : typeclass.{u v}) : Type.{max (u+1) v} :=
    (U : Type.{u})
    (struct : data C U)

  attribute obj.U [coercion]

end typeclass open typeclass

-- A "concrete infinity-category", a subcategory of the inf-category of types
-- An object consists of a type plus some data
-- The arrows are the 'good' maps
structure cCat.{u v w} extends CC:typeclass.{u v} : Type.{(max u v w)+1} :=
  (good : Π (A B : obj CC) , (A → B) → Type.{w})
  (idwd : Π (A : obj CC), good A A (λ x , x))

namespace cCat
  variables {C : cCat}

  structure arr (A B : obj C) :=
    (to_fun : A → B)
    (wd : good C A B to_fun)

  infix ` →* `:30 := pmap

  attribute to_fun [coercion]

  definition id (A : obj C) : arr A A :=
    arr.mk (λ x , x) (idwd C A)

  structure cequiv.{u v w} {C : cCat.{u v w}} (A B : obj C) extends e:equiv.{u u} A B, arr A B : Type.{(max u v w)+1} :=
    (wd_inv : good C B A e⁻¹ᵉ)

  infix ` ≃* `:25 := cequiv

  definition inv_inv {A B : Type} (e : A ≃ B) : e⁻¹⁻¹ = e :=
    begin
      apply eq_of_homotopy,
      intro a,
      exact equiv.to_inv_eq_of_eq _ (symm (to_left_inv e a))
    end
  
  protected definition cequiv.symm [symm] [constructor] {A B : obj C} (f : A ≃* B) : B ≃* A :=
    begin
      apply cequiv.mk,
      {
        exact cequiv.wd_inv f
      },
      {
        esimp,
        apply transport (good C A B),
        rotate 1,
        {
          exact cequiv.wd f
        },
        {       
          symmetry,
          apply inv_inv
        }
      }
    end
end cCat open cCat

--Closed concrete infinity-category
structure ccCat.{u v} extends CC:cCat.{u v u} : Type.{(max u v)+1} :=
  (closed : Π {A B : obj CC} , data (arr A B))

namespace ccCat
  variables {C : ccCat}

  definition hom (A B : obj C) : obj C := obj.mk (arr A B) (closed C)

  definition deYonedify.{u v w} {C : ccCat.{u v}} {A B : obj C} (f : Π X, cequiv.{u v u} (hom A X) (hom B X)) : B → A := 
    begin
      refine @arr.to_fun C _ _ _,
      apply equiv.to_fun (f A),
      apply id
    end

  definition yoneda {A B : obj C} (e : Π X , hom A X ≃* hom B X) : A ≃* B :=
    begin
      fapply cequiv.mk,
      {
        apply deYonedify,
        intro X,
        apply cequiv.symm,
        exact (e X)
      },
      {
      },
      {
      }
    end

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
