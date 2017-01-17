-- A "concrete infinity-category", a subcategory of the inf-category of types
-- An object consists of a type plus some data
-- The arrows are the 'good' maps

import types.equiv
import .equiv
import .typeclass

open eq equiv is_equiv function typeclass

structure cCat.{u v} extends CC:typeclass.{u v} : Type.{(max u v)+1} :=
  (good : Π {A B : obj CC} , (A → B) → Type.{u})
  (idwd : Π (A : obj CC), good (λ (x : A) , x))
  (invwd : Π {A B : obj CC} (e : A ≃ B) , good e → good e⁻¹)
  (compwd : Π {A B C : obj CC} (g : B → C) (f : A → B), good g → good f → good (g ∘ f))
  (coh_unitr : Π {A B : obj CC} (g : A → B) (p : good g) ,
    compwd g (λ x , x) p (idwd A) = p)

namespace cCat
  variables {CC : cCat}

  structure arr (A B : obj CC) :=
    (to_fun : A → B)
    (wd : good CC to_fun)

  infix ` →* `:30 := pmap

  attribute arr.to_fun [coercion]

  definition arr_inj {A B : obj CC} {f g : A → B} {p : good CC f} {q : good CC g}
    (f_is_g : f = g) (p_is_q : p =[ f_is_g ] q) : arr.mk f p = arr.mk g q := 
    begin
      induction f_is_g,
      apply congr_arg _ _ (arr.mk f),
      apply eq_of_pathover_idp p_is_q
    end

  definition arr_eta {A B : obj CC} (f : arr A B) : f = arr.mk (arr.to_fun f) (arr.wd f) :=
    begin
      induction f,
      reflexivity
    end

  definition arr_inj' {A B : obj CC} {f g : arr A B} (p : arr.to_fun f = arr.to_fun g) (q : arr.wd f =[ p ] arr.wd g) : f = g :=
    begin
      transitivity _,
      apply arr_eta,
      transitivity _,
      apply arr_inj,
      exact q,
      symmetry,
      exact arr_eta g
    end

  definition id (A : obj CC) : arr A A :=
    arr.mk (λ x , x) (idwd CC A)

  definition comp {A B C : obj CC} (g : arr B C) (f : arr A B) : arr A C :=
    begin
      apply arr.mk (g ∘ f),
      apply compwd CC g f (arr.wd g) (arr.wd f)
    end

  infix ` ∘* `:50 := comp

  definition unitr {A B : obj CC} (f : arr A B) : f ∘* id A = f :=
    begin
      fapply arr_inj',
      reflexivity,
      apply pathover_idp_of_eq,
      apply coh_unitr
    end

  structure cequiv (A B : obj CC) extends e:equiv A B, arr A B

  infix ` ≃* `:25 := cequiv

  protected definition cequiv.symm [symm] [constructor] {A B : obj CC} (f : A ≃* B) : B ≃* A :=
    begin
      fconstructor,
      { exact f⁻¹ᵉ },
      { apply is_equiv_inv },
      { apply invwd, exact arr.wd f }
    end
end cCat open cCat

