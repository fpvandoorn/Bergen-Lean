--Concrete category with hom-object

import .ccat

open eq equiv is_equiv cCat

structure cCatwHom.{u v} extends CC:cCat.{u v u} : Type.{(max u v)+1} :=
  (_closed : Π {A B : Type} (Ad : data A) (Bd : data B), data (arr (@obj.mk.{u v u} CC A Ad) (obj.mk B Bd)))

namespace cCatwHom
  open function
  variables {CC : cCatwHom}

  definition closed {A B : obj CC} : data CC (arr A B) :=
    begin
      induction A,
      induction B,
      apply _closed
    end

--The internal hom
  definition hom (A B : obj CC) : obj CC := obj.mk (arr A B) (@closed CC A B)

--Equivalences between A → X and B → X for all X
  definition equiv_hom (A B : obj CC) : Type := Π X, @cequiv CC (hom A X) (hom B X)

  namespace equiv_hom

    definition deYon {A B : obj CC} (e : equiv_hom A B) : @arr CC B A :=
      begin
        apply equiv.to_fun (e A),
        apply id
      end

    protected definition symm [symm] {A B : obj CC} (e : equiv_hom A B) : equiv_hom B A :=
      begin
        intro X,
        exact cequiv.symm (e X)
      end

--Natural isomorphisms between the functors A → - and B → -
    definition natural {A B : obj CC} (e : equiv_hom A B) : Type := Π {X Y} (f : X →* Y) (g : A →* X), f ∘* e X g = e Y (f ∘* g)

    definition nat_inv {A B : obj CC} {e : equiv_hom A B} (enat : natural e) : natural (equiv_hom.symm e) :=
    begin
      intro X Y f g,
      apply eq_of_fn_eq_fn (e Y),
      transitivity _,
      { symmetry,
        refine enat f ((e X)⁻¹ᵉ g) },
      { transitivity (f ∘* g),
        { apply congr_arg _ _ (λ x , f ∘* x),
          refine to_right_inv (e X) g },
        { symmetry,
          apply to_right_inv (e Y) (f ∘* g) }}
    end

  end equiv_hom open equiv_hom

  structure nat_equiv_hom (A B : obj CC) :=
    (comp : equiv_hom A B)
    (nat : natural comp)

  attribute nat_equiv_hom.comp [coercion]

  namespace nat_equiv_hom

    protected definition symm [symm] {A B : obj CC} (e : nat_equiv_hom A B) : nat_equiv_hom B A :=
      begin
        fapply nat_equiv_hom.mk,
        exact equiv_hom.symm e,
        apply equiv_hom.nat_inv,
        intro X Y,
        exact nat_equiv_hom.nat e
      end

  definition deYon_inv_deYon {A B : obj CC} (e : nat_equiv_hom A B) :
    deYon (nat_equiv_hom.symm e) ∘* deYon e = id B :=
  begin
    transitivity _,
    apply nat_equiv_hom.nat e,
    { transitivity _,
      { apply congr_arg _ _ (nat_equiv_hom.comp e B),
        apply unitr },
      { apply to_right_inv (nat_equiv_hom.comp e B) (id B) }}
  end

  definition deYon_inv_deYon' {A B : obj CC} (e : nat_equiv_hom A B) (b : B) :
    deYon (nat_equiv_hom.symm e) (deYon e b) = b :=
  begin
    refine congr_fun _ b,
    apply congr_arg (deYon (nat_equiv_hom.symm e) ∘* deYon e) _ arr.to_fun,
    apply deYon_inv_deYon
  end

  definition deYon_deYon_inv {A B : obj CC} (e : nat_equiv_hom A B) :
    deYon e ∘* deYon (nat_equiv_hom.symm e) = id A :=
  begin
    transitivity _,
    { apply @nat_inv CC A B (nat_equiv_hom.comp e) (@nat_equiv_hom.nat CC A B e) },
    { transitivity _,
      { apply congr_arg _ _ (nat_equiv_hom.comp (nat_equiv_hom.symm e) A),
        apply unitr },
      { apply to_right_inv }}
  end

  definition deYon_deYon_inv' {A B : obj CC} (e : nat_equiv_hom A B) (a : A) :
    deYon e (deYon (nat_equiv_hom.symm e) a) = a :=
  begin
    refine congr_fun _ a,
    apply congr_arg (deYon e ∘* deYon (nat_equiv_hom.symm e)) _ arr.to_fun,
    apply deYon_deYon_inv
  end

  definition yoneda {A B : obj CC} (e : nat_equiv_hom A B) : @cequiv CC A B :=
    begin
      fapply cequiv.mk,
      exact (deYon (nat_equiv_hom.symm e)),
      { fapply adjointify,
        exact deYon e,
        apply deYon_inv_deYon',
        apply deYon_deYon_inv' },
      apply arr.wd
    end

end nat_equiv_hom

end cCatwHom
