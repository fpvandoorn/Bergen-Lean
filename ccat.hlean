-- A "concrete infinity-category", a subcategory of the inf-category of types
-- An object consists of a type plus some data
-- The arrows are the 'good' maps

import types.equiv

open eq equiv is_equiv function

structure cCat.{u v w} : Type.{(max u v w)+1} :=
  (data : Type.{u} → Type.{v})
  (_good : Π (A B : Type) , data A → data B → (A → B) → Type.{w})
  (_idwd : Π (A : Type) (Ad : data A), _good A A Ad Ad (λ (x : A) , x))
  (_invwd : Π {A B : Type} {Ad : data A} {Bd : data B} (e : A ≃ B) , _good A B Ad Bd e → _good B A Bd Ad e⁻¹)
  (_compwd : Π {A B C : Type} {Ad : data A} {Bd : data B} {Cd : data C} {g : B → C} {f : A → B}, 
    _good B C Bd Cd g → _good A B Ad Bd f → _good A C Ad Cd (g ∘ f))
  (_coh_unitl : Π {A B : Type} {Ad : data A} {Bd : data B} (f : A → B) (p : _good A B Ad Bd f) ,
    _compwd (_idwd B Bd) p = p)
  (_coh_unitr : Π {A B : Type} {Ad : data A} {Bd : data B} (g : A → B) (p : _good A B Ad Bd g) ,
    _compwd p (_idwd A Ad) = p)
  (_coh_assoc : Π {X Y Z W : Type} {Xd : data X} {Yd : data Y} {Zd : data Z} {Wd : data W} {f : X → Y} {g : Y → Z} {h : Z → W}
    (p : _good X Y Xd Yd f) (q : _good Y Z Yd Zd g) (r : _good Z W Zd Wd h),
    _compwd r (_compwd q p) = _compwd (_compwd r q) p)
  (_coh_invl : Π {A B : Type} {Ad : data A} {Bd : data B} (e : A ≃ B) (eg : _good A B Ad Bd e),
    _compwd (_invwd e eg) eg =[ eq_of_homotopy (to_left_inv e) ] _idwd A Ad)
  (_coh_invr : Π {A B : Type} {Ad : data A} {Bd : data B} (e : A ≃ B) (eg : _good A B Ad Bd e),
    _compwd eg (_invwd e eg) =[ eq_of_homotopy (to_right_inv e) ] _idwd B Bd)

namespace cCat
  structure obj.{u v w} (CC : cCat.{u v w}) : Type.{max (u+1) v} :=
    (U : Type)
    (struct : data CC U)

  attribute obj.U [coercion]

  definition good.{u v w} {CC : cCat.{u v w}} (A B : obj CC) (f : A → B) : Type.{w} := 
    begin
      exact _good CC A B (obj.struct A) (obj.struct B) f
    end

  variables {CC : cCat} 

  definition idwd (A : obj CC) : good A A (λ (x : A) , x) :=
    begin
      exact _idwd CC A (obj.struct A)
    end

  definition invwd {A B : obj CC} (e : A ≃ B) (eg : good A B e) : good B A e⁻¹ :=     begin
      exact _invwd CC e eg
    end

  definition compwd {A B C : obj CC} {g : B → C} {f : A → B} (gg : good B C g) (fg : good A B f) : good A C (g ∘ f) := 
    begin
      exact _compwd CC gg fg
    end

  definition coh_unitl {A B : obj CC} (f : A → B) (fg : good A B f) : compwd (idwd B) fg = fg :=
    begin
      exact _coh_unitl CC f fg
    end

  definition coh_unitr {A B : obj CC} (g : A → B) (gg : good A B g) : compwd gg (idwd A) = gg :=
    begin
      exact _coh_unitr CC g gg
    end

  definition coh_assoc {X Y Z W : obj CC} {f : X → Y} {g : Y → Z} {h : Z → W}
    (fg : good X Y f) (gg : good Y Z g) (hg : good Z W h) :
    compwd hg (compwd gg fg) = compwd (compwd hg gg) fg := 
    begin
      exact _coh_assoc CC fg gg hg
    end

  definition coh_invl {A B : obj CC} (e : A ≃ B) (eg : good A B e) : compwd (invwd e eg) eg =[ eq_of_homotopy (to_left_inv e) ] idwd A :=
  begin
    apply _coh_invl
  end

  definition coh_invr {A B : obj CC} (e : A ≃ B) (eg : good A B e) :
    compwd eg (invwd e eg) =[ eq_of_homotopy (to_right_inv e) ] idwd B :=
  begin
    apply _coh_invr
  end

  structure arr (A B : obj CC) :=
    (to_fun : A → B)
    (wd : good A B to_fun)

  infix ` →* `:30 := arr

  attribute arr.to_fun [coercion]

  definition arr_cong {A B : obj CC} {f g : A → B} {p : good A B f} {q : good A B g}
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

  definition arr_cong' {A B : obj CC} {f g : A →* B} (p : arr.to_fun f = arr.to_fun g) (q : arr.wd f =[ p ] arr.wd g) : f = g :=
    begin
      transitivity _,
      apply arr_eta,
      transitivity _,
      apply arr_cong,
      exact q,
      symmetry,
      exact arr_eta g
    end

  definition id (A : obj CC) : A →* A := arr.mk (λ x , x) (idwd A)

  definition comp {A B C : obj CC} (g : B →* C) (f : A →* B) : A →* C :=
    begin
      apply arr.mk (g ∘ f),
      apply compwd (arr.wd g) (arr.wd f)
    end

  infix ` ∘* `:50 := comp

  definition unitl {A B : obj CC} (f : A →* B) : cCat.id B ∘* f = f :=
  begin
    fapply arr_cong',
    reflexivity,
    apply pathover_idp_of_eq,
    apply coh_unitl
  end

  definition unitr {A B : obj CC} (f : A →* B) : f ∘* id A = f :=
    begin
      fapply arr_cong',
      reflexivity,
      apply pathover_idp_of_eq,
      apply coh_unitr
    end

  definition assoc {A B C D : obj CC} {f : @arr CC A B} {g : @arr CC B C} {h : @arr CC C D} : h ∘* (g ∘* f) = ((h ∘* g) ∘* f) :=
  begin
    fapply arr_cong',
    reflexivity,
    { apply pathover_idp_of_eq,
      apply coh_assoc }
  end

  structure cequiv (A B : obj CC) extends equiv A B, arr A B

  infix ` ≃* `:25 := cequiv

  namespace cequiv
    variables {A B : obj CC}

    protected definition cong {f g : A → B}
      (is_equiv_f : is_equiv f) (is_equiv_g : is_equiv g)
      (good_f : good A B f) (good_g : good A B g)
      (p : f = g) : good_f =[ p ] good_g →
      cequiv.mk f is_equiv_f good_f = cequiv.mk g is_equiv_g good_g :=
    begin
      induction p,
      intros good_hom,
      refine congr_arg2 is_equiv_f is_equiv_g _ _ (cequiv.mk f) _ _,
      refine @eq_of_pathover_idp (A → B) is_equiv f is_equiv_f is_equiv_g _,
      apply !is_trunc.is_prop.elimo,
      exact @eq_of_pathover_idp (A → B) (@good CC A B) f good_f good_g good_hom
    end

    protected definition eta (f : A ≃* B) : cequiv.mk f (cequiv.to_is_equiv f) (cequiv.wd f) = f :=
    begin
      induction f,
      reflexivity
    end

    protected definition symm [symm] [constructor] (f : A ≃* B) : B ≃* A :=
      begin
        fconstructor,
        { exact f⁻¹ᵉ },
        { apply is_equiv_inv },
        { apply invwd, exact arr.wd f }
      end

    postfix ⁻¹ := cequiv.symm

    protected definition to_left_inv (f : A ≃* B) : cequiv.symm f ∘* f = id A :=
    begin
      fapply arr_cong,
      { apply eq_of_homotopy,
        apply to_left_inv },
      { apply coh_invl }
    end

    protected definition to_right_inv (f : A ≃* B) : f ∘* cequiv.symm f = id B :=
    begin
      fapply arr_cong,
      { apply eq_of_homotopy,
        intro x,
        apply to_right_inv f },
      { apply coh_invr }
    end

    protected definition mk' (f : A →* B) (g : B →* A) : g ∘* f = id A → f ∘* g = id B → A ≃* B :=
    begin
      intro gf_is_id fg_is_id,
      fapply mk,
      { exact f },
      { fapply adjointify,
        { exact g },
        { apply homotopy_of_eq,
          exact congr_arg _ _ arr.to_fun fg_is_id },
        { apply homotopy_of_eq,
          exact congr_arg _ _ arr.to_fun gf_is_id }},
      { apply arr.wd }
    end

  end cequiv

end cCat open cCat
