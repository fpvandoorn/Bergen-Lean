--Results about equivalences

open eq equiv is_equiv

definition inv_inv {A B : Type} (e : A ≃ B) : e⁻¹⁻¹ = e :=
begin
  apply eq_of_homotopy,
  intro a,
  exact equiv.to_inv_eq_of_eq _ (symm (to_left_inv e a))
end
  
definition inv_equiv {A B : Type} (e : A ≃ B) (x : A) : e⁻¹ (e x) = x :=
begin
  apply inv_eq_of_eq,
  reflexivity
end

definition equiv_inv {A B : Type} (e : A ≃ B) (x : B) : e (e⁻¹ x) = x :=
begin
  apply @eq_of_eq_inv A B e,
  reflexivity
end

definition equiv_inj {A B : Type} (e : A ≃ B) (x y : A)
  (ex_is_ey : e x = e y) : x = y :=
begin
  transitivity (e⁻¹ (e x)),
  { symmetry,
    apply inv_equiv },
  { transitivity (e⁻¹ (e y)),
    { refine congr_arg _ _ e⁻¹ _, 
      exact ex_is_ey },
    apply inv_equiv }
end

