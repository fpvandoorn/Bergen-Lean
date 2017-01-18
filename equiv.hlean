--Results about equivalences

import types.equiv
open eq equiv is_equiv

definition equiv_inj {A B : Type} (e : A ≃ B) (x y : A)
  (ex_is_ey : e x = e y) : x = y :=
begin
  transitivity (e⁻¹ (e x)),
  { symmetry,
    apply to_left_inv },
  { transitivity (e⁻¹ (e y)),
    { refine congr_arg _ _ e⁻¹ _, 
      exact ex_is_ey },
    apply to_left_inv }
end

