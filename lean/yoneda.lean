--The following special case of the Yoneda lemma:
--If A -> X ~= B -> X for all X, then A ~= B

import 

definition yoneda {A B : Type} : (Π X → equiv (A → X) (B → X))
