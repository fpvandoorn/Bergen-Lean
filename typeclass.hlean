--A typeclass B is a function B : U → U
--It should be thought of as the type of types Σ X : U. B X
--An object of B is a pair (X, x) with X : U and x : B X

structure typeclass :=
  (data : Type → Type)

namespace typeclass
  structure obj.{u v} (C : typeclass.{u v}) : Type.{max (u+1) v} :=
    (U : Type.{u})
    (struct : data C U)

  attribute obj.U [coercion]

end typeclass open typeclass

