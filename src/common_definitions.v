(** * Various useful general purpose notations and definitions *)

Notation eta_expand x := (fst x, snd x).

Definition prod_eta A B (p : A * B) : p = eta_expand p
    := match p as p return p = eta_expand p with
         | (x, y) => Coq.Init.Logic.eq_refl
       end.
