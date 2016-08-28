axiom dne {p: Prop}:  ¬¬ p -> p

theorem em {p: Prop}: p ∨ ¬ p :=
  have Hdn: ¬ ¬ (p ∨ ¬ p),
    from (assume Hcontra: ¬ (p ∨ ¬p),
                 have Hnp: ¬ p, from (assume Hp: p, Hcontra (or.inl Hp)),
                 Hcontra (or.inr Hnp)),
  show p ∨ ¬ p, from dne Hdn

open classical

example {p: Prop} (H: ¬¬p): p :=
  by_cases
    (assume H1: p, H1)
    (assume H1: ¬ p, absurd H1 H)

example {p: Prop} (H: ¬¬p): p :=
  by_contradiction
    (assume H1: ¬ p,
      show false, from H H1)

example {p q: Prop} (H: ¬ (p ∧ q)): ¬ p ∨ ¬ q :=
  or.elim (em p)
    (assume Hp: p, or.inr
            (show ¬ q, from
              assume Hq: q, H (and.intro Hp Hq)))
    (assume Hnp: ¬p, or.inl Hnp)
