open classical

variables p q r s: Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume Hpq: p ∧ q,
      have Hp: p, from and.left Hpq,
      have Hq: q, from and.right Hpq,
      and.intro Hq Hp)
    (assume Hqp: q ∧ p,
      have Hp: p, from and.right Hqp,
      have Hq: q, from and.left Hqp,
      and.intro Hp Hq)

example: p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume Hpq: p ∨ q,
      or.elim Hpq
        (assume Hp: p, or.inr Hp)
        (assume Hq: q, or.inl Hq))
    (assume Hqp: q ∨ p,
      or.elim Hqp
        (assume Hq: q, or.inr Hq)
        (assume Hp: p, or.inl Hp))


-- associativity of ∧ and ∨
example: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have suff: (p ∧ q) ∧ r → p ∧ (q ∧ r),
    from (assume H: (p ∧ q) ∧ r,
                 have Hpq: p ∧ q, from and.left H,
                 have Hp: p, from and.left Hpq,
                 have Hq: q, from and.right Hpq,
                 have Hr: r, from and.right H,
         and.intro Hp (and.intro Hq Hr)),
  have nece: p ∧ (q ∧ r) → (p ∧ q) ∧ r,
    from (assume H: p ∧ (q ∧ r),
                 have Hqr: q ∧ r, from and.right H,
                 have Hp: p, from and.left H,
                 have Hq: q, from and.left Hqr,
                 have Hr: r, from and.right Hqr,
         and.intro (and.intro Hp Hq) Hr),
  iff.intro suff nece

example: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have suff: (p ∨ q) ∨ r → p ∨ (q ∨ r),
    from (assume Hpqr: (p ∨ q) ∨ r,
                 or.elim Hpqr
                   (assume Hpq: p ∨ q, or.elim Hpq or.inl (assume Hq: q, or.inr (or.inl Hq)))
                   (assume Hr: r, or.inr (or.inr Hr))),
  have nece: p ∨ (q ∨ r) → (p ∨ q) ∨ r,
    from (assume Hpqr: p ∨ (q ∨ r),
                 or.elim Hpqr
                   (assume Hp: p, or.inl (or.inl Hp))
                   (assume Hqr: q ∨ r, or.elim Hqr (assume Hq: q, or.inl (or.inr Hq)) or.inr)),
  iff.intro suff nece

-- distributivity
example: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have suff: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r),
    from (assume H: p ∧ (q ∨ r),
                 have Hp: p, from and.left H,
                 or.elim (and.right H)
                   (assume Hq: q, or.inl (and.intro Hp Hq))
                   (assume Hr: r, or.inr (and.intro Hp Hr))),
  have nece: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r),
    from (assume H: (p ∧ q) ∨ (p ∧ r),
                 or.elim H
                   (assume Hpq: p ∧ q, and.intro (and.left Hpq) (or.inl (and.right Hpq)))
                   (assume Hpr: p ∧ r, and.intro (and.left Hpr) (or.inr (and.right Hpr)))),
  iff.intro suff nece

-- other properties
example: (p → (q → r)) ↔ (p ∧ q → r) :=
  have suff: (p → (q → r)) → (p ∧ q → r),
    from (assume H: (p → (q → r)),
          assume Hpq: p ∧ q, H (and.left Hpq) (and.right Hpq)),
  have nece: (p ∧ q → r) → (p → (q → r)),
    from (assume H: (p ∧ q → r),
          assume Hp: p,
          assume Hq: q,
            H (and.intro Hp Hq)),
  iff.intro suff nece

example: ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have suff: ((p ∨ q) → r) → (p → r) ∧ (q → r),
    from (assume H: ((p ∨ q) → r),
                 have Hpr: p → r, from (assume Hp: p, H (or.inl Hp)),
                 have Hqr: q → r, from (assume Hq: q, H (or.inr Hq)),
                 and.intro Hpr Hqr),
  have nece: (p → r) ∧ (q → r) → ((p ∨ q) → r),
    from (assume H: (p → r) ∧ (q → r),
          assume Hpq: (p ∨ q),
          or.elim Hpq (and.left H) (and.right H)),
  iff.intro suff nece

example: ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  have suff: ¬ (p ∨ q) → ¬ p ∧ ¬ q,
    from (assume Hnpq: ¬ (p ∨ q),
                 have Hnp: ¬ p, from (assume Hp: p, Hnpq (or.inl Hp)),
                 have Hnq: ¬ q, from (assume Hq: q, Hnpq (or.inr Hq)),
                 and.intro Hnp Hnq),
  have nece: ¬ p ∧ ¬ q → ¬ (p ∨ q),
    from (assume Hnpnq: ¬ p ∧ ¬ q,
                 (assume Hpq: p ∨ q,
                         or.elim Hpq (and.left Hnpnq) (and.right Hnpnq))),
  iff.intro suff nece

example: ¬ p ∨ ¬ q → ¬ (p ∧ q) :=
  assume Hnpnq: ¬ p ∨ ¬ q,
  assume Hpq: (p ∧ q),
  or.elim Hnpnq
    (assume Hnp: ¬ p, Hnp (and.left Hpq))
    (assume Hnq: ¬ q, Hnq (and.right Hpq))

example: ¬ (p ∧ ¬ p) :=
  assume Hpnp: (p ∧ ¬ p),
    (and.right Hpnp) (and.left Hpnp)

example: p ∧ ¬ q → ¬ (p → q) :=
  assume Hpnq: p ∧ ¬ q,
  assume Hpq: p → q,
  have Hp: p, from and.left Hpnq,
  have Hnq: ¬ q, from and.right Hpnq,
  Hnq (Hpq Hp)

example: ¬ p → (p → q) :=
  assume Hnp: ¬ p,
  assume Hp: p,
  absurd Hp Hnp

example: (¬ p ∨ q) → (p → q) :=
  assume Hnpq: ¬ p ∨ q,
  assume Hp: p,
  or.elim Hnpq
    (assume Hnp: ¬ p, absurd Hp Hnp)
    (assume Hq: q, Hq)

example: p ∨ false ↔ p :=
  have suff: p ∨ false → p,
    from (assume Hpf: p ∨ false,
                 or.elim Hpf (assume Hp: p, Hp) (assume Hf: false, false.elim Hf)),
  have nece: p → p ∨ false,
    from (assume Hp: p, or.inl Hp),
  iff.intro suff nece

example: p ∧ false ↔ false :=
  have suff: p ∧ false → false,
    from (assume Hpf: p ∧ false, and.right Hpf),
  have nece: false → p ∧ false,
    from (assume Hf: false, false.elim Hf),
  iff.intro suff nece

example: ¬ (p ↔ ¬ p) :=
  assume Hpnp: (p ↔ ¬ p),
  iff.elim (assume H1: p → ¬ p,
            assume H2: ¬ p → p,
            have Hp: p, from H2 (assume Hp: p, H1 Hp Hp),
             (H1 Hp Hp))
           Hpnp

example: (p → q) → (¬ q → ¬ p) :=
  assume Hpq: p → q,
  assume Hnq: ¬ q,
  assume Hp: p,
  Hnq (Hpq Hp)

-- these require classical reasoning
example: (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume Hprs: p → r ∨ s,
  by_cases
        (assume Hr: r,
           or.inl (assume Hp: p, Hr))
        (assume Hnr: ¬ r,
           or.inr (assume Hp: p,
                   have Hrs: r ∨ s, from Hprs Hp,
                   or.elim Hrs
                           (assume Hr: r, absurd Hr Hnr)
                           (assume Hs: s, Hs)))

example: ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  assume Hnpq: ¬ (p ∧ q),
  by_cases
    (assume Hp: p,
      by_cases (assume Hq: q, false.elim (Hnpq (and.intro Hp Hq)))
               (assume Hnq: ¬ q, or.inr Hnq))
    (assume Hnp: ¬ p, or.inl Hnp)

example: ¬ (p → q) → p ∧ ¬ q :=
  assume Hnpq: ¬ (p → q),
  by_cases
    (assume Hp: p,
     by_cases
       (assume Hq: q, show p ∧ ¬ q, from false.elim (Hnpq (assume Hp: p, Hq)))
       (assume Hnq: ¬ q, and.intro Hp Hnq))
    (assume Hnp: ¬ p,
      show p ∧ ¬ q, from false.elim (Hnpq (assume Hp: p, false.elim (Hnp Hp))))

example: (p → q) → (¬ p ∨ q) :=
  assume Hpq: p → q,
  by_cases
    (assume Hp: p, or.inr (Hpq Hp))
    (assume Hnp: ¬ p, or.inl Hnp)

example: (¬ q → ¬ p) → p → q :=
  assume Hnqnp: ¬ q → ¬ p,
  assume Hp: p,
  by_cases
    (assume Hq: q, Hq)
    (assume Hnq: ¬ q, false.elim (Hnqnp Hnq Hp))

example: p ∨ ¬ p :=
  em p

example: (((p → q) → p) → p) :=
  assume Hpqp: ((p → q) → p),
  by_cases
    (assume Hp: p, Hp)
    (assume Hnp: ¬ p,
      Hpqp (assume Hp: p, absurd Hp Hnp))
