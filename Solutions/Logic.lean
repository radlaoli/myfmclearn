section propositional
/- Obs: Ao longo das demonstrações fui aprendendo formas diferentes de fazer <<as mesmas coisas>>,
por isso ficou irregular.
Porém pretendo padronizar-/
variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro h
  intro h1
  apply h1 h


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnnp
  by_cases hnp: P
  · exact hnp
  · exfalso
    apply hnnp
    exact hnp


theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  · intro nnp
    by_cases hnp: P
    · exact hnp
    · exfalso
      apply nnp
      exact hnp
  · intro hp
    intro np
    apply np
    exact hp




------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro h
  rcases h with hp|hq
  right
  exact hp
  left
  exact hq

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro h
  constructor
  exact h.2
  exact h.1


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro h
  intro hp
  rcases h with h1|h2
  contradiction
  exact h2

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro h
  intro hn
  rcases h with hp|hq
  contradiction
  exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq hnq hp
  apply hnq
  apply hpq
  exact hp

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro hnpq hp
  by_cases hq : Q
  exact hq
  exfalso
  apply hnpq hq
  exact hp


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  · intro hpq hnq hp
    have hq: Q := hpq hp
    have hf: False := hnq hq
    contradiction
  · intro hnpnq hp
    by_cases hq: Q
    · exact hq
    · have hnp : ¬P := hnpnq hq
      have hc: False := hnp hp
      contradiction



------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h
  apply h
  right
  intro hp
  apply h
  left
  exact hp



------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro himp hnp
  have hpq: P → Q := by
    intro hp
    have hc: False:= hnp hp
    contradiction
  have hp: P := himp hpq
  have hc: False := hnp hp
  contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases h: P
  right
  intro hq
  exact h
  left
  intro hp
  exfalso
  exact h hp


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro puq npnq
  rcases puq with hp|hq
  · have hc: False:= npnq.1 hp
    contradiction
  · have hc: False := npnq.2 hq
    contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro peq npnq
  rcases npnq with np|nq
  · have f1: False := np peq.1
    contradiction
  · have f2: False := nq peq.2
    contradiction






------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro h
  constructor
  · intro p
    have pq: P ∨ Q:= by
      · left
        exact p
    have f: False := h pq
    exact f
  · intro q
    have pq: P ∨ Q:= by
      · right
        exact q
    have f : False := h pq
    exact f


theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro npnq pq
  rcases pq with p|q
  · have np: ¬P := npnq.1
    have f: False := np p
    contradiction
  . have nq : ¬ Q := npnq.2
    have f: False := nq q
    contradiction

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro h
  by_cases lemp: P
  · left
    · intro q
      have pq : (P ∧ Q) := by
        constructor
        · exact lemp
        · exact q
      have f : False := h pq
      contradiction
  · right
    exact lemp




theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro hd peq
  rcases hd with nq|np
  · have q: Q := peq.right
    have f : False := nq q
    contradiction
  . have p : P := peq.left
    have f: False:= np p
    contradiction


theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  · intro h
    by_cases hP : P
    · left
      intro hQ
      have hPQ : P ∧ Q := ⟨hP, hQ⟩
      exact h hPQ
    · right
      exact hP
  · intro h hPQ
    rcases h with (hNQ | hNP)
    · exact hNQ hPQ.right
    · exact hNP hPQ.left


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  · intro h
    constructor
    · intro p
      have pq: P ∨ Q:= by
        · left
          exact p
      have f: False := h pq
      exact f
    · intro q
      have pq: P ∨ Q:= by
        · right
          exact q
      have f : False := h pq
      exact f
  · intro npnq pq
    rcases pq with p|q
    · have np: ¬P := npnq.1
      have f: False := np p
      contradiction
    . have nq : ¬ Q := npnq.2
      have f: False := nq q
      contradiction


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro pqr
  have p: P := pqr.left
  have qur: (Q ∨ R ) := pqr.right
  rcases qur with q|r
  · left
    constructor
    · exact p
    · exact q
  · right
    constructor
    · exact p
    · exact r

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro h
  rcases h with pq|pr
  · constructor
    · have p: P := pq.1
      exact p
    · left
      have q: Q := pq.2
      exact q
  · constructor
    · have p: P := pr.1
      exact p
    · right
      · have r: R := pr.2
        exact r



theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  rcases h with hp|hd
  constructor
  left
  exact hp
  left
  exact hp
  constructor
  right
  exact hd.left
  right
  exact hd.right


theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  have pq : (P ∨ Q) := h.1
  have pr : (P ∨ R) := h.2
  rcases pq with p|q
  · left
    exact p
  rcases pr with p|r
  · left
    exact p
  · right
    constructor
    · exact q
    · exact r





------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h p q
  have peq: (P ∧ Q) := by
    constructor
    · exact p
    · exact q
  have r: R := h peq
  exact r

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro h peq
  have p: P := peq.1
  have qr: (Q → R):= h p
  have q : Q := peq.2
  have r: R := qr q
  exact r



------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro h
  exact h


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro h
  left
  exact h

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro h
  right
  exact h

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro h
  exact h.left

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro h
  exact h.right


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  · intro pup
    rcases pup with hp1|hp2
    · exact hp1
    · exact hp2
  · intro hp
    · left
      exact hp

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  · intro pep
    exact pep.1
  · intro hp
    constructor
    · exact hp
    · exact hp



------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro h
  contradiction

theorem true_top :
  P → True  := by
  intro h
  trivial --Ohh


end propositional

----------------------------------------------------------------

section predicate

variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro h
  intro n
  intro Pn
  have ep: ∃ x, P x:= by
    exists n
  have f : False := h ep
  exact f


theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  intro h
  intro he
  have ⟨ x, hx ⟩ := he
  have nPx: ¬P x := h x
  exact nPx hx


theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  intro h
  by_cases hn : ∃ x, ¬P x
  · exact hn
  · have : ∀ x, P x := by
      intro x
      by_cases hx : P x
      · exact hx
      · have : ∃ x, ¬ P x := ⟨x, hx⟩
        contradiction
    contradiction


theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  intro h
  intro Pa
  have ⟨x, nPx ⟩:= h
  have Px: P x:= Pa x
  exact nPx Px

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  constructor
  · intro h
    by_cases hn : ∃ x, ¬P x
    · exact hn
    · have : ∀ x, P x := by
        intro x
        by_cases hx : P x
        · exact hx
        · have : ∃ x, ¬ P x := ⟨x, hx⟩
          contradiction
      contradiction
  · intro h
    intro Pa
    have ⟨x, nPx ⟩:= h
    have Px: P x:= Pa x
    exact nPx Px

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  constructor
  · intro h
    intro n
    intro Pn
    have ep: ∃ x, P x:= by
      exists n
    have f : False := h ep
    exact f
  · intro h
    intro he
    have ⟨ x, hx ⟩ := he
    have nPx: ¬P x := h x
    exact nPx hx


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  intro he
  intro Pa
  have ⟨n, hn⟩ := he
  have nPn: ¬P n:= Pa n
  exact nPn hn



theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  intro ha
  intro he
  have ⟨x, nPx ⟩:= he
  have Px : P x:= ha x
  exact nPx Px

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  intro h x
  by_cases h1 : P x
  · exact h1
  · have h2: ∃ x, ¬ P x := ⟨x, h1⟩
    contradiction

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  intro h
  by_cases hn:∃ x, P x
  · exact hn
  · have: ∀ x, ¬ P x := by
      intro x
      by_cases hx : P x
      · have : ∃ x, P x := ⟨x, hx⟩
        contradiction
      · exact hx
    contradiction

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  constructor
  · intro ha
    intro he
    have ⟨x, nPx ⟩:= he
    have Px : P x:= ha x
    exact nPx Px
  · intro h x
    by_cases h1 : P x
    · exact h1
    · have h2: ∃ x, ¬ P x := ⟨x, h1⟩
      contradiction

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  constructor
  · intro h1 h2
    have ⟨n,hn⟩:= h1
    have nPn: ¬P n:= h2 n
    apply nPn hn
  · intro h
    by_cases hn:∃ x, P x
    · exact hn
    · have: ∀ x, ¬ P x := by
        intro x
        by_cases hx : P x
        · have : ∃ x, P x := ⟨x, hx⟩
          contradiction
        · exact hx
      contradiction


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  intro h
  have ⟨ p,hp ⟩ := h
  have Pp: P p:= hp.left
  have Pq: Q p:= hp.right
  constructor
  · exists p
  · exists p





theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  intro h
  have ⟨n , hn⟩ := h
  rcases hn with Pn| Qn
  · left
    exists n
  · right
    exists n



theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  intro h
  rcases h with h1|h2
  · have ⟨n,Pn ⟩:= h1
    exists n
    left
    · exact Pn
  · have ⟨n, Qn ⟩:= h2
    exists n
    right
    · exact Qn

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  intro h
  constructor
  · intro n
    have PQn : P n ∧ Q n := h n
    have Pn : P n := PQn.left
    exact Pn
  · intro n
    have PQn : P n ∧ Q n := h n
    have Qn : Q n := PQn.right
    exact Qn

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  intro h n
  constructor
  · have Pn: P n:= h.left n
    exact Pn
  · have Qn : Q n:= h.right n
    exact Qn


theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  intro h n
  rcases h with hp|hq
  · left
    · have Pn: P n:= hp n
      exact Pn
  · right
    · have Qn: Q n:= hq n
      exact Qn



end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
