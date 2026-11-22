/-
  A Lean 4 check of the proofs in the paper "Your proof".

  Contents:
    1. The Sure Thing theorem, for any finitely additive probability measure on any algebra of
       events (two cells; and two cells that partition the measure, at any ratio).
    2. The main proof, steps (1) to (5), and the whole proof as one statement.
    3. Section 5.1: the subdivision lemma, (S1), (S3) which is (B), and (S4).
    4. Section 5.3: Jeffrey's rule (J) as a measure, and its conflict with the proved value.
    5. Models: the sets of Appendix B, and a four-point case for section 5.3. They show that
       the conditions of the theorems can all be met.

  Checked with Lean 4.36.0, using nothing beyond Lean's own library:  lean YourProof.lean
  A run with no error means every theorem below is accepted. The lines printed at the end name
  the axioms the results rest on.

  The letters are the paper's: `π` is your measure, and `Pr` is the recording's.

  How to read this file against the paper: each `theorem` carries, in its comment, the
  display of the paper that it states. What Lean certifies is that each statement follows
  from the hypotheses written in front of it. That a statement here says what the paper's
  sentence says is checked by reading the two side by side.
-/

namespace YourProof

/-! ## The arithmetic of the steps, as statements about rational numbers alone -/

theorem arith1 (h c hc hnc nhc nhnc nh : Rat) (coin : h = 1/2) (ball : c = 1/2)
    (indep : hc / c = h) (s1 : h = hc + hnc) (s2 : c = hc + nhc) (s3 : nh = nhc + nhnc)
    (cc : h + nh = 1) : hc = 1/4 ∧ hnc = 1/4 ∧ nhc = 1/4 ∧ nhnc = 1/4 := by grind

theorem arith2 (h nh hc hnc pM pT : Rat) (coin : h = 1/2) (cc : h + nh = 1)
    (o1 : hc = 1/4) (o2 : hnc = 1/4) (dM : pM = hc + nh) (dT : pT = hnc + nh) :
    hc / pM = 1/3 ∧ hnc / pT = 1/3 := by grind

theorem arithCells (PX xa xna y z xb w pa pb pab pbna por pnor r : Rat)
    (s1 : PX = xa + xna) (s2 : xna = y + z) (s3 : xb = w + y) (s4 : por = pa + pbna)
    (s5 : pb = pab + pbna) (n1 : w ≤ pab) (p1 : 0 ≤ w) (s6 : por + pnor = 1)
    (n2 : z ≤ pnor) (p2 : 0 ≤ z) (a_pos : pa ≠ 0) (b_pos : pb ≠ 0)
    (ra : xa / pa = r) (rb : xb / pb = r)
    (h_and : pab = 0) (h_or : por = 1) : PX = r := by grind

theorem arithTP (PX x1 x2 e e' : Rat) (s : PX = x1 + x2) (he : e ≠ 0) (he' : e' ≠ 0) :
    PX = e * (x1 / e) + e' * (x2 / e') := by grind

theorem arithWithin (x1 x2 p1 p2 c : Rat) (h1 : x1 / p1 = c) (h2 : x2 / p2 = c)
    (a : 0 < p1) (b : 0 < p2) : (x1 + x2) / (p1 + p2) = c := by grind

theorem arithScale (t x e : Rat) (ht : t ≠ 0) (he : e ≠ 0) : (t * x) / (t * e) = x / e := by
  grind

theorem arithEdge (PX x1 x2 e ne c : Rat) (s : PX = x1 + x2) (cc : e + ne = 1) (he : e = 1)
    (n : x2 ≤ ne) (p : 0 ≤ x2) (h : x1 / e = c) : PX = c := by grind

theorem arithST (PX x1 x2 b b' : Rat) (s : PX = x1 + x2) (c : b + b' = 1)
    (hb : b ≠ 0) (hb' : b' ≠ 0) (h : x1 / b = x2 / b') : PX = x1 / b := by grind

/-- A standard (finitely additive) probability measure on an algebra of events.
    Events are sets of points of `Ω`, written as predicates. Only three things are asked:
    values are not negative, the whole has 1, and values add over exclusive events. -/
structure Measure (Ω : Type) where
  /-- which sets of points are events (the algebra) -/
  ev : (Ω → Prop) → Prop
  ev_true : ev (fun _ => True)
  ev_not : ∀ {A : Ω → Prop}, ev A → ev (fun ω => ¬ A ω)
  ev_and : ∀ {A B : Ω → Prop}, ev A → ev B → ev (fun ω => A ω ∧ B ω)
  /-- the measure -/
  P : (Ω → Prop) → Rat
  nonneg : ∀ {A : Ω → Prop}, ev A → 0 ≤ P A
  total : P (fun _ => True) = 1
  add : ∀ {A B : Ω → Prop}, ev A → ev B → (∀ ω, ¬ (A ω ∧ B ω)) →
    P (fun ω => A ω ∨ B ω) = P A + P B

variable {Ω : Type} (m : Measure Ω)

namespace Measure

/-- The conditional probability of `X` given `B`: the ratio of two values of the measure. -/
def cond (X B : Ω → Prop) : Rat := m.P (fun ω => X ω ∧ B ω) / m.P B

theorem ev_or {A B : Ω → Prop} (hA : m.ev A) (hB : m.ev B) : m.ev (fun ω => A ω ∨ B ω) := by
  have h := m.ev_not (m.ev_and (m.ev_not hA) (m.ev_not hB))
  have e : (fun ω => ¬ (¬ A ω ∧ ¬ B ω)) = (fun ω => A ω ∨ B ω) := by
    funext ω; apply propext; constructor
    · intro h; cases Classical.em (A ω) with
      | inl a => exact Or.inl a
      | inr na => cases Classical.em (B ω) with
        | inl b => exact Or.inr b
        | inr nb => exact absurd ⟨na, nb⟩ h
    · intro h ⟨na, nb⟩; cases h with
      | inl a => exact na a
      | inr b => exact nb b
  rw [e] at h; exact h

/-- An event splits over another event and its negation. -/
theorem split {X B : Ω → Prop} (hX : m.ev X) (hB : m.ev B) :
    m.P X = m.P (fun ω => X ω ∧ B ω) + m.P (fun ω => X ω ∧ ¬ B ω) := by
  have h := m.add (m.ev_and hX hB) (m.ev_and hX (m.ev_not hB))
    (by intro ω h; exact h.2.2 h.1.2)
  have e : (fun ω => (X ω ∧ B ω) ∨ (X ω ∧ ¬ B ω)) = X := by
    funext ω; apply propext; constructor
    · intro h; cases h with
      | inl h => exact h.1
      | inr h => exact h.1
    · intro x; cases Classical.em (B ω) with
      | inl b => exact Or.inl ⟨x, b⟩
      | inr nb => exact Or.inr ⟨x, nb⟩
  rw [e] at h; exact h

/-- An event and its negation have 1 together. -/
theorem compl {B : Ω → Prop} (hB : m.ev B) : m.P B + m.P (fun ω => ¬ B ω) = 1 := by
  have h := m.split m.ev_true hB
  have e1 : (fun ω => True ∧ B ω) = B := by funext ω; simp
  have e2 : (fun ω => True ∧ ¬ B ω) = (fun ω => ¬ B ω) := by funext ω; simp
  rw [e1, e2, m.total] at h; exact h.symm

/-- A part has no more than the whole. -/
theorem mono {A B : Ω → Prop} (hA : m.ev A) (hB : m.ev B) (h : ∀ ω, A ω → B ω) :
    m.P A ≤ m.P B := by
  have s := m.split hB hA
  have e : (fun ω => B ω ∧ A ω) = A := by
    funext ω; apply propext; exact ⟨fun h => h.2, fun a => ⟨h ω a, a⟩⟩
  rw [e] at s
  have n := m.nonneg (m.ev_and hB (m.ev_not hA))
  grind

/-- **Sure Thing** (the paper, end of section 1.3):
    `π(X | B) = π(X | ¬B)  ⊨  π(X) = π(X | B)`.
    Both conditional probabilities are defined, that is, `B` and `¬B` have positive value. -/
theorem sure_thing {X B : Ω → Prop} (hX : m.ev X) (hB : m.ev B)
    (hB0 : m.P B ≠ 0) (hB1 : m.P (fun ω => ¬ B ω) ≠ 0)
    (h : m.cond X B = m.cond X (fun ω => ¬ B ω)) :
    m.P X = m.cond X B := by
  have s := m.split hX hB
  have c := m.compl hB
  unfold cond at *
  exact arithST _ _ _ _ _ s c hB0 hB1 h

/-- The impossible event has 0. -/
theorem P_false : m.P (fun _ => False) = 0 := by
  have c := m.compl m.ev_true
  have e : (fun (_ : Ω) => ¬ True) = (fun _ => False) := by funext ω; simp
  rw [e, m.total] at c
  grind

/-- **Sure Thing over two cells that partition the measure**, at any ratio `r`:
    if `π(X | a) = π(X | b) = r`, `π(a ∧ b) = 0` and `π(a ∨ b) = 1`, then `π(X) = r`.
    Step (5) of the main proof is this at `r = 1/3`. Step (S3) of section 5.1 is this in the
    later measure. -/
theorem sure_thing_cells {X a b : Ω → Prop} {r : Rat} (hX : m.ev X) (ha : m.ev a) (hb : m.ev b)
    (a_pos : m.P a ≠ 0) (b_pos : m.P b ≠ 0)
    (ra : m.cond X a = r) (rb : m.cond X b = r)
    (h_and : m.P (fun ω => a ω ∧ b ω) = 0) (h_or : m.P (fun ω => a ω ∨ b ω) = 1) :
    m.P X = r := by
  -- X splits over a; the part outside a splits over b
  have s1 := m.split hX ha
  have s2 := m.split (m.ev_and hX (m.ev_not ha)) hb
  -- X and b splits over a
  have s3 := m.split (m.ev_and hX hb) ha
  -- a or b splits over a
  have s4 := m.split (m.ev_or ha hb) ha
  have e4a : (fun ω => (a ω ∨ b ω) ∧ a ω) = a := by
    funext ω; apply propext; exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
  have e4b : (fun ω => (a ω ∨ b ω) ∧ ¬ a ω) = (fun ω => b ω ∧ ¬ a ω) := by
    funext ω; apply propext; constructor
    · intro h; cases h.1 with
      | inl x => exact absurd x h.2
      | inr x => exact ⟨x, h.2⟩
    · intro h; exact ⟨Or.inr h.1, h.2⟩
  rw [e4a, e4b] at s4
  -- b splits over a
  have s5 := m.split hb ha
  have e5 : (fun ω => b ω ∧ a ω) = (fun ω => a ω ∧ b ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e5] at s5
  -- what lies in X, a and b together has no more than a and b together: nothing
  have n1 : m.P (fun ω => (X ω ∧ b ω) ∧ a ω) ≤ m.P (fun ω => a ω ∧ b ω) :=
    m.mono (m.ev_and (m.ev_and hX hb) ha) (m.ev_and ha hb) (fun ω h => ⟨h.2, h.1.2⟩)
  have p1 := m.nonneg (m.ev_and (m.ev_and hX hb) ha)
  -- what lies in X outside both a and b has no more than what lies outside both: nothing
  have s6 := m.compl (m.ev_or ha hb)
  have n2 : m.P (fun ω => (X ω ∧ ¬ a ω) ∧ ¬ b ω) ≤ m.P (fun ω => ¬ (a ω ∨ b ω)) :=
    m.mono (m.ev_and (m.ev_and hX (m.ev_not ha)) (m.ev_not hb)) (m.ev_not (m.ev_or ha hb))
      (fun ω h x => x.elim h.1.2 h.2)
  have p2 := m.nonneg (m.ev_and (m.ev_and hX (m.ev_not ha)) (m.ev_not hb))
  have e7 : (fun ω => (X ω ∧ ¬ a ω) ∧ b ω) = (fun ω => (X ω ∧ b ω) ∧ ¬ a ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  rw [e7] at s2
  unfold cond at ra rb
  exact arithCells _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 s4 s5 n1 p1 s6 n2 p2 a_pos b_pos ra rb
    h_and h_or

/-- **(S4), second half: total probability.** `π(X) = π(E) π(X | E) + π(¬E) π(X | ¬E)`. -/
theorem total_probability {X E : Ω → Prop} (hX : m.ev X) (hE : m.ev E)
    (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0) :
    m.P X = m.P E * m.cond X E + m.P (fun ω => ¬ E ω) * m.cond X (fun ω => ¬ E ω) := by
  have s := m.split hX hE
  unfold cond
  exact arithTP _ _ _ _ _ s hE0 hE1

/-- **(S1): Sure Thing inside `E`.** If two exclusive cells make up `E` and `X` has the ratio `c`
    in each of them, then `π(X | E) = c`. -/
theorem sure_thing_within {X E a1 a2 : Ω → Prop} {c : Rat} (hX : m.ev X)
    (ha1 : m.ev a1) (ha2 : m.ev a2)
    (cells : ∀ ω, E ω ↔ (a1 ω ∨ a2 ω)) (excl : ∀ ω, ¬ (a1 ω ∧ a2 ω))
    (pos1 : m.P a1 ≠ 0) (pos2 : m.P a2 ≠ 0)
    (r1 : m.cond X a1 = c) (r2 : m.cond X a2 = c) : m.cond X E = c := by
  have eE : E = (fun ω => a1 ω ∨ a2 ω) := by funext ω; exact propext (cells ω)
  subst eE
  have pE : m.P (fun ω => a1 ω ∨ a2 ω) = m.P a1 + m.P a2 := m.add ha1 ha2 excl
  have pXE : m.P (fun ω => (X ω ∧ a1 ω) ∨ (X ω ∧ a2 ω))
      = m.P (fun ω => X ω ∧ a1 ω) + m.P (fun ω => X ω ∧ a2 ω) :=
    m.add (m.ev_and hX ha1) (m.ev_and hX ha2) (fun ω h => excl ω ⟨h.1.2, h.2.2⟩)
  have e : (fun ω => X ω ∧ (a1 ω ∨ a2 ω)) = (fun ω => (X ω ∧ a1 ω) ∨ (X ω ∧ a2 ω)) := by
    funext ω; apply propext; constructor
    · intro h; cases h.2 with
      | inl x => exact Or.inl ⟨h.1, x⟩
      | inr x => exact Or.inr ⟨h.1, x⟩
    · intro h; cases h with
      | inl x => exact ⟨x.1, Or.inl x.2⟩
      | inr x => exact ⟨x.1, Or.inr x.2⟩
  have n1 := m.nonneg ha1
  have n2 := m.nonneg ha2
  have q1 : 0 < m.P a1 := by grind
  have q2 : 0 < m.P a2 := by grind
  unfold cond at *
  rw [e, pXE, pE]
  exact arithWithin _ _ _ _ _ r1 r2 q1 q2

/-- **(S3) at the edge, where the one cell is all of `E`.** In any measure in which `E` is
    certain and `X` has the ratio `c` given `E`, the unconditional probability of `X` is `c`. -/
theorem certain_gives_ratio {X E : Ω → Prop} {c : Rat} (hX : m.ev X) (hE : m.ev E)
    (E_certain : m.P E = 1) (ratio : m.cond X E = c) : m.P X = c := by
  have s := m.split hX hE
  have cc := m.compl hE
  have n : m.P (fun ω => X ω ∧ ¬ E ω) ≤ m.P (fun ω => ¬ E ω) :=
    m.mono (m.ev_and hX (m.ev_not hE)) (m.ev_not hE) (fun ω h => h.2)
  have p := m.nonneg (m.ev_and hX (m.ev_not hE))
  unfold cond at ratio
  exact arithEdge _ _ _ _ _ _ s cc E_certain n p ratio

end Measure

/-! ## Steps (1) and (2): the recording's measure, written `Pr` here -/

section Recording

variable (Pr : Measure Ω) (H C : Ω → Prop)

/-- You are awakened on Monday: heads with a Monday ball, or tails. -/
def M : Ω → Prop := fun ω => (H ω ∧ C ω) ∨ ¬ H ω
/-- You are awakened on Tuesday: heads with a Tuesday ball, or tails. -/
def T : Ω → Prop := fun ω => (H ω ∧ ¬ C ω) ∨ ¬ H ω

/-- **(1)** From the first assumption (the coin has 1/2, a Monday ball has 1/2, and the two are
    independent, `Pr(H | C) = Pr(H)`): each of the four outcomes has 1/4. -/
theorem step1 (hH : Pr.ev H) (hC : Pr.ev C)
    (coin : Pr.P H = 1/2) (ball : Pr.P C = 1/2) (indep : Pr.cond H C = Pr.P H) :
    Pr.P (fun ω => H ω ∧ C ω) = 1/4 ∧ Pr.P (fun ω => H ω ∧ ¬ C ω) = 1/4 ∧
    Pr.P (fun ω => ¬ H ω ∧ C ω) = 1/4 ∧ Pr.P (fun ω => ¬ H ω ∧ ¬ C ω) = 1/4 := by
  have s1 := Pr.split hH hC
  have s2 := Pr.split hC hH
  have s3 := Pr.split (Pr.ev_not hH) hC
  have c := Pr.compl hH
  have e : (fun ω => C ω ∧ H ω) = (fun ω => H ω ∧ C ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have e' : (fun ω => C ω ∧ ¬ H ω) = (fun ω => ¬ H ω ∧ C ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e, e'] at s2
  unfold Measure.cond at indep
  exact arith1 _ _ _ _ _ _ _ coin ball indep s1 s2 s3 c

/-- **(2)** `Pr(H | [M]) = Pr(H | [T]) = 1/3`: each of the two wakings takes place on three of
    the four outcomes, one of them with heads. -/
theorem step2 (hH : Pr.ev H) (hC : Pr.ev C)
    (coin : Pr.P H = 1/2) (ball : Pr.P C = 1/2) (indep : Pr.cond H C = Pr.P H) :
    Pr.cond H (M H C) = 1/3 ∧ Pr.cond H (T H C) = 1/3 := by
  obtain ⟨o1, o2, o3, o4⟩ := step1 Pr H C hH hC coin ball indep
  have c := Pr.compl hH
  -- heads together with a Monday waking is heads with a Monday ball; likewise for Tuesday
  have eM : (fun ω => H ω ∧ M H C ω) = (fun ω => H ω ∧ C ω) := by
    funext ω; apply propext; unfold M; constructor
    · intro h; cases h.2 with
      | inl hc => exact hc
      | inr nh => exact absurd h.1 nh
    · intro h; exact ⟨h.1, Or.inl h⟩
  have eT : (fun ω => H ω ∧ T H C ω) = (fun ω => H ω ∧ ¬ C ω) := by
    funext ω; apply propext; unfold T; constructor
    · intro h; cases h.2 with
      | inl hc => exact hc
      | inr nh => exact absurd h.1 nh
    · intro h; exact ⟨h.1, Or.inl h⟩
  -- a Monday waking is: heads with a Monday ball, or tails (two exclusive events)
  have aM := Pr.add (Pr.ev_and hH hC) (Pr.ev_not hH) (by intro ω h; exact h.2 h.1.1)
  have aT := Pr.add (Pr.ev_and hH (Pr.ev_not hC)) (Pr.ev_not hH) (by intro ω h; exact h.2 h.1.1)
  have dM : Pr.P (M H C) = Pr.P (fun ω => H ω ∧ C ω) + Pr.P (fun ω => ¬ H ω) := aM
  have dT : Pr.P (T H C) = Pr.P (fun ω => H ω ∧ ¬ C ω) + Pr.P (fun ω => ¬ H ω) := aT
  unfold Measure.cond
  rw [eM, eT]
  exact arith2 _ _ _ _ _ _ coin c o1 o2 dM dT

end Recording

/-! ## Steps (3), (4) and (5): your measure, written `π` here -/

section Yours

variable {Ω' : Type} (π : Measure Ω') (H a b : Ω' → Prop)

/-- **(5)** `π(H) = 1/3`, from **(3)** `π(H | a) = π(H | b) = 1/3` and
    **(4)** `π(a ∧ b) = 0`, `π(a ∨ b) = 1`, for any standard measure `π` whatever.
    (The conditional probabilities of (3) are defined, so `a` and `b` have positive value.) -/
theorem step5 (hH : π.ev H) (ha : π.ev a) (hb : π.ev b)
    (a_pos : π.P a ≠ 0) (b_pos : π.P b ≠ 0)
    (three_a : π.cond H a = 1/3) (three_b : π.cond H b = 1/3)
    (four_and : π.P (fun ω => a ω ∧ b ω) = 0) (four_or : π.P (fun ω => a ω ∨ b ω) = 1) :
    π.P H = 1/3 := by
  exact π.sure_thing_cells hH ha hb a_pos b_pos three_a three_b four_and four_or

end Yours

/-! ## The whole proof in one statement -/

/-- **Your proof.** Let `Pr` be any standard measure that has the recording's values (the first
    assumption), and let `π` be any standard measure with two events `a` and `b` such that
    `π(H' | a) = Pr(H | [M])` and `π(H' | b) = Pr(H | [T])` (the construction, at heads) and
    `π(a ∧ b) = 0`, `π(a ∨ b) = 1` (the partition). Then `π(H') = 1/3`. -/
theorem your_proof {Ω Ω' : Type}
    (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
    (coin : Pr.P H = 1/2) (ball : Pr.P C = 1/2) (indep : Pr.cond H C = Pr.P H)
    (π : Measure Ω') (H' a b : Ω' → Prop) (hH' : π.ev H') (ha : π.ev a) (hb : π.ev b)
    (a_pos : π.P a ≠ 0) (b_pos : π.P b ≠ 0)
    (construction_a : π.cond H' a = Pr.cond H (M H C))
    (construction_b : π.cond H' b = Pr.cond H (T H C))
    (four_and : π.P (fun ω => a ω ∧ b ω) = 0) (four_or : π.P (fun ω => a ω ∨ b ω) = 1) :
    π.P H' = 1/3 := by
  obtain ⟨m2, t2⟩ := step2 Pr H C hH hC coin ball indep
  exact step5 π H' a b hH' ha hb a_pos b_pos (construction_a.trans m2) (construction_b.trans t2)
    four_and four_or

/-- **One function, one value.** A measure gives an event one value. -/
theorem one_value {Ω : Type} (m : Measure Ω) (X : Ω → Prop) (v w : Rat)
    (h1 : m.P X = v) (h2 : m.P X = w) : v = w := h1.symm.trans h2

/-- **No measure meets the conditions of your proof and gives heads another value.** Whatever
    value `v` other than `1/3` a view requires for heads, no standard measure has it together
    with the recording's values, the construction and the partition. -/
theorem no_other_value {Ω Ω' : Type}
    (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
    (coin : Pr.P H = 1/2) (ball : Pr.P C = 1/2) (indep : Pr.cond H C = Pr.P H)
    (π : Measure Ω') (H' a b : Ω' → Prop) (hH' : π.ev H') (ha : π.ev a) (hb : π.ev b)
    (a_pos : π.P a ≠ 0) (b_pos : π.P b ≠ 0)
    (construction_a : π.cond H' a = Pr.cond H (M H C))
    (construction_b : π.cond H' b = Pr.cond H (T H C))
    (four_and : π.P (fun ω => a ω ∧ b ω) = 0) (four_or : π.P (fun ω => a ω ∨ b ω) = 1)
    (v : Rat) (hv : v ≠ 1/3) : π.P H' ≠ v := by
  rw [your_proof Pr H C hH hC coin ball indep π H' a b hH' ha hb a_pos b_pos construction_a
    construction_b four_and four_or]
  exact fun h => hv h.symm

/-! ## Section 5.1 of the paper: the subdivision lemma, and conditionalization as a theorem -/

section Conditionalization

/-- An event of the old algebra, as an event of the expanded one. -/
def lift (Y : Ω → Prop) : Ω × Bool → Prop := fun p => Y p.1
/-- The one event added. -/
def Z : Ω × Bool → Prop := fun p => p.2 = true

namespace Measure

/-- **The subdivision lemma, the construction.** The algebra is expanded by the one event `Z`:
    its events are `(Y₁ ∧ Z) ∨ (Y₂ ∧ ¬Z)` with `Y₁`, `Y₂` old events, and
    `π((Y₁ ∧ Z) ∨ (Y₂ ∧ ¬Z)) = s π(Y₁) + (1 - s) π(Y₂)`, for a proportion `s` with `0 < s < 1`. -/
def subdivide (s : Rat) (hs0 : 0 < s) (hs1 : s < 1) : Measure (Ω × Bool) where
  ev := fun A => m.ev (fun ω => A (ω, true)) ∧ m.ev (fun ω => A (ω, false))
  ev_true := ⟨m.ev_true, m.ev_true⟩
  ev_not := fun h => ⟨m.ev_not h.1, m.ev_not h.2⟩
  ev_and := fun h k => ⟨m.ev_and h.1 k.1, m.ev_and h.2 k.2⟩
  P := fun A => s * m.P (fun ω => A (ω, true)) + (1 - s) * m.P (fun ω => A (ω, false))
  nonneg := by
    intro A h
    have h1 : (0 : Rat) ≤ s * m.P (fun ω => A (ω, true)) :=
      Rat.mul_nonneg (by grind) (m.nonneg h.1)
    have h2 : (0 : Rat) ≤ (1 - s) * m.P (fun ω => A (ω, false)) :=
      Rat.mul_nonneg (by grind) (m.nonneg h.2)
    grind
  total := by
    show s * m.P (fun _ => True) + (1 - s) * m.P (fun _ => True) = 1
    rw [m.total]; grind
  add := by
    intro A B hA hB h
    have a1 : m.P (fun ω => A (ω, true) ∨ B (ω, true))
        = m.P (fun ω => A (ω, true)) + m.P (fun ω => B (ω, true)) :=
      m.add hA.1 hB.1 (fun ω => h (ω, true))
    have a2 : m.P (fun ω => A (ω, false) ∨ B (ω, false))
        = m.P (fun ω => A (ω, false)) + m.P (fun ω => B (ω, false)) :=
      m.add hA.2 hB.2 (fun ω => h (ω, false))
    show s * m.P (fun ω => A (ω, true) ∨ B (ω, true))
          + (1 - s) * m.P (fun ω => A (ω, false) ∨ B (ω, false))
        = (s * m.P (fun ω => A (ω, true)) + (1 - s) * m.P (fun ω => A (ω, false)))
          + (s * m.P (fun ω => B (ω, true)) + (1 - s) * m.P (fun ω => B (ω, false)))
    rw [a1, a2]; grind

variable (s : Rat) (hs0 : 0 < s) (hs1 : s < 1)

/-- The lemma, first part: every old event keeps its value. -/
theorem subdivide_keeps (Y : Ω → Prop) : (m.subdivide s hs0 hs1).P (lift Y) = m.P Y := by
  show s * m.P (fun ω => lift Y (ω, true)) + (1 - s) * m.P (fun ω => lift Y (ω, false)) = m.P Y
  have e1 : (fun ω => lift Y (ω, true)) = Y := rfl
  have e2 : (fun ω => lift Y (ω, false)) = Y := rfl
  rw [e1, e2]; grind

/-- The values of the two cells of an old event `E`: `s π(E)` and `(1 - s) π(E)`. -/
theorem subdivide_cells (E : Ω → Prop) :
    (m.subdivide s hs0 hs1).P (fun p => lift E p ∧ Z p) = s * m.P E ∧
    (m.subdivide s hs0 hs1).P (fun p => lift E p ∧ ¬ Z p) = (1 - s) * m.P E := by
  have e1 : (fun ω => lift E (ω, true) ∧ Z (ω, true)) = E := by funext ω; simp [lift, Z]
  have e2 : (fun ω => lift E (ω, false) ∧ Z (ω, false)) = (fun (_ : Ω) => False) := by
    funext ω; simp [lift, Z]
  have e3 : (fun ω => lift E (ω, true) ∧ ¬ Z (ω, true)) = (fun (_ : Ω) => False) := by
    funext ω; simp [lift, Z]
  have e4 : (fun ω => lift E (ω, false) ∧ ¬ Z (ω, false)) = E := by funext ω; simp [lift, Z]
  constructor
  · show s * m.P (fun ω => lift E (ω, true) ∧ Z (ω, true))
        + (1 - s) * m.P (fun ω => lift E (ω, false) ∧ Z (ω, false)) = s * m.P E
    rw [e1, e2, m.P_false]; grind
  · show s * m.P (fun ω => lift E (ω, true) ∧ ¬ Z (ω, true))
        + (1 - s) * m.P (fun ω => lift E (ω, false) ∧ ¬ Z (ω, false)) = (1 - s) * m.P E
    rw [e3, e4, m.P_false]; grind

/-- **The subdivision lemma.** In the expanded measure each of the two cells of `E`, `E ∧ Z` and
    `E ∧ ¬Z`, gives every old event `X` the ratio that `E` gives it:
    `π(X | a₁) = π(X | a₂) = π(X | E)`. (For the cells of `¬E`, take `¬E` for `E`.) -/
theorem subdivision_lemma (X E : Ω → Prop) (hE : m.P E ≠ 0) :
    (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ Z p) = m.cond X E ∧
    (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ ¬ Z p) = m.cond X E := by
  obtain ⟨c1, c2⟩ := m.subdivide_cells s hs0 hs1 E
  -- X together with a cell of E is the same cell of (X and E)
  have x1 : (fun p : Ω × Bool => lift X p ∧ (lift E p ∧ Z p))
      = (fun p => lift (fun ω => X ω ∧ E ω) p ∧ Z p) := by
    funext p; apply propext; exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  have x2 : (fun p : Ω × Bool => lift X p ∧ (lift E p ∧ ¬ Z p))
      = (fun p => lift (fun ω => X ω ∧ E ω) p ∧ ¬ Z p) := by
    funext p; apply propext; exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  obtain ⟨d1, d2⟩ := m.subdivide_cells s hs0 hs1 (fun ω => X ω ∧ E ω)
  unfold cond
  rw [x1, x2, c1, c2, d1, d2]
  constructor
  · exact arithScale s _ _ (by grind) hE
  · exact arithScale (1 - s) _ _ (by grind) hE

/-- **(S3), which is (B).** Let `later` be any standard measure on the expanded algebra in which
    `E` is certain and each of the two cells of `E` has, for `X`, the ratio it is defined with
    (the ratio of the subdivision lemma). Then the unconditional probability of `X` in `later`
    is `π(X | E)`, the conditional probability in the first measure. -/
theorem conditionalization {X E : Ω → Prop} (hE0 : m.P E ≠ 0) (later : Measure (Ω × Bool))
    (hX : later.ev (lift X)) (hc1 : later.ev (fun p => lift E p ∧ Z p))
    (hc2 : later.ev (fun p => lift E p ∧ ¬ Z p))
    (E_certain : later.P (lift E) = 1)
    (cell1_pos : later.P (fun p => lift E p ∧ Z p) ≠ 0)
    (cell2_pos : later.P (fun p => lift E p ∧ ¬ Z p) ≠ 0)
    (same1 : later.cond (lift X) (fun p => lift E p ∧ Z p)
              = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ Z p))
    (same2 : later.cond (lift X) (fun p => lift E p ∧ ¬ Z p)
              = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ ¬ Z p)) :
    later.P (lift X) = m.cond X E := by
  obtain ⟨l1, l2⟩ := m.subdivision_lemma s hs0 hs1 X E hE0
  -- the two cells are exclusive, and together they are E
  have e_and : (fun p : Ω × Bool => (lift E p ∧ Z p) ∧ (lift E p ∧ ¬ Z p)) = (fun _ => False) := by
    funext p; apply propext; exact ⟨fun h => h.2.2 h.1.2, fun h => h.elim⟩
  have e_or : (fun p : Ω × Bool => (lift E p ∧ Z p) ∨ (lift E p ∧ ¬ Z p)) = lift E := by
    funext p; apply propext; constructor
    · intro h; cases h with
      | inl x => exact x.1
      | inr x => exact x.1
    · intro h; cases Classical.em (Z p) with
      | inl z => exact Or.inl ⟨h, z⟩
      | inr z => exact Or.inr ⟨h, z⟩
  have h_and : later.P (fun p => (lift E p ∧ Z p) ∧ (lift E p ∧ ¬ Z p)) = 0 := by
    rw [e_and]; exact later.P_false
  have h_or : later.P (fun p => (lift E p ∧ Z p) ∨ (lift E p ∧ ¬ Z p)) = 1 := by
    rw [e_or]; exact E_certain
  exact later.sure_thing_cells hX hc1 hc2 cell1_pos cell2_pos (same1.trans l1) (same2.trans l2)
    h_and h_or

end Measure

end Conditionalization

/-! ## Section 5.3 of the paper: Jeffrey's rule (J), and its conflict with the proved value -/

section Jeffrey

/-! The arithmetic, as statements about rational numbers alone. -/

theorem arithDivNonneg (x e : Rat) (hx : 0 ≤ x) (he : 0 < e) : 0 ≤ x / e := by
  cases Classical.em (0 ≤ x / e) with
  | inl h => exact h
  | inr h =>
    have h1 : (0 : Rat) ≤ (-(x / e)) * e := Rat.mul_nonneg (by grind) (by grind)
    have h2 : (-(x / e)) * e = -x := by grind
    rw [h2] at h1
    have hx0 : x = 0 := by grind
    have h3 : x / e = 0 := by rw [hx0]; grind
    rw [h3] at h
    grind

theorem arithJtotal (u e e' : Rat) (he : e ≠ 0) (he' : e' ≠ 0) :
    u * (e / e) + (1 - u) * (e' / e') = 1 := by grind

theorem arithJadd (u xa xb ya yb e e' : Rat) :
    u * ((xa + xb) / e) + (1 - u) * ((ya + yb) / e')
      = (u * (xa / e) + (1 - u) * (ya / e')) + (u * (xb / e) + (1 - u) * (yb / e')) := by grind

theorem arithJu (u e e' : Rat) (he : e ≠ 0) : u * (e / e) + (1 - u) * (0 / e') = u := by grind

theorem arithJratio (u x e e' : Rat) (hu : u ≠ 0) (he : e ≠ 0) :
    (u * (x / e) + (1 - u) * (0 / e')) / (u * (e / e) + (1 - u) * (0 / e')) = x / e := by grind

theorem arithJratioNot (u x e e' : Rat) (hu : u ≠ 1) (he' : e' ≠ 0) :
    (u * (0 / e) + (1 - u) * (x / e')) / (u * (0 / e) + (1 - u) * (e' / e')) = x / e' := by grind

theorem arithJone (c nc : Rat) : (1 : Rat) * c + (1 - 1) * nc = c := by grind

theorem arithBayes (PS sx snx p np : Rat) (s : PS = sx + snx) (c : p + np = 1)
    (h1 : sx / p = 9/10) (h2 : snx / np = 1/10) (_hp0 : 0 < p) (_hp1 : p < 1) :
    sx / PS = 9 * p / (8 * p + 1) := by grind

theorem arithOnlyAtHalf (p : Rat) (_hp0 : 0 < p) (h : 9 * p / (8 * p + 1) = 9/10) : p = 1/2 := by
  grind

theorem arithSless (u : Rat) (_hu0 : 0 ≤ u) (_hu1 : u ≤ 1) :
    u * (9/10) + (1 - u) * (1/10) < 1 := by grind

theorem arithSunday (u : Rat) : u * (1/2) + (1 - u) * (1/2) = 1/2 := by grind

namespace Measure

/-- `(A or B) and E` is `(A and E) or (B and E)`, and the two are exclusive when `A`, `B` are. -/
theorem or_and_split {A B E : Ω → Prop} (hA : m.ev A) (hB : m.ev B) (hE : m.ev E)
    (h : ∀ ω, ¬ (A ω ∧ B ω)) :
    m.P (fun ω => (A ω ∨ B ω) ∧ E ω) = m.P (fun ω => A ω ∧ E ω) + m.P (fun ω => B ω ∧ E ω) := by
  have a : m.P (fun ω => (A ω ∧ E ω) ∨ (B ω ∧ E ω))
      = m.P (fun ω => A ω ∧ E ω) + m.P (fun ω => B ω ∧ E ω) :=
    m.add (m.ev_and hA hE) (m.ev_and hB hE) (fun ω x => h ω ⟨x.1.1, x.2.1⟩)
  have e : (fun ω => (A ω ∨ B ω) ∧ E ω) = (fun ω => (A ω ∧ E ω) ∨ (B ω ∧ E ω)) := by
    funext ω; apply propext; constructor
    · intro x; cases x.1 with
      | inl y => exact Or.inl ⟨y, x.2⟩
      | inr y => exact Or.inr ⟨y, x.2⟩
    · intro x; cases x with
      | inl y => exact ⟨Or.inl y.1, y.2⟩
      | inr y => exact ⟨Or.inr y.1, y.2⟩
  rw [e]; exact a

/-- **Jeffrey's rule (J)**, as the paper states it: with the probability of `E` changed to `u`,
    `P_j(X) = u P_i(X | E) + (1 - u) P_i(X | ¬E)`. It is a standard measure. -/
def jeffrey (E : Ω → Prop) (hE : m.ev E) (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0)
    (u : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : Measure Ω where
  ev := m.ev
  ev_true := m.ev_true
  ev_not := m.ev_not
  ev_and := m.ev_and
  P := fun A => u * m.cond A E + (1 - u) * m.cond A (fun ω => ¬ E ω)
  nonneg := by
    intro A hA
    have pE := m.nonneg hE
    have pnE := m.nonneg (m.ev_not hE)
    have x1 := m.nonneg (m.ev_and hA hE)
    have x2 := m.nonneg (m.ev_and hA (m.ev_not hE))
    have c1 : (0 : Rat) ≤ m.cond A E := arithDivNonneg _ _ x1 (by grind)
    have c2 : (0 : Rat) ≤ m.cond A (fun ω => ¬ E ω) := arithDivNonneg _ _ x2 (by grind)
    have t1 : (0 : Rat) ≤ u * m.cond A E := Rat.mul_nonneg hu0 c1
    have t2 : (0 : Rat) ≤ (1 - u) * m.cond A (fun ω => ¬ E ω) := Rat.mul_nonneg (by grind) c2
    grind
  total := by
    have e1 : (fun ω => True ∧ E ω) = E := by funext ω; simp
    have e2 : (fun ω => True ∧ ¬ E ω) = (fun ω => ¬ E ω) := by funext ω; simp
    show u * (m.P (fun ω => True ∧ E ω) / m.P E)
        + (1 - u) * (m.P (fun ω => True ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)) = 1
    rw [e1, e2]; exact arithJtotal u _ _ hE0 hE1
  add := by
    intro A B hA hB h
    have s1 := m.or_and_split hA hB hE h
    have s2 := m.or_and_split hA hB (m.ev_not hE) h
    show u * (m.P (fun ω => (A ω ∨ B ω) ∧ E ω) / m.P E)
          + (1 - u) * (m.P (fun ω => (A ω ∨ B ω) ∧ ¬ E ω) / m.P (fun ω => ¬ E ω))
        = (u * (m.P (fun ω => A ω ∧ E ω) / m.P E)
            + (1 - u) * (m.P (fun ω => A ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
          + (u * (m.P (fun ω => B ω ∧ E ω) / m.P E)
            + (1 - u) * (m.P (fun ω => B ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
    rw [s1, s2]; exact arithJadd _ _ _ _ _ _ _

variable {E : Ω → Prop} (hE : m.ev E) (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0)
  (u : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)

/-- (J) gives `E` the value `u`. -/
theorem jeffrey_E : (m.jeffrey E hE hE0 hE1 u hu0 hu1).P E = u := by
  have e1 : (fun ω => E ω ∧ E ω) = E := by funext ω; simp
  have e2 : (fun ω => E ω ∧ ¬ E ω) = (fun (_ : Ω) => False) := by funext ω; simp
  show u * (m.P (fun ω => E ω ∧ E ω) / m.P E)
      + (1 - u) * (m.P (fun ω => E ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)) = u
  rw [e1, e2, m.P_false]; exact arithJu u _ _ hE0

/-- (J) keeps the ratio inside `E` (the paper: "in the schema the values of the ratios in each
    of the cells are kept constant"), when `u` is not 0. -/
theorem jeffrey_keeps_ratio (X : Ω → Prop) (hu : u ≠ 0) :
    (m.jeffrey E hE hE0 hE1 u hu0 hu1).cond X E = m.cond X E := by
  have e1 : (fun ω => (X ω ∧ E ω) ∧ E ω) = (fun ω => X ω ∧ E ω) := by
    funext ω; apply propext; exact ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩
  have e2 : (fun ω => (X ω ∧ E ω) ∧ ¬ E ω) = (fun (_ : Ω) => False) := by
    funext ω; apply propext; exact ⟨fun h => h.2 h.1.2, fun h => h.elim⟩
  have e3 : (fun ω => E ω ∧ E ω) = E := by funext ω; simp
  have e4 : (fun ω => E ω ∧ ¬ E ω) = (fun (_ : Ω) => False) := by funext ω; simp
  show (u * (m.P (fun ω => (X ω ∧ E ω) ∧ E ω) / m.P E)
        + (1 - u) * (m.P (fun ω => (X ω ∧ E ω) ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
      / (u * (m.P (fun ω => E ω ∧ E ω) / m.P E)
        + (1 - u) * (m.P (fun ω => E ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
      = m.P (fun ω => X ω ∧ E ω) / m.P E
  rw [e1, e2, e3, e4, m.P_false]; exact arithJratio u _ _ _ hu hE0

/-- (J) keeps the ratio inside `¬E` as well, when `u` is not 1. With `jeffrey_keeps_ratio` this
    is the paper's "the values of the ratios in each of the cells are kept constant". -/
theorem jeffrey_keeps_ratio_not (X : Ω → Prop) (hu : u ≠ 1) :
    (m.jeffrey E hE hE0 hE1 u hu0 hu1).cond X (fun ω => ¬ E ω) = m.cond X (fun ω => ¬ E ω) := by
  have e1 : (fun ω => (X ω ∧ ¬ E ω) ∧ E ω) = (fun (_ : Ω) => False) := by
    funext ω; apply propext; exact ⟨fun h => h.1.2 h.2, fun h => h.elim⟩
  have e2 : (fun ω => (X ω ∧ ¬ E ω) ∧ ¬ E ω) = (fun ω => X ω ∧ ¬ E ω) := by
    funext ω; apply propext; exact ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩
  have e3 : (fun ω => ¬ E ω ∧ E ω) = (fun (_ : Ω) => False) := by
    funext ω; apply propext; exact ⟨fun h => h.1 h.2, fun h => h.elim⟩
  have e4 : (fun ω => ¬ E ω ∧ ¬ E ω) = (fun ω => ¬ E ω) := by funext ω; simp
  show (u * (m.P (fun ω => (X ω ∧ ¬ E ω) ∧ E ω) / m.P E)
        + (1 - u) * (m.P (fun ω => (X ω ∧ ¬ E ω) ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
      / (u * (m.P (fun ω => ¬ E ω ∧ E ω) / m.P E)
        + (1 - u) * (m.P (fun ω => ¬ E ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)))
      = m.P (fun ω => X ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)
  rw [e1, e2, e3, e4, m.P_false]; exact arithJratioNot u _ _ _ hu hE1

/-- (J) at `u = 1` gives every event its conditional value given `E`. (The paper: "when `u = 1`
    ... we have (B)".) -/
theorem jeffrey_at_one (X : Ω → Prop) :
    (m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).P X = m.cond X E := by
  show (1 : Rat) * m.cond X E + (1 - 1) * m.cond X (fun ω => ¬ E ω) = m.cond X E
  exact arithJone _ _

end Measure

/-! ### The conflict (the paragraph "For suppose her reliability is exactly 0.9 ...") -/

/-- With `P_i(S | x) = 9/10`, `P_i(S | ¬x) = 1/10` and `P_i(x) = p`:
    `P_i(x | S) = 9p / (8p + 1)`. -/
theorem bayes_value (x S : Ω → Prop) (hx : m.ev x) (hS : m.ev S)
    (p : Rat) (hp : m.P x = p) (hp0 : 0 < p) (hp1 : p < 1)
    (rel1 : m.cond S x = 9/10) (rel2 : m.cond S (fun ω => ¬ x ω) = 1/10) :
    m.cond x S = 9 * p / (8 * p + 1) := by
  have s := m.split hS hx
  have c := m.compl hx
  have e : (fun ω => x ω ∧ S ω) = (fun ω => S ω ∧ x ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  unfold Measure.cond at *
  rw [e]
  rw [hp] at rel1 c
  exact arithBayes _ _ _ p _ s c rel1 rel2 hp0 hp1

/-- **The proved value.** In any measure in which her saying it is certain and `x` has given `S`
    the ratio it has by the definitions, `x` has `9p / (8p + 1)`. -/
theorem value_with_S_certain (x S : Ω → Prop) (hx : m.ev x) (hS : m.ev S)
    (p : Rat) (hp : m.P x = p) (hp0 : 0 < p) (hp1 : p < 1)
    (rel1 : m.cond S x = 9/10) (rel2 : m.cond S (fun ω => ¬ x ω) = 1/10)
    (later : Measure Ω) (hx' : later.ev x) (hS' : later.ev S)
    (S_certain : later.P S = 1) (same : later.cond x S = m.cond x S) :
    later.P x = 9 * p / (8 * p + 1) :=
  later.certain_gives_ratio hx' hS' S_certain
    (same.trans (bayes_value m x S hx hS p hp hp0 hp1 rel1 rel2))

/-- **(J)'s value.** With `x` for its `E` and `u = 9/10`, (J) gives `x` the value `9/10`,
    whatever `p` is. -/
theorem jeffrey_value (x : Ω → Prop) (hx : m.ev x)
    (h0 : m.P x ≠ 0) (h1 : m.P (fun ω => ¬ x ω) ≠ 0) :
    (m.jeffrey x hx h0 h1 (9/10) (by grind) (by grind)).P x = 9/10 :=
  m.jeffrey_E hx h0 h1 (9/10) (by grind) (by grind)

/-- **The two values differ unless `p = 1/2`.** -/
theorem jeffrey_differs (x S : Ω → Prop) (hx : m.ev x) (hS : m.ev S)
    (p : Rat) (hp : m.P x = p) (hp0 : 0 < p) (hp1 : p < 1)
    (rel1 : m.cond S x = 9/10) (rel2 : m.cond S (fun ω => ¬ x ω) = 1/10)
    (h0 : m.P x ≠ 0) (h1 : m.P (fun ω => ¬ x ω) ≠ 0) (hne : p ≠ 1/2) :
    (m.jeffrey x hx h0 h1 (9/10) (by grind) (by grind)).P x ≠ m.cond x S := by
  rw [jeffrey_value m x hx h0 h1, bayes_value m x S hx hS p hp hp0 hp1 rel1 rel2]
  intro h
  exact hne (arithOnlyAtHalf p hp0 h.symm)

/-- **Whatever value (J) is given for `x`, it gives her saying it less than 1.**
    (The paper: "it gives her saying it, which is certain, less than 1".) -/
theorem jeffrey_leaves_S_short (x S : Ω → Prop) (hx : m.ev x)
    (rel1 : m.cond S x = 9/10) (rel2 : m.cond S (fun ω => ¬ x ω) = 1/10)
    (h0 : m.P x ≠ 0) (h1 : m.P (fun ω => ¬ x ω) ≠ 0)
    (u : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (m.jeffrey x hx h0 h1 u hu0 hu1).P S < 1 := by
  show u * m.cond S x + (1 - u) * m.cond S (fun ω => ¬ x ω) < 1
  rw [rel1, rel2]; exact arithSless u hu0 hu1

/-! The values the paper lists for `9p / (8p + 1)`. -/
example : 9 * (1/10 : Rat) / (8 * (1/10) + 1) = 1/2 := by grind
example : 9 * (1/4 : Rat) / (8 * (1/4) + 1) = 3/4 := by grind
example : 9 * (1/2 : Rat) / (8 * (1/2) + 1) = 9/10 := by grind
example : 9 * (3/4 : Rat) / (8 * (3/4) + 1) = 27/28 := by grind
example : 9 * (9/10 : Rat) / (8 * (9/10) + 1) = 81/82 := by grind

/-! ### The rule run from Sunday (the paragraph "Let Pr_A(R) = u in general ...") -/

/-- On Sunday the coin is independent of `R`: `Pr(H | R) = Pr(H | ¬R) = 1/2`. Then (J) on `R`
    gives heads `1/2` whatever `u` is, and keeps `1/2` for heads given `R`. -/
theorem jeffrey_from_sunday (H R : Ω → Prop) (hR : m.ev R)
    (h0 : m.P R ≠ 0) (h1 : m.P (fun ω => ¬ R ω) ≠ 0)
    (iR : m.cond H R = 1/2) (inR : m.cond H (fun ω => ¬ R ω) = 1/2)
    (u : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (m.jeffrey R hR h0 h1 u hu0 hu1).P H = 1/2 ∧
    (u ≠ 0 → (m.jeffrey R hR h0 h1 u hu0 hu1).cond H R = 1/2) := by
  constructor
  · show u * m.cond H R + (1 - u) * m.cond H (fun ω => ¬ R ω) = 1/2
    rw [iR, inR]; exact arithSunday u
  · intro hu
    rw [m.jeffrey_keeps_ratio hR h0 h1 u hu0 hu1 H hu]; exact iR

/-- **No measure has both.** A measure in which the two cells make up `R` and heads has `1/3`
    in each (the proof under `R`) has heads at `1/3` given `R`; so it does not have the `1/2`
    that the rule run from Sunday gives heads given `R`. -/
theorem not_both (Q : Measure Ω) (H R a1 a2 : Ω → Prop) (hH : Q.ev H)
    (ha1 : Q.ev a1) (ha2 : Q.ev a2)
    (cells : ∀ ω, R ω ↔ (a1 ω ∨ a2 ω)) (excl : ∀ ω, ¬ (a1 ω ∧ a2 ω))
    (pos1 : Q.P a1 ≠ 0) (pos2 : Q.P a2 ≠ 0)
    (r1 : Q.cond H a1 = 1/3) (r2 : Q.cond H a2 = 1/3) : Q.cond H R ≠ 1/2 := by
  rw [Q.sure_thing_within hH ha1 ha2 cells excl pos1 pos2 r1 r2]
  grind

/-! ### The conditions of (S3) can be met, and (B) with the definitions as one object -/

/-- **The conditions of (S3) can be met**, for any measure and any `E` with `π(E)` and `π(¬E)`
    not zero: the measure conditioned on `E` (the rule (J) at `u = 1`), subdivided, is a later
    measure in which `E` is certain, both cells of `E` have positive value, and each cell gives
    `X` the ratio it has in the first measure's subdivision. -/
theorem conditionalization_has_a_model (X E : Ω → Prop) (hE : m.ev E)
    (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0) (s : Rat) (hs0 : 0 < s) (hs1 : s < 1) :
    ((m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide s hs0 hs1).P (lift E) = 1 ∧
    ((m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide s hs0 hs1).P
      (fun p => lift E p ∧ Z p) ≠ 0 ∧
    ((m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide s hs0 hs1).P
      (fun p => lift E p ∧ ¬ Z p) ≠ 0 ∧
    ((m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide s hs0 hs1).cond (lift X)
        (fun p => lift E p ∧ Z p)
      = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ Z p) ∧
    ((m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide s hs0 hs1).cond (lift X)
        (fun p => lift E p ∧ ¬ Z p)
      = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ ¬ Z p) := by
  have k := m.jeffrey_keeps_ratio hE hE0 hE1 1 (by grind) (by grind) X (by grind)
  have eE := m.jeffrey_E hE hE0 hE1 1 (by grind) (by grind)
  obtain ⟨a1, a2⟩ := (m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivision_lemma s hs0 hs1
    X E (by rw [eE]; grind)
  obtain ⟨b1, b2⟩ := m.subdivision_lemma s hs0 hs1 X E hE0
  obtain ⟨c1, c2⟩ := (m.jeffrey E hE hE0 hE1 1 (by grind) (by grind)).subdivide_cells s hs0 hs1 E
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.subdivide_keeps]; exact eE
  · rw [c1, eE]; grind
  · rw [c2, eE]; grind
  · rw [a1, b1]; exact k
  · rw [a2, b2]; exact k

/-- What is defined before any measure is chosen: two events, and the ratio that the definitions
    give the first on the second. -/
structure Definitions (Ω : Type) where
  X : Ω → Prop
  E : Ω → Prop
  c : Rat

/-- A standard measure of those definitions: wherever `E` has positive value, `X` has, given
    `E`, the defined ratio. (This writes into the type what the paper says of a ratio: that it is
    fixed by the definitions of its events and not by the measure.) -/
structure MeasureOf {Ω : Type} (D : Definitions Ω) extends Measure Ω where
  evX : ev D.X
  evE : ev D.E
  ratio : P D.E ≠ 0 → P (fun ω => D.X ω ∧ D.E ω) / P D.E = D.c

/-- **(B) with the definitions as one object.** Any measure of the definitions `D` in which `E`
    is certain gives `X` the defined ratio. An earlier and a later measure "with the same
    definitions" are two measures of one `D`; nothing else ties them. -/
theorem bayes_of_definitions {Ω : Type} (D : Definitions Ω) (later : MeasureOf D)
    (E_certain : later.P D.E = 1) : later.P D.X = D.c :=
  later.toMeasure.certain_gives_ratio later.evX later.evE E_certain
    (later.ratio (by rw [E_certain]; grind))

end Jeffrey

/-! ## The model in sets (Appendix B of the paper): every condition of the proof can be met

The theorem above would say nothing if no measure met its conditions. Here are the two measures
of the paper's Appendix B, the recording's on the four outcomes and yours on the six points, and
the check that they meet every condition, at every `q` strictly between 0 and 1. -/

section Model

open Classical in
/-- 1 if the statement is true, 0 if not. -/
noncomputable def ind (p : Prop) : Rat := if p then 1 else 0

theorem ind_true : ind True = 1 := by simp [ind]
theorem ind_false : ind False = 0 := by simp [ind]
theorem ind_cases (p : Prop) : ind p = 0 ∨ ind p = 1 := by
  unfold ind; split <;> simp
set_option linter.deprecated false in
theorem ind_or {p q : Prop} (h : ¬ (p ∧ q)) : ind (p ∨ q) = ind p + ind q := by
  unfold ind
  cases Classical.em p with
  | inl hp =>
    have hq : ¬ q := fun hq => h ⟨hp, hq⟩
    rw [if_pos (Or.inl hp), if_pos hp, if_neg hq]; grind
  | inr hp =>
    cases Classical.em q with
    | inl hq => rw [if_pos (Or.inr hq), if_neg hp, if_pos hq]; grind
    | inr hq => rw [if_neg (fun x => x.elim hp hq), if_neg hp, if_neg hq]; grind

/-- A weight that is not negative, times 0 or 1, is not negative. -/
theorem wind_nonneg (w : Rat) (hw : 0 ≤ w) (p : Prop) : 0 ≤ w * ind p := by
  rcases ind_cases p with h | h <;> rw [h] <;> grind

/-- The four outcomes: heads and a Monday ball, heads and a Tuesday ball,
    tails and a Monday ball, tails and a Tuesday ball. -/
inductive Outcome | R1 | R2 | R3 | R4

/-- The recording's measure on the four outcomes: a quarter each (B3). -/
noncomputable def PrModel : Measure Outcome where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 1/4 * ind (E .R1) + 1/4 * ind (E .R2) + 1/4 * ind (E .R3) + 1/4 * ind (E .R4)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (1/4) (by grind) (A .R1); have h2 := wind_nonneg (1/4) (by grind) (A .R2)
    have h3 := wind_nonneg (1/4) (by grind) (A .R3); have h4 := wind_nonneg (1/4) (by grind) (A .R4)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1); have h2 := ind_or (h .R2)
    have h3 := ind_or (h .R3); have h4 := ind_or (h .R4)
    simp only [h1, h2, h3, h4]; grind

/-- Heads, and a Monday ball, as sets of outcomes. -/
def Hout : Outcome → Prop | .R1 => True | .R2 => True | .R3 => False | .R4 => False
def Cout : Outcome → Prop | .R1 => True | .R2 => False | .R3 => True | .R4 => False

/-- The six points (B1): an outcome together with a day on which it has a waking. -/
inductive Point | R1M | R2T | R3M | R3T | R4M | R4T

/-- The sets of (B2). -/
def Hpt : Point → Prop | .R1M => True | .R2T => True | _ => False
def apt : Point → Prop | .R1M => True | .R3M => True | .R4M => True | _ => False
def bpt : Point → Prop | .R2T => True | .R3T => True | .R4T => True | _ => False

/-- Your measure on the six points (B3): `q/3` on each Monday point, `(1-q)/3` on each Tuesday point. -/
noncomputable def piModel (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) : Measure Point where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => q/3 * ind (E .R1M) + (1-q)/3 * ind (E .R2T) + q/3 * ind (E .R3M)
        + (1-q)/3 * ind (E .R3T) + q/3 * ind (E .R4M) + (1-q)/3 * ind (E .R4T)
  nonneg := by
    intro A _
    have wq : (0 : Rat) ≤ q/3 := by grind
    have wq' : (0 : Rat) ≤ (1-q)/3 := by grind
    have h1 := wind_nonneg (q/3) wq (A .R1M); have h2 := wind_nonneg ((1-q)/3) wq' (A .R2T)
    have h3 := wind_nonneg (q/3) wq (A .R3M); have h4 := wind_nonneg ((1-q)/3) wq' (A .R3T)
    have h5 := wind_nonneg (q/3) wq (A .R4M); have h6 := wind_nonneg ((1-q)/3) wq' (A .R4T)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1M); have h2 := ind_or (h .R2T); have h3 := ind_or (h .R3M)
    have h4 := ind_or (h .R3T); have h5 := ind_or (h .R4M); have h6 := ind_or (h .R4T)
    simp only [h1, h2, h3, h4, h5, h6]; grind

/-- The recording's measure has the values of the first assumption. -/
theorem PrModel_values :
    PrModel.P Hout = 1/2 ∧ PrModel.P Cout = 1/2 ∧ PrModel.cond Hout Cout = PrModel.P Hout := by
  simp only [PrModel, Measure.cond, Hout, Cout, ind_true, ind_false, and_self, and_true, and_false]
  grind

variable (q : Rat) (hq0 : 0 < q) (hq1 : q < 1)

/-- (B4) at heads and (B2): in your measure on the six points, `π(H | a) = π(H | b) = 1/3`,
    `a` and `b` have positive value, `π(a ∧ b) = 0` and `π(a ∨ b) = 1`. -/
theorem piModel_values :
    (piModel q hq0 hq1).P apt = q ∧ (piModel q hq0 hq1).P bpt = 1 - q ∧
    (piModel q hq0 hq1).cond Hpt apt = 1/3 ∧ (piModel q hq0 hq1).cond Hpt bpt = 1/3 ∧
    (piModel q hq0 hq1).P (fun ω => apt ω ∧ bpt ω) = 0 ∧
    (piModel q hq0 hq1).P (fun ω => apt ω ∨ bpt ω) = 1 := by
  simp only [piModel, Measure.cond, Hpt, apt, bpt, ind_true, ind_false, and_self, and_true,
    and_false, or_true, or_false]
  grind

/-- (B5): the proof applies to the model, and heads has 1/3 in it at every `q`. -/
theorem model_third : (piModel q hq0 hq1).P Hpt = 1/3 := by
  obtain ⟨coin, ball, indep⟩ := PrModel_values
  obtain ⟨pa, pb, ca, cb, four_and, four_or⟩ := piModel_values q hq0 hq1
  obtain ⟨m2, t2⟩ := step2 PrModel Hout Cout trivial trivial coin ball indep
  exact your_proof PrModel Hout Cout trivial trivial coin ball indep
    (piModel q hq0 hq1) Hpt apt bpt trivial trivial trivial
    (by rw [pa]; grind) (by rw [pb]; grind) (ca.trans m2.symm) (cb.trans t2.symm) four_and four_or

/-- The same value read off the six points directly: `q/3 + (1-q)/3 = 1/3`. -/
theorem model_third_direct : (piModel q hq0 hq1).P Hpt = 1/3 := by
  simp only [piModel, Hpt, ind_true, ind_false]
  grind

/-! ### A case that meets the conditions of the conflict with Jeffrey's rule

Four points: `x` and she says it, `x` and she does not, not-`x` and she says it, not-`x` and she
does not, with `9p/10`, `p/10`, `(1-p)/10`, `9(1-p)/10`. Then `P(x) = p`, `P(S | x) = 9/10` and
`P(S | ¬x) = 1/10`, at every `p` strictly between 0 and 1. -/

inductive APoint | xS | xN | nS | nN

def xA : APoint → Prop | .xS => True | .xN => True | _ => False
def SA : APoint → Prop | .xS => True | .nS => True | _ => False

noncomputable def aminaModel (p : Rat) (hp0 : 0 < p) (hp1 : p < 1) : Measure APoint where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 9*p/10 * ind (E .xS) + p/10 * ind (E .xN) + (1-p)/10 * ind (E .nS)
        + 9*(1-p)/10 * ind (E .nN)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (9*p/10) (by grind) (A .xS)
    have h2 := wind_nonneg (p/10) (by grind) (A .xN)
    have h3 := wind_nonneg ((1-p)/10) (by grind) (A .nS)
    have h4 := wind_nonneg (9*(1-p)/10) (by grind) (A .nN)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .xS); have h2 := ind_or (h .xN)
    have h3 := ind_or (h .nS); have h4 := ind_or (h .nN)
    simp only [h1, h2, h3, h4]; grind

theorem aminaModel_values (p : Rat) (hp0 : 0 < p) (hp1 : p < 1) :
    (aminaModel p hp0 hp1).P xA = p ∧
    (aminaModel p hp0 hp1).cond SA xA = 9/10 ∧
    (aminaModel p hp0 hp1).cond SA (fun ω => ¬ xA ω) = 1/10 := by
  simp only [aminaModel, Measure.cond, xA, SA, ind_true, ind_false, and_self, and_true, and_false,
    not_true_eq_false, not_false_eq_true]
  grind

/-- In this case, at any `p` other than `1/2`, (J)'s value for `x` and `P(x | S)` differ. -/
theorem aminaModel_conflict (p : Rat) (hp0 : 0 < p) (hp1 : p < 1) (hne : p ≠ 1/2)
    (h0 : (aminaModel p hp0 hp1).P xA ≠ 0)
    (h1 : (aminaModel p hp0 hp1).P (fun ω => ¬ xA ω) ≠ 0) :
    ((aminaModel p hp0 hp1).jeffrey xA trivial h0 h1 (9/10) (by grind) (by grind)).P xA
      ≠ (aminaModel p hp0 hp1).cond xA SA := by
  obtain ⟨v, r1, r2⟩ := aminaModel_values p hp0 hp1
  exact jeffrey_differs (aminaModel p hp0 hp1) xA SA trivial trivial p v hp0 hp1 r1 r2 h0 h1 hne

/-- A Monday ball, as a set of points (B2). -/
def Cpt : Point → Prop | .R1M => True | .R3M => True | .R3T => True | _ => False

/-- **(B4) in full**: in the model the construction holds at each of the four outcomes, in both
    cells, at every `q` strictly between 0 and 1. -/
theorem model_construction_all :
    (piModel q hq0 hq1).cond (fun ω => Hpt ω ∧ Cpt ω) apt
      = PrModel.cond (fun ω => Hout ω ∧ Cout ω) (M Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => Hpt ω ∧ ¬ Cpt ω) apt
      = PrModel.cond (fun ω => Hout ω ∧ ¬ Cout ω) (M Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => ¬ Hpt ω ∧ Cpt ω) apt
      = PrModel.cond (fun ω => ¬ Hout ω ∧ Cout ω) (M Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => ¬ Hpt ω ∧ ¬ Cpt ω) apt
      = PrModel.cond (fun ω => ¬ Hout ω ∧ ¬ Cout ω) (M Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => Hpt ω ∧ Cpt ω) bpt
      = PrModel.cond (fun ω => Hout ω ∧ Cout ω) (T Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => Hpt ω ∧ ¬ Cpt ω) bpt
      = PrModel.cond (fun ω => Hout ω ∧ ¬ Cout ω) (T Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => ¬ Hpt ω ∧ Cpt ω) bpt
      = PrModel.cond (fun ω => ¬ Hout ω ∧ Cout ω) (T Hout Cout) ∧
    (piModel q hq0 hq1).cond (fun ω => ¬ Hpt ω ∧ ¬ Cpt ω) bpt
      = PrModel.cond (fun ω => ¬ Hout ω ∧ ¬ Cout ω) (T Hout Cout) := by
  simp only [piModel, PrModel, Measure.cond, Hpt, Cpt, apt, bpt, Hout, Cout, M, T,
    ind_true, ind_false, and_self, and_true, and_false, or_true, or_false,
    not_true_eq_false, not_false_eq_true]
  grind

end Model

end YourProof

-- What the theorems rest on (Lean prints every axiom used):
#print axioms YourProof.Measure.sure_thing
#print axioms YourProof.your_proof
#print axioms YourProof.model_third
#print axioms YourProof.Measure.subdivision_lemma
#print axioms YourProof.Measure.conditionalization
#print axioms YourProof.jeffrey_differs
#print axioms YourProof.jeffrey_leaves_S_short
#print axioms YourProof.not_both
#print axioms YourProof.aminaModel_conflict
#print axioms YourProof.no_other_value
#print axioms YourProof.Measure.jeffrey_keeps_ratio_not
#print axioms YourProof.conditionalization_has_a_model
#print axioms YourProof.bayes_of_definitions
#print axioms YourProof.model_construction_all
