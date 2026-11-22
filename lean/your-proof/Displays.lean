/-
  The remaining numbered displays of the paper (NEC11_c1957_21nov.tex), each with the
  justification the paper gives after it. Checked by Lean 4.36.0 with nothing beyond Lean's own
  library. Standalone: the `Measure` structure and the lemmas it needs are copied from
  YourProof.lean.

  The letters are the paper's: `π` is your measure, and `Pr` is the recording's. In the quoted
  LaTeX, `\prsb` prints as π and `\prany` prints as Pr. The measure of display (17) is called κ,
  as in the paper since 22 Nov (it was ν in the snapshot named above).

  How to read this file against the paper: each display theorem carries, in its comment, the
  display's number, its source line(s), the display copied from the source, and any choice made
  in stating it. What Lean certifies is that each statement follows from the hypotheses written
  in front of it. That a statement says what the paper's display says is checked by reading the
  two side by side.

  Two linters are switched off below: hypotheses the paper states are kept in a theorem even
  where its proof does not use them (for example `0 < c < 1` where the proof needs only `0 < c`).

  A recurring choice: two cells `a`, `b` are taken as exclusive and exhaustive as sets
  (`∀ ω, ¬ (a ω ∧ b ω)` and `∀ ω, a ω ∨ b ω`), as in Appendix B (`ea ∩ eb = ∅`,
  `ea ∪ eb = S`); this gives (4), `π(a ∧ b) = 0`, `π(a ∨ b) = 1`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Displays

theorem pos_div (x y : Rat) (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  have h := Rat.mul_pos hx (Rat.inv_pos.mpr hy)
  rw [Rat.div_def]; exact h

/-! ## Arithmetic, as statements about rational numbers alone -/

theorem arithCells (PX xa xna y z xb w pa pb pab pbna por pnor r : Rat)
    (s1 : PX = xa + xna) (s2 : xna = y + z) (s3 : xb = w + y) (s4 : por = pa + pbna)
    (s5 : pb = pab + pbna) (n1 : w ≤ pab) (p1 : 0 ≤ w) (s6 : por + pnor = 1)
    (n2 : z ≤ pnor) (p2 : 0 ≤ z) (a_pos : pa ≠ 0) (b_pos : pb ≠ 0)
    (ra : xa / pa = r) (rb : xb / pb = r)
    (h_and : pab = 0) (h_or : por = 1) : PX = r := by grind

theorem arithST (PX x1 x2 b b' : Rat) (s : PX = x1 + x2) (c : b + b' = 1)
    (hb : b ≠ 0) (hb' : b' ≠ 0) (h : x1 / b = x2 / b') : PX = x1 / b := by grind

theorem arith4 (PY yh yn b1 b2 b3 b4 a1 a2 a3 a4 : Rat) (s1 : PY = yh + yn) (s2 : yh = b1 + b2)
    (s3 : yn = b3 + b4) (e1 : b1 = a1) (e2 : b2 = a2) (e3 : b3 = a3) (e4 : b4 = a4) :
    PY = a1 + a2 + a3 + a4 := by grind

theorem arithDecomp (PX xa xb a1 a2 a3 a4 b1 b2 b3 b4 : Rat) (s : PX = xa + xb)
    (sa : xa = a1 + a2 + a3 + a4) (sb : xb = b1 + b2 + b3 + b4) :
    PX = a1 + a2 + a3 + a4 + b1 + b2 + b3 + b4 := by grind

theorem arithMul (pxb pL pb q v : Rat) (hB : pb = q) (hq : q ≠ 0) (e : pxb = pL)
    (h : pxb / pb = v) : pL = q * v := by grind

theorem lt_le (x y : Rat) (h : x < y) : x ≤ y := by grind

/-- A standard (finitely additive) probability measure on an algebra of events
    (copied from YourProof.lean). -/
structure Measure (Ω : Type) where
  ev : (Ω → Prop) → Prop
  ev_true : ev (fun _ => True)
  ev_not : ∀ {A : Ω → Prop}, ev A → ev (fun ω => ¬ A ω)
  ev_and : ∀ {A B : Ω → Prop}, ev A → ev B → ev (fun ω => A ω ∧ B ω)
  P : (Ω → Prop) → Rat
  nonneg : ∀ {A : Ω → Prop}, ev A → 0 ≤ P A
  total : P (fun _ => True) = 1
  add : ∀ {A B : Ω → Prop}, ev A → ev B → (∀ ω, ¬ (A ω ∧ B ω)) →
    P (fun ω => A ω ∨ B ω) = P A + P B

namespace Measure

variable {Ω : Type} (m : Measure Ω)

/-- The conditional probability: the ratio of two values of the measure. -/
def cond (X B : Ω → Prop) : Rat := m.P (fun ω => X ω ∧ B ω) / m.P B

theorem Pcongr {A B : Ω → Prop} (h : ∀ ω, A ω ↔ B ω) : m.P A = m.P B := by
  have e : A = B := funext fun ω => propext (h ω)
  rw [e]

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

theorem compl {B : Ω → Prop} (hB : m.ev B) : m.P B + m.P (fun ω => ¬ B ω) = 1 := by
  have h := m.split m.ev_true hB
  have e1 : (fun ω => True ∧ B ω) = B := by funext ω; simp
  have e2 : (fun ω => True ∧ ¬ B ω) = (fun ω => ¬ B ω) := by funext ω; simp
  rw [e1, e2, m.total] at h; exact h.symm

theorem mono {A B : Ω → Prop} (hA : m.ev A) (hB : m.ev B) (h : ∀ ω, A ω → B ω) :
    m.P A ≤ m.P B := by
  have s := m.split hB hA
  have e : (fun ω => B ω ∧ A ω) = A := by
    funext ω; apply propext; exact ⟨fun h => h.2, fun a => ⟨h ω a, a⟩⟩
  rw [e] at s
  have n := m.nonneg (m.ev_and hB (m.ev_not hA))
  grind

theorem P_false : m.P (fun _ => False) = 0 := by
  have c := m.compl m.ev_true
  have e : (fun (_ : Ω) => ¬ True) = (fun _ => False) := by funext ω; simp
  rw [e, m.total] at c
  grind

/-- Sure Thing (end of section 1.3), copied from YourProof.lean. -/
theorem sure_thing {X B : Ω → Prop} (hX : m.ev X) (hB : m.ev B)
    (hB0 : m.P B ≠ 0) (hB1 : m.P (fun ω => ¬ B ω) ≠ 0)
    (h : m.cond X B = m.cond X (fun ω => ¬ B ω)) :
    m.P X = m.cond X B := by
  have s := m.split hX hB
  have c := m.compl hB
  unfold cond at *
  exact arithST _ _ _ _ _ s c hB0 hB1 h

/-- Sure Thing over two cells that partition the measure, copied from YourProof.lean. -/
theorem sure_thing_cells {X a b : Ω → Prop} {r : Rat} (hX : m.ev X) (ha : m.ev a) (hb : m.ev b)
    (a_pos : m.P a ≠ 0) (b_pos : m.P b ≠ 0)
    (ra : m.cond X a = r) (rb : m.cond X b = r)
    (h_and : m.P (fun ω => a ω ∧ b ω) = 0) (h_or : m.P (fun ω => a ω ∨ b ω) = 1) :
    m.P X = r := by
  have s1 := m.split hX ha
  have s2 := m.split (m.ev_and hX (m.ev_not ha)) hb
  have s3 := m.split (m.ev_and hX hb) ha
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
  have s5 := m.split hb ha
  have e5 : (fun ω => b ω ∧ a ω) = (fun ω => a ω ∧ b ω) := by
    funext ω; apply propext; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e5] at s5
  have n1 : m.P (fun ω => (X ω ∧ b ω) ∧ a ω) ≤ m.P (fun ω => a ω ∧ b ω) :=
    m.mono (m.ev_and (m.ev_and hX hb) ha) (m.ev_and ha hb) (fun ω h => ⟨h.2, h.1.2⟩)
  have p1 := m.nonneg (m.ev_and (m.ev_and hX hb) ha)
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

/-- Two exclusive and exhaustive sets: the partition (4) follows. -/
theorem part_and {a b : Ω → Prop} (excl : ∀ ω, ¬ (a ω ∧ b ω)) :
    m.P (fun ω => a ω ∧ b ω) = 0 := by
  rw [m.Pcongr (B := fun _ => False) (fun ω => ⟨fun h => excl ω h, fun h => h.elim⟩)]
  exact m.P_false

theorem part_or {a b : Ω → Prop} (exh : ∀ ω, a ω ∨ b ω) : m.P (fun ω => a ω ∨ b ω) = 1 := by
  rw [m.Pcongr (B := fun _ => True) (fun ω => ⟨fun _ => trivial, fun _ => exh ω⟩)]
  exact m.total

theorem part_sum {a b : Ω → Prop} (ha : m.ev a) (hb : m.ev b) (excl : ∀ ω, ¬ (a ω ∧ b ω))
    (exh : ∀ ω, a ω ∨ b ω) : m.P a + m.P b = 1 := by
  have h := m.add ha hb excl
  rw [m.part_or exh] at h; exact h.symm

theorem split_cells {X a b : Ω → Prop} (hX : m.ev X) (ha : m.ev a) (hb : m.ev b)
    (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω) :
    m.P X = m.P (fun ω => X ω ∧ a ω) + m.P (fun ω => X ω ∧ b ω) := by
  have h := m.add (m.ev_and hX ha) (m.ev_and hX hb) (fun ω h => excl ω ⟨h.1.2, h.2.2⟩)
  have e : m.P X = m.P (fun ω => (X ω ∧ a ω) ∨ (X ω ∧ b ω)) :=
    m.Pcongr (fun ω => by have := exh ω; grind)
  exact e.trans h

theorem split4 {Y H C : Ω → Prop} (hY : m.ev Y) (hH : m.ev H) (hC : m.ev C) :
    m.P Y = m.P (fun ω => Y ω ∧ (H ω ∧ C ω)) + m.P (fun ω => Y ω ∧ (H ω ∧ ¬ C ω))
      + m.P (fun ω => Y ω ∧ (¬ H ω ∧ C ω)) + m.P (fun ω => Y ω ∧ (¬ H ω ∧ ¬ C ω)) := by
  have s1 := m.split hY hH
  have s2 := m.split (m.ev_and hY hH) hC
  have s3 := m.split (m.ev_and hY (m.ev_not hH)) hC
  have e1 : m.P (fun ω => (Y ω ∧ H ω) ∧ C ω) = m.P (fun ω => Y ω ∧ (H ω ∧ C ω)) :=
    m.Pcongr (fun ω => by grind)
  have e2 : m.P (fun ω => (Y ω ∧ H ω) ∧ ¬ C ω) = m.P (fun ω => Y ω ∧ (H ω ∧ ¬ C ω)) :=
    m.Pcongr (fun ω => by grind)
  have e3 : m.P (fun ω => (Y ω ∧ ¬ H ω) ∧ C ω) = m.P (fun ω => Y ω ∧ (¬ H ω ∧ C ω)) :=
    m.Pcongr (fun ω => by grind)
  have e4 : m.P (fun ω => (Y ω ∧ ¬ H ω) ∧ ¬ C ω) = m.P (fun ω => Y ω ∧ (¬ H ω ∧ ¬ C ω)) :=
    m.Pcongr (fun ω => by grind)
  exact arith4 _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 e1 e2 e3 e4

theorem inter_line {X L : Ω → Prop} (h : ∀ ω, L ω → X ω) : m.P (fun ω => X ω ∧ L ω) = m.P L :=
  m.Pcongr (fun ω => ⟨fun x => x.2, fun l => ⟨h ω l, l⟩⟩)

theorem inter_zero {X L : Ω → Prop} (h : ∀ ω, L ω → ¬ X ω) : m.P (fun ω => X ω ∧ L ω) = 0 := by
  rw [m.Pcongr (B := fun _ => False) (fun ω => ⟨fun x => h ω x.2 x.1, fun f => f.elim⟩)]
  exact m.P_false

/-- `π(X ∧ B) = π(B) π(X | B)` read backwards: a value from a conditional value. -/
theorem line_from_cond {X B L : Ω → Prop} {q v : Rat} (hB : m.P B = q) (hq : q ≠ 0)
    (h : m.cond X B = v) (e : ∀ ω, (X ω ∧ B ω) ↔ L ω) : m.P L = q * v := by
  have e2 := m.Pcongr e
  unfold cond at h
  exact arithMul _ _ _ _ _ hB hq e2 h

end Measure

/-! ## The recording's events and the lines of a measure partitioned by two cells -/

/-- You are awakened on Monday: heads with a Monday ball, or tails. -/
def M {Ω : Type} (H C : Ω → Prop) : Ω → Prop := fun ω => (H ω ∧ C ω) ∨ ¬ H ω
/-- You are awakened on Tuesday: heads with a Tuesday ball, or tails. -/
def T {Ω : Type} (H C : Ω → Prop) : Ω → Prop := fun ω => (H ω ∧ ¬ C ω) ∨ ¬ H ω
/-- You are awakened on the day the ball marks: a Monday ball and a Monday waking, or a Tuesday
    ball and a Tuesday waking. It takes place on every outcome. -/
def ballDay {Ω : Type} (H C : Ω → Prop) : Ω → Prop :=
  fun ω => (C ω ∧ M H C ω) ∨ (¬ C ω ∧ T H C ω)
/-- You are awakened on the other day. It takes place exactly on tails. -/
def otherDay {Ω : Type} (H C : Ω → Prop) : Ω → Prop :=
  fun ω => (C ω ∧ T H C ω) ∨ (¬ C ω ∧ M H C ω)

/-- The eight conjunctions of a cell with a coin-and-ball outcome (the paper's "lines"). -/
def aHC {Ω : Type} (a H C : Ω → Prop) : Ω → Prop := fun ω => a ω ∧ H ω ∧ C ω
def aHn {Ω : Type} (a H C : Ω → Prop) : Ω → Prop := fun ω => a ω ∧ H ω ∧ ¬ C ω
def anC {Ω : Type} (a H C : Ω → Prop) : Ω → Prop := fun ω => a ω ∧ ¬ H ω ∧ C ω
def ann {Ω : Type} (a H C : Ω → Prop) : Ω → Prop := fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω
def bHC {Ω : Type} (b H C : Ω → Prop) : Ω → Prop := fun ω => b ω ∧ H ω ∧ C ω
def bHn {Ω : Type} (b H C : Ω → Prop) : Ω → Prop := fun ω => b ω ∧ H ω ∧ ¬ C ω
def bnC {Ω : Type} (b H C : Ω → Prop) : Ω → Prop := fun ω => b ω ∧ ¬ H ω ∧ C ω
def bnn {Ω : Type} (b H C : Ω → Prop) : Ω → Prop := fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω

macro "lterm" : tactic => `(tactic| first
  | (apply Measure.inter_line; intro ω;
     simp only [aHC, aHn, anC, ann, bHC, bHn, bnC, bnn, M, T] <;> grind)
  | (apply Measure.inter_zero; intro ω;
     simp only [aHC, aHn, anC, ann, bHC, bHn, bnC, bnn, M, T] <;> grind))

section Lines

variable {Ω : Type} (m : Measure Ω) {a b H C : Ω → Prop}
  (ha : m.ev a) (hb : m.ev b) (hH : m.ev H) (hC : m.ev C)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
include ha hb hH hC excl exh

/-- Every event is the sum of its parts in the eight lines. -/
theorem decomp {X : Ω → Prop} (hX : m.ev X) :
    m.P X = m.P (fun ω => X ω ∧ aHC a H C ω) + m.P (fun ω => X ω ∧ aHn a H C ω)
      + m.P (fun ω => X ω ∧ anC a H C ω) + m.P (fun ω => X ω ∧ ann a H C ω)
      + m.P (fun ω => X ω ∧ bHC b H C ω) + m.P (fun ω => X ω ∧ bHn b H C ω)
      + m.P (fun ω => X ω ∧ bnC b H C ω) + m.P (fun ω => X ω ∧ bnn b H C ω) := by
  have s := m.split_cells hX ha hb excl exh
  have sa := m.split4 (m.ev_and hX ha) hH hC
  have sb := m.split4 (m.ev_and hX hb) hH hC
  have e1 : m.P (fun ω => (X ω ∧ a ω) ∧ (H ω ∧ C ω)) = m.P (fun ω => X ω ∧ aHC a H C ω) :=
    m.Pcongr (fun ω => by simp only [aHC]; grind)
  have e2 : m.P (fun ω => (X ω ∧ a ω) ∧ (H ω ∧ ¬ C ω)) = m.P (fun ω => X ω ∧ aHn a H C ω) :=
    m.Pcongr (fun ω => by simp only [aHn]; grind)
  have e3 : m.P (fun ω => (X ω ∧ a ω) ∧ (¬ H ω ∧ C ω)) = m.P (fun ω => X ω ∧ anC a H C ω) :=
    m.Pcongr (fun ω => by simp only [anC]; grind)
  have e4 : m.P (fun ω => (X ω ∧ a ω) ∧ (¬ H ω ∧ ¬ C ω)) = m.P (fun ω => X ω ∧ ann a H C ω) :=
    m.Pcongr (fun ω => by simp only [ann]; grind)
  have f1 : m.P (fun ω => (X ω ∧ b ω) ∧ (H ω ∧ C ω)) = m.P (fun ω => X ω ∧ bHC b H C ω) :=
    m.Pcongr (fun ω => by simp only [bHC]; grind)
  have f2 : m.P (fun ω => (X ω ∧ b ω) ∧ (H ω ∧ ¬ C ω)) = m.P (fun ω => X ω ∧ bHn b H C ω) :=
    m.Pcongr (fun ω => by simp only [bHn]; grind)
  have f3 : m.P (fun ω => (X ω ∧ b ω) ∧ (¬ H ω ∧ C ω)) = m.P (fun ω => X ω ∧ bnC b H C ω) :=
    m.Pcongr (fun ω => by simp only [bnC]; grind)
  have f4 : m.P (fun ω => (X ω ∧ b ω) ∧ (¬ H ω ∧ ¬ C ω)) = m.P (fun ω => X ω ∧ bnn b H C ω) :=
    m.Pcongr (fun ω => by simp only [bnn]; grind)
  rw [e1, e2, e3, e4] at sa
  rw [f1, f2, f3, f4] at sb
  exact arithDecomp _ _ _ _ _ _ _ _ _ _ _ s sa sb

theorem decomp_eval {X : Ω → Prop} (hX : m.ev X) {v1 v2 v3 v4 v5 v6 v7 v8 : Rat}
    (h1 : m.P (fun ω => X ω ∧ aHC a H C ω) = v1) (h2 : m.P (fun ω => X ω ∧ aHn a H C ω) = v2)
    (h3 : m.P (fun ω => X ω ∧ anC a H C ω) = v3) (h4 : m.P (fun ω => X ω ∧ ann a H C ω) = v4)
    (h5 : m.P (fun ω => X ω ∧ bHC b H C ω) = v5) (h6 : m.P (fun ω => X ω ∧ bHn b H C ω) = v6)
    (h7 : m.P (fun ω => X ω ∧ bnC b H C ω) = v7) (h8 : m.P (fun ω => X ω ∧ bnn b H C ω) = v8) :
    m.P X = v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 := by
  rw [decomp m ha hb hH hC excl exh hX, h1, h2, h3, h4, h5, h6, h7, h8]

theorem P_true : m.P (fun _ => True) = m.P (aHC a H C) + m.P (aHn a H C) + m.P (anC a H C)
    + m.P (ann a H C) + m.P (bHC b H C) + m.P (bHn b H C) + m.P (bnC b H C) + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh m.ev_true (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_H : m.P H = m.P (aHC a H C) + m.P (aHn a H C) + 0 + 0
    + m.P (bHC b H C) + m.P (bHn b H C) + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh hH (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_C : m.P C = m.P (aHC a H C) + 0 + m.P (anC a H C) + 0
    + m.P (bHC b H C) + 0 + m.P (bnC b H C) + 0 :=
  decomp_eval m ha hb hH hC excl exh hC (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_nC : m.P (fun ω => ¬ C ω) = 0 + m.P (aHn a H C) + 0 + m.P (ann a H C)
    + 0 + m.P (bHn b H C) + 0 + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh (m.ev_not hC) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HC : m.P (fun ω => H ω ∧ C ω) = m.P (aHC a H C) + 0 + 0 + 0
    + m.P (bHC b H C) + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH hC) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HnC : m.P (fun ω => H ω ∧ ¬ C ω) = 0 + m.P (aHn a H C) + 0 + 0
    + 0 + m.P (bHn b H C) + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH (m.ev_not hC)) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_nHC : m.P (fun ω => ¬ H ω ∧ C ω) = 0 + 0 + m.P (anC a H C) + 0
    + 0 + 0 + m.P (bnC b H C) + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and (m.ev_not hH) hC) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_nHnC : m.P (fun ω => ¬ H ω ∧ ¬ C ω) = 0 + 0 + 0 + m.P (ann a H C)
    + 0 + 0 + 0 + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and (m.ev_not hH) (m.ev_not hC)) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_a : m.P a = m.P (aHC a H C) + m.P (aHn a H C) + m.P (anC a H C) + m.P (ann a H C)
    + 0 + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh ha (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_b : m.P b = 0 + 0 + 0 + 0
    + m.P (bHC b H C) + m.P (bHn b H C) + m.P (bnC b H C) + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh hb (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_Ha : m.P (fun ω => H ω ∧ a ω) = m.P (aHC a H C) + m.P (aHn a H C) + 0 + 0
    + 0 + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH ha) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_Hb : m.P (fun ω => H ω ∧ b ω) = 0 + 0 + 0 + 0
    + m.P (bHC b H C) + m.P (bHn b H C) + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH hb) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_aC : m.P (fun ω => a ω ∧ C ω) = m.P (aHC a H C) + 0 + m.P (anC a H C) + 0
    + 0 + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and ha hC) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_anC : m.P (fun ω => a ω ∧ ¬ C ω) = 0 + m.P (aHn a H C) + 0 + m.P (ann a H C)
    + 0 + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and ha (m.ev_not hC)) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_bC : m.P (fun ω => b ω ∧ C ω) = 0 + 0 + 0 + 0
    + m.P (bHC b H C) + 0 + m.P (bnC b H C) + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hb hC) (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_bnC : m.P (fun ω => b ω ∧ ¬ C ω) = 0 + 0 + 0 + 0
    + 0 + m.P (bHn b H C) + 0 + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hb (m.ev_not hC)) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HaC : m.P (fun ω => H ω ∧ (a ω ∧ C ω)) = m.P (aHC a H C) + 0 + 0 + 0
    + 0 + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH (m.ev_and ha hC)) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HbC : m.P (fun ω => H ω ∧ (b ω ∧ C ω)) = 0 + 0 + 0 + 0
    + m.P (bHC b H C) + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH (m.ev_and hb hC)) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_M : m.P (M H C) = m.P (aHC a H C) + 0 + m.P (anC a H C) + m.P (ann a H C)
    + m.P (bHC b H C) + 0 + m.P (bnC b H C) + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh (m.ev_or (m.ev_and hH hC) (m.ev_not hH)) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HM : m.P (fun ω => H ω ∧ M H C ω) = m.P (aHC a H C) + 0 + 0 + 0
    + m.P (bHC b H C) + 0 + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh (m.ev_and hH (m.ev_or (m.ev_and hH hC) (m.ev_not hH)))
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_T : m.P (T H C) = 0 + m.P (aHn a H C) + m.P (anC a H C) + m.P (ann a H C)
    + 0 + m.P (bHn b H C) + m.P (bnC b H C) + m.P (bnn b H C) :=
  decomp_eval m ha hb hH hC excl exh (m.ev_or (m.ev_and hH (m.ev_not hC)) (m.ev_not hH))
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

theorem P_HT : m.P (fun ω => H ω ∧ T H C ω) = 0 + m.P (aHn a H C) + 0 + 0
    + 0 + m.P (bHn b H C) + 0 + 0 :=
  decomp_eval m ha hb hH hC excl exh
    (m.ev_and hH (m.ev_or (m.ev_and hH (m.ev_not hC)) (m.ev_not hH)))
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)

end Lines


/-! ## Section 6: the tag-swapping lemma, displays (8) to (13), and (14) of section 7 -/

theorem arithRec (pH pC pnH hc hnc ch cnh nhc nhnc c : Rat) (s1 : pH = hc + hnc)
    (s2 : pC = ch + cnh) (e1 : ch = hc) (e2 : cnh = nhc) (s3 : pnH = nhc + nhnc)
    (cc : pH + pnH = 1) (coin : pH = 1/2) (ball : pC = c) (indep : hc / pC = pH) (hc0 : 0 < c) :
    hc = c/2 ∧ nhc = c/2 ∧ hnc = (1-c)/2 ∧ nhnc = (1-c)/2 ∧ pnH = 1/2 := by grind

theorem arithCondM (hc nhc nhnc pnH pM c : Rat) (o1 : hc = c/2) (o3 : nhc = c/2)
    (o4 : nhnc = (1-c)/2) (n : pnH = 1/2) (dM : pM = hc + pnH) (hc0 : 0 < c) :
    hc / pM = c/(1+c) ∧ nhc / pM = c/(1+c) ∧ nhnc / pM = (1-c)/(1+c) := by grind

theorem arithCondT (hnc nhc nhnc pnH pT c : Rat) (o2 : hnc = (1-c)/2) (o3 : nhc = c/2)
    (o4 : nhnc = (1-c)/2) (n : pnH = 1/2) (dT : pT = hnc + pnH) (hc1 : c ≤ 1) :
    hnc / pT = (1-c)/(2-c) ∧ nhc / pT = c/(2-c) ∧ nhnc / pT = (1-c)/(2-c) := by grind

theorem arithSub (q pb : Rat) (h : q + pb = 1) : pb = 1 - q := by grind

theorem zero_div' (x : Rat) : 0 / x = 0 := by grind

theorem cond_eq {Ω : Type} (Pr : Measure Ω) {X D L : Ω → Prop} (e : ∀ ω, (X ω ∧ D ω) ↔ L ω) :
    Pr.cond X D = Pr.P L / Pr.P D := by
  unfold Measure.cond; rw [Pr.Pcongr e]

/-! Arithmetic for the tag-swap equation by a second partition. -/

theorem cancel_pos (x y : Rat) (hx : 0 < x) (h : x * y = 0) : y = 0 := by
  have e : y = (x * y) / x := by grind
  rw [h] at e
  grind

theorem arithSwapAB (A B c : Rat) (hc0 : 0 < c) (hc1 : c < 1) (h : 2*c*A + c*B = c)
    (sum : (1+c)*A + (2-c)*B = 1) : A = 1/3 ∧ B = 1/3 := by
  have h1 : c * (2*A + B - 1) = 0 := by grind
  have h2 : 2*A + B - 1 = 0 := cancel_pos c _ hc0 h1
  have h3 : (1 - c) * (B - A) = 0 := by grind
  have h4 : B - A = 0 := cancel_pos (1 - c) _ (by grind) h3
  grind

theorem arithSwapSum (q c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    (1+c)*(q/(1+c)) + (2-c)*((1-q)/(2-c)) = 1 := by grind

theorem arithSwap (pC x1 x3 x5 x7 q c : Rat) (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0)
    (h1 : x1 = q*(c/(1+c))) (h3 : x3 = q*(c/(1+c))) (h5 : x5 = (1-q)*0)
    (h7 : x7 = (1-q)*(c/(2-c))) (pc : pC = c) (hc0 : 0 < c) (hc1 : c < 1) :
    q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3 := by
  have e1 : 2*c*(q/(1+c)) + c*((1-q)/(2-c)) = c := by grind
  exact arithSwapAB _ _ c hc0 hc1 e1 (arithSwapSum q c hc0 hc1)

theorem arithBallDay (pC c : Rat) (ball : pC = c) : pC / 1 = c := by grind
theorem arithOtherDay (x pnH c : Rat) (hx : x = c/2) (hn : pnH = 1/2) : x / pnH = c := by grind

section Recording

variable {Ω : Type} (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
  (c : Rat) (coin : Pr.P H = 1/2) (ball : Pr.P C = c) (indep : Pr.cond H C = Pr.P H)
include hH hC coin ball indep

/-- The recording's values in the urn with a proportion `c` of Monday balls: the four outcomes,
    and the two wakings. -/
theorem rec_values (hc0 : 0 < c) :
    Pr.P (fun ω => H ω ∧ C ω) = c/2 ∧ Pr.P (fun ω => ¬ H ω ∧ C ω) = c/2 ∧
    Pr.P (fun ω => H ω ∧ ¬ C ω) = (1-c)/2 ∧ Pr.P (fun ω => ¬ H ω ∧ ¬ C ω) = (1-c)/2 ∧
    Pr.P (fun ω => ¬ H ω) = 1/2 ∧
    Pr.P (M H C) = Pr.P (fun ω => H ω ∧ C ω) + Pr.P (fun ω => ¬ H ω) ∧
    Pr.P (T H C) = Pr.P (fun ω => H ω ∧ ¬ C ω) + Pr.P (fun ω => ¬ H ω) := by
  have s1 := Pr.split hH hC
  have s2 := Pr.split hC hH
  have e1 : Pr.P (fun ω => C ω ∧ H ω) = Pr.P (fun ω => H ω ∧ C ω) := Pr.Pcongr (fun ω => by grind)
  have e2 : Pr.P (fun ω => C ω ∧ ¬ H ω) = Pr.P (fun ω => ¬ H ω ∧ C ω) :=
    Pr.Pcongr (fun ω => by grind)
  have s3 := Pr.split (Pr.ev_not hH) hC
  have cc := Pr.compl hH
  unfold Measure.cond at indep
  obtain ⟨o1, o2, o3, o4, n⟩ := arithRec _ _ _ _ _ _ _ _ _ _ s1 s2 e1 e2 s3 cc coin ball indep hc0
  have aM := Pr.add (Pr.ev_and hH hC) (Pr.ev_not hH) (by intro ω h; exact h.2 h.1.1)
  have aT := Pr.add (Pr.ev_and hH (Pr.ev_not hC)) (Pr.ev_not hH) (by intro ω h; exact h.2 h.1.1)
  exact ⟨o1, o2, o3, o4, n, aM, aT⟩

/-- The recording's conditional values of the four outcomes given each waking. -/
theorem rec_cells (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Pr.cond (fun ω => H ω ∧ C ω) (M H C) = c/(1+c) ∧
    Pr.cond (fun ω => H ω ∧ ¬ C ω) (M H C) = 0 ∧
    Pr.cond (fun ω => ¬ H ω ∧ C ω) (M H C) = c/(1+c) ∧
    Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (M H C) = (1-c)/(1+c) ∧
    Pr.cond (fun ω => H ω ∧ C ω) (T H C) = 0 ∧
    Pr.cond (fun ω => H ω ∧ ¬ C ω) (T H C) = (1-c)/(2-c) ∧
    Pr.cond (fun ω => ¬ H ω ∧ C ω) (T H C) = c/(2-c) ∧
    Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (T H C) = (1-c)/(2-c) := by
  obtain ⟨o1, o3, o2, o4, n, dM, dT⟩ := rec_values Pr H C hH hC c coin ball indep hc0
  obtain ⟨m1, m3, m4⟩ := arithCondM _ _ _ _ _ c o1 o3 o4 n dM hc0
  obtain ⟨t2, t3, t4⟩ := arithCondT _ _ _ _ _ c o2 o3 o4 n dT hc1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cond_eq Pr (L := fun ω => H ω ∧ C ω)
      (fun ω => by simp only [M]; grind)]; exact m1
  · rw [cond_eq Pr (L := fun _ => False)
      (fun ω => by simp only [M]; grind), Pr.P_false]; exact zero_div' _
  · rw [cond_eq Pr (L := fun ω => ¬ H ω ∧ C ω)
      (fun ω => by simp only [M]; grind)]; exact m3
  · rw [cond_eq Pr (L := fun ω => ¬ H ω ∧ ¬ C ω)
      (fun ω => by simp only [M]; grind)]; exact m4
  · rw [cond_eq Pr (L := fun _ => False)
      (fun ω => by simp only [T]; grind), Pr.P_false]; exact zero_div' _
  · rw [cond_eq Pr (L := fun ω => H ω ∧ ¬ C ω)
      (fun ω => by simp only [T]; grind)]; exact t2
  · rw [cond_eq Pr (L := fun ω => ¬ H ω ∧ C ω)
      (fun ω => by simp only [T]; grind)]; exact t3
  · rw [cond_eq Pr (L := fun ω => ¬ H ω ∧ ¬ C ω)
      (fun ω => by simp only [T]; grind)]; exact t4

/-- **(8)**, section 6, source line 723-728:
    ```
    \prany(H\wedge C)=\prany(\lnot H\wedge C)=\tfrac{c}{2}\qquad
    \prany(H\wedge\lnot C)=\prany(\lnot H\wedge\lnot C)=\tfrac{1-c}{2}\\
    \prany(H\mid\hear{M})=\frac{c}{1+c}\qquad
    \prany(H\mid\hear{T})=\frac{1-c}{2-c}
    ```
    Choice: the first assumption with the urn altered, `Pr(H) = 1/2`, `Pr(C) = c`, `0 < c < 1`, and
    independence `Pr(H | C) = Pr(H)`; `[M]` is heads with a Monday ball or tails, `[T]` heads with a
    Tuesday ball or tails (the justification after (8)). -/
theorem display8 (hc0 : 0 < c) (hc1 : c < 1) :
    Pr.P (fun ω => H ω ∧ C ω) = c/2 ∧ Pr.P (fun ω => ¬ H ω ∧ C ω) = c/2 ∧
    Pr.P (fun ω => H ω ∧ ¬ C ω) = (1-c)/2 ∧ Pr.P (fun ω => ¬ H ω ∧ ¬ C ω) = (1-c)/2 ∧
    Pr.cond H (M H C) = c/(1+c) ∧ Pr.cond H (T H C) = (1-c)/(2-c) := by
  obtain ⟨o1, o3, o2, o4, _, _, _⟩ := rec_values Pr H C hH hC c coin ball indep hc0
  obtain ⟨m1, _, _, _, _, t2, _, _⟩ :=
    rec_cells Pr H C hH hC c coin ball indep hc0 (lt_le _ _ hc1)
  refine ⟨o1, o3, o2, o4, ?_, ?_⟩
  · rw [cond_eq Pr (L := fun ω => H ω ∧ C ω)
      (fun ω => by simp only [M]; grind)]
    rw [cond_eq Pr (L := fun ω => H ω ∧ C ω)
      (fun ω => by simp only [M]; grind)] at m1
    exact m1
  · rw [cond_eq Pr (L := fun ω => H ω ∧ ¬ C ω)
      (fun ω => by simp only [T]; grind)]
    rw [cond_eq Pr (L := fun ω => H ω ∧ ¬ C ω)
      (fun ω => by simp only [T]; grind)] at t2
    exact t2

/-- The recording's value of a Monday ball given each event of the second partition:
    `Pr(C | you are awakened on the day the ball marks) = c` (that event takes place on every
    outcome) and `Pr(C | you are awakened on the other day) = c` (that event is tails, and the
    ball is independent of the coin). -/
theorem rec_second (hc0 : 0 < c) :
    Pr.cond C (ballDay H C) = c ∧ Pr.cond C (otherDay H C) = c := by
  obtain ⟨o1, o3, o2, o4, n, dM, dT⟩ := rec_values Pr H C hH hC c coin ball indep hc0
  constructor
  · rw [cond_eq Pr (L := C) (fun ω => by simp only [ballDay, M, T]; grind)]
    have e : Pr.P (ballDay H C) = Pr.P (fun _ => True) :=
      Pr.Pcongr (fun ω => by simp only [ballDay, M, T]; grind)
    rw [e, Pr.total]; exact arithBallDay _ c ball
  · rw [cond_eq Pr (L := fun ω => ¬ H ω ∧ C ω)
      (fun ω => by simp only [otherDay, M, T]; grind)]
    have e : Pr.P (otherDay H C) = Pr.P (fun ω => ¬ H ω) :=
      Pr.Pcongr (fun ω => by simp only [otherDay, M, T]; grind)
    rw [e]; exact arithOtherDay _ _ c o3 n

end Recording

/-! ### Your measure in the uneven urn: the construction at the four outcomes -/

theorem arith9 (pH x1 x2 x5 x6 q c : Rat) (s : pH = x1 + x2 + 0 + 0 + x5 + x6 + 0 + 0)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h5 : x5 = (1-q)*0)
    (h6 : x6 = (1-q)*((1-c)/(2-c))) : pH = q*(c/(1+c)) + (1-q)*((1-c)/(2-c)) := by grind

theorem arith9eq (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    c/(1+c) = (1-c)/(2-c) ↔ c = 1/2 := by grind

theorem arith10 (aC anC' bC bnC' x1 x2 x3 x4 x5 x6 x7 x8 q c : Rat)
    (s1 : aC = x1 + 0 + x3 + 0 + 0 + 0 + 0 + 0) (s2 : anC' = 0 + x2 + 0 + x4 + 0 + 0 + 0 + 0)
    (s3 : bC = 0 + 0 + 0 + 0 + x5 + 0 + x7 + 0) (s4 : bnC' = 0 + 0 + 0 + 0 + 0 + x6 + 0 + x8)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c))) (h4 : x4 = q*((1-c)/(1+c)))
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    aC = 2*c*(q/(1+c)) ∧ anC' = (1-c)*(q/(1+c)) ∧ bC = c*((1-q)/(2-c)) ∧
    bnC' = 2*(1-c)*((1-q)/(2-c)) := by grind

theorem arith11 (hc pC hnc pnC x1 x2 x3 x4 x5 x6 x7 x8 q c A B : Rat)
    (sHC : hc = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0) (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0)
    (sHnC : hnc = 0 + x2 + 0 + 0 + 0 + x6 + 0 + 0) (snC : pnC = 0 + x2 + 0 + x4 + 0 + x6 + 0 + x8)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c))) (h4 : x4 = q*((1-c)/(1+c)))
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) (hA : A = q/(1+c)) (hB : B = (1-q)/(2-c))
    (Apos : 0 < A) (Bpos : 0 < B) (hc0 : 0 < c) (hc1 : c < 1) :
    hc / pC = A/(2*A+B) ∧ hnc / pnC = B/(A+2*B) := by grind

theorem arith12 (A B c : Rat) (Apos : 0 < A) (Bpos : 0 < B) (s : (1+c)*A + (2-c)*B = 1) :
    A/(2*A+B) = B/(A+2*B) ↔ A = 1/3 ∧ B = 1/3 := by grind

theorem arith12sum (q c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    (1+c)*(q/(1+c)) + (2-c)*((1-q)/(2-c)) = 1 := by grind

theorem arith13 (pH hc pC hnc pnC aC haC bC hbC x1 x2 x3 x4 x5 x6 x7 x8 q c : Rat)
    (sH : pH = x1 + x2 + 0 + 0 + x5 + x6 + 0 + 0)
    (sHC : hc = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0) (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0)
    (sHnC : hnc = 0 + x2 + 0 + 0 + 0 + x6 + 0 + 0) (snC : pnC = 0 + x2 + 0 + x4 + 0 + x6 + 0 + x8)
    (saC : aC = x1 + 0 + x3 + 0 + 0 + 0 + 0 + 0) (shaC : haC = x1 + 0 + 0 + 0 + 0 + 0 + 0 + 0)
    (sbC : bC = 0 + 0 + 0 + 0 + x5 + 0 + x7 + 0) (shbC : hbC = 0 + 0 + 0 + 0 + x5 + 0 + 0 + 0)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c))) (h4 : x4 = q*((1-c)/(1+c)))
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) (hA : q/(1+c) = 1/3) (hB : (1-q)/(2-c) = 1/3)
    (hc0 : 0 < c) (hc1 : c < 1) :
    hc / pC = 1/3 ∧ hnc / pnC = 1/3 ∧ pH = 1/3 ∧ pC = c ∧ aC / pC = 2/3 ∧ haC / aC = 1/2 ∧
    hbC / bC = 0 := by grind

theorem arith14 (hc pC x1 x3 x5 x7 q c : Rat) (c1 : c = 1)
    (sHC : hc = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0) (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0)
    (h1 : x1 = q*(c/(1+c))) (h3 : x3 = q*(c/(1+c))) (h5 : x5 = (1-q)*0)
    (h7 : x7 = (1-q)*(c/(2-c))) : pC = 1 ∧ hc / pC = q/2 := by grind

theorem arith14b (q c : Rat) (c1 : c = 1) (hA : q/(1+c) = 1/3) (hB : (1-q)/(2-c) = 1/3) :
    q/2 = 1/3 := by grind

/-- The justification of (9), source line 738: "The two values are equal iff `c = 1/2`." -/
theorem display9_equal_iff (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    c/(1+c) = (1-c)/(2-c) ↔ c = 1/2 := arith9eq c hc0 hc1

theorem AB_pos (q c : Rat) (hq0 : 0 < q) (hq1 : q < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    0 < q/(1+c) ∧ 0 < (1-q)/(2-c) :=
  ⟨pos_div _ _ hq0 (by grind), pos_div _ _ (by grind) (by grind)⟩

section TagSwap

variable {Ω Ω' : Type} (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
  (c : Rat) (coin : Pr.P H = 1/2) (ball : Pr.P C = c) (indep : Pr.cond H C = Pr.P H)
  (π : Measure Ω') (H' C' a b : Ω' → Prop)
  (hH' : π.ev H') (hC' : π.ev C') (ha : π.ev a) (hb : π.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) (qa : π.P a = q)
  (con1 : π.cond (fun ω => H' ω ∧ C' ω) a = Pr.cond (fun ω => H ω ∧ C ω) (M H C))
  (con2 : π.cond (fun ω => H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => H ω ∧ ¬ C ω) (M H C))
  (con3 : π.cond (fun ω => ¬ H' ω ∧ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ C ω) (M H C))
  (con4 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (M H C))
  (con5 : π.cond (fun ω => H' ω ∧ C' ω) b = Pr.cond (fun ω => H ω ∧ C ω) (T H C))
  (con6 : π.cond (fun ω => H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => H ω ∧ ¬ C ω) (T H C))
  (con7 : π.cond (fun ω => ¬ H' ω ∧ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ C ω) (T H C))
  (con8 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (T H C))
include hH hC coin ball indep hH' hC' ha hb excl exh hq0 hq1 qa con1 con2 con3 con4 con5 con6
  con7 con8

omit hH' hC' in
/-- The eight lines of your measure in the urn with proportion `c` (`0 < c ≤ 1`), from the
    construction and the recording's values: `π(cell ∧ outcome) = π(cell) Pr(outcome | waking)`. -/
theorem lines_c (hc0 : 0 < c) (hc1 : c ≤ 1) :
    π.P (aHC a H' C') = q*(c/(1+c)) ∧ π.P (aHn a H' C') = q*0 ∧
    π.P (anC a H' C') = q*(c/(1+c)) ∧ π.P (ann a H' C') = q*((1-c)/(1+c)) ∧
    π.P (bHC b H' C') = (1-q)*0 ∧ π.P (bHn b H' C') = (1-q)*((1-c)/(2-c)) ∧
    π.P (bnC b H' C') = (1-q)*(c/(2-c)) ∧ π.P (bnn b H' C') = (1-q)*((1-c)/(2-c)) := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := rec_cells Pr H C hH hC c coin ball indep hc0 hc1
  have sum := π.part_sum ha hb excl exh
  have qb : π.P b = 1 - q := by rw [qa] at sum; exact (arithSub _ _ sum)
  have q0 : q ≠ 0 := by grind
  have q1 : 1 - q ≠ 0 := by grind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← v1]; exact π.line_from_cond qa q0 con1 (fun ω => by simp only [aHC]; grind)
  · rw [← v2]; exact π.line_from_cond qa q0 con2 (fun ω => by simp only [aHn]; grind)
  · rw [← v3]; exact π.line_from_cond qa q0 con3 (fun ω => by simp only [anC]; grind)
  · rw [← v4]; exact π.line_from_cond qa q0 con4 (fun ω => by simp only [ann]; grind)
  · rw [← v5]; exact π.line_from_cond qb q1 con5 (fun ω => by simp only [bHC]; grind)
  · rw [← v6]; exact π.line_from_cond qb q1 con6 (fun ω => by simp only [bHn]; grind)
  · rw [← v7]; exact π.line_from_cond qb q1 con7 (fun ω => by simp only [bnC]; grind)
  · rw [← v8]; exact π.line_from_cond qb q1 con8 (fun ω => by simp only [bnn]; grind)

/-- **(9)**, section 6, source line 735:
    ```
    \prsb(H)=q\,\frac{c}{1+c}+(1-q)\,\frac{1-c}{2-c}
    ```
    Choice (here and in (10) to (13)): `H'`, `C'` are the events `H`, `C` in your measure; the
    construction `π(X | a) = Pr(X | [M])`, `π(X | b) = Pr(X | [T])` is assumed at the four outcomes
    `X` (every event of the recording's algebra is a union of them); `a`, `b` are exclusive and
    exhaustive as sets, which gives (4); `q = π(a)`, `0 < q < 1`. -/
theorem display9 (hc0 : 0 < c) (hc1 : c < 1) :
    π.P H' = q * (c/(1+c)) + (1-q) * ((1-c)/(2-c)) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 (lt_le _ _ hc1)
  exact arith9 _ _ _ _ _ _ _ (P_H π ha hb hH' hC' excl exh) l1 l2 l5 l6

/-- **(10)**, section 6, source lines 740-744:
    ```
    \prsb(\ea\wedge C)=2cA\qquad \prsb(\ea\wedge\lnot C)=(1-c)A\qquad
    \prsb(\eb\wedge C)=cB\qquad \prsb(\eb\wedge\lnot C)=2(1-c)B\\
    \text{with } A=\frac{q}{1+c},\quad B=\frac{1-q}{2-c}
    ``` -/
theorem display10 (hc0 : 0 < c) (hc1 : c < 1) :
    π.P (fun ω => a ω ∧ C' ω) = 2*c*(q/(1+c)) ∧
    π.P (fun ω => a ω ∧ ¬ C' ω) = (1-c)*(q/(1+c)) ∧
    π.P (fun ω => b ω ∧ C' ω) = c*((1-q)/(2-c)) ∧
    π.P (fun ω => b ω ∧ ¬ C' ω) = 2*(1-c)*((1-q)/(2-c)) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 (lt_le _ _ hc1)
  exact arith10 _ _ _ _ _ _ _ _ _ _ _ _ q c (P_aC π ha hb hH' hC' excl exh)
    (P_anC π ha hb hH' hC' excl exh) (P_bC π ha hb hH' hC' excl exh)
    (P_bnC π ha hb hH' hC' excl exh) l1 l2 l3 l4 l5 l6 l7 l8 hc0 (lt_le _ _ hc1)

/-- **(11)**, section 6, source line 748-749:
    ```
    \prsb(H\mid C)=\frac{A}{2A+B}\qquad
    \prsb(H\mid\lnot C)=\frac{B}{A+2B}
    ``` -/
theorem display11 (hc0 : 0 < c) (hc1 : c < 1) :
    π.cond H' C' = (q/(1+c)) / (2*(q/(1+c)) + (1-q)/(2-c)) ∧
    π.cond H' (fun ω => ¬ C' ω) = ((1-q)/(2-c)) / (q/(1+c) + 2*((1-q)/(2-c))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 (lt_le _ _ hc1)
  obtain ⟨Apos, Bpos⟩ := AB_pos q c hq0 hq1 hc0 hc1
  unfold Measure.cond
  exact arith11 _ _ _ _ _ _ _ _ _ _ _ _ q c _ _ (P_HC π ha hb hH' hC' excl exh)
    (P_C π ha hb hH' hC' excl exh) (P_HnC π ha hb hH' hC' excl exh)
    (P_nC π ha hb hH' hC' excl exh) l1 l2 l3 l4 l5 l6 l7 l8 rfl rfl Apos Bpos hc0 hc1

/-- **(12)**, section 6, source line 754:
    ```
    \prsb(H\mid C)=\prsb(H\mid\lnot C)\ \text{ iff }\ A=B=\third
    ``` -/
theorem display12 (hc0 : 0 < c) (hc1 : c < 1) :
    π.cond H' C' = π.cond H' (fun ω => ¬ C' ω) ↔
      q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3 := by
  obtain ⟨e1, e2⟩ := display11 Pr H C hH hC c coin ball indep π H' C' a b
    hH' hC' ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 hc1
  obtain ⟨Apos, Bpos⟩ := AB_pos q c hq0 hq1 hc0 hc1
  rw [e1, e2]
  exact arith12 _ _ c Apos Bpos (arith12sum q c hc0 hc1)

/-- **(13)**, section 6, source lines 759-766:
    ```
    A=B=\third:\qquad
    \prsb(H\mid C)=\prsb(H\mid\lnot C)=\third\qquad \prsb(H)=\third\\
    \prsb(C)=c\qquad
    \prsb(\ea\mid C)=\twothirds\qquad
    \prsb(H\mid \ea\wedge C)=\half\qquad
    \prsb(H\mid \eb\wedge C)=0
    ```
    Choice: "A = B = 1/3" is the hypothesis `q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3`. -/
theorem display13 (hc0 : 0 < c) (hc1 : c < 1)
    (hAB : q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3) :
    π.cond H' C' = 1/3 ∧ π.cond H' (fun ω => ¬ C' ω) = 1/3 ∧ π.P H' = 1/3 ∧
    π.P C' = c ∧ π.cond a C' = 2/3 ∧ π.cond H' (fun ω => a ω ∧ C' ω) = 1/2 ∧
    π.cond H' (fun ω => b ω ∧ C' ω) = 0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 (lt_le _ _ hc1)
  unfold Measure.cond
  exact arith13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q c (P_H π ha hb hH' hC' excl exh)
    (P_HC π ha hb hH' hC' excl exh) (P_C π ha hb hH' hC' excl exh)
    (P_HnC π ha hb hH' hC' excl exh) (P_nC π ha hb hH' hC' excl exh)
    (P_aC π ha hb hH' hC' excl exh) (P_HaC π ha hb hH' hC' excl exh)
    (P_bC π ha hb hH' hC' excl exh) (P_HbC π ha hb hH' hC' excl exh)
    l1 l2 l3 l4 l5 l6 l7 l8 hAB.1 hAB.2 hc0 hc1

/-- **(14)**, section 7, source line 803:
    ```
    \prsb(H\mid C)=\third.
    ```
    Choice: the urn with Monday balls only is `c = 1`, outside the lemma's `0 < c < 1`; the
    lemma's `A = B = 1/3` (which the lemma reaches through `π(H | ¬C)`, a ratio with no value at
    `c = 1`, since `π(¬C) = 0` there) is carried to `c = 1` as a hypothesis, as the paper does
    with "the value given C is the same for any distribution (see (13))". -/
theorem display14 (c1 : c = 1) (hAB : q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3) :
    π.cond H' C' = 1/3 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 (by grind)
    (by grind)
  unfold Measure.cond
  obtain ⟨_, e⟩ := arith14 _ _ _ _ _ _ q c c1 (P_HC π ha hb hH' hC' excl exh)
    (P_C π ha hb hH' hC' excl exh) l1 l3 l5 l7
  rw [e]; exact arith14b q c c1 hAB.1 hAB.2

/-- What (14) rests on, at `c = 1`: `π(C) = 1` and `π(H | C) = q/2`, so (14) holds exactly when
    `q = 2/3`, the lemma's `q = (1+c)/3` at `c = 1`. -/
theorem display14_at_c1 (c1 : c = 1) : π.P C' = 1 ∧ π.cond H' C' = q/2 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 (by grind)
    (by grind)
  unfold Measure.cond
  exact arith14 _ _ _ _ _ _ q c c1 (P_HC π ha hb hH' hC' excl exh)
    (P_C π ha hb hH' hC' excl exh) l1 l3 l5 l7

/-- **The tag-swap equation by a second partition** (not a numbered display of the paper).
    Besides the cells `a` and `b`, take two more cells of your measure: `d`, being certain that
    today is the day the ball marks, and `e`, being certain that it is the other day. With the
    construction applied to them at the event `C`,
    `π(C | d) = Pr(C | you are awakened on the day the ball marks)` and
    `π(C | e) = Pr(C | you are awakened on the other day)`, the ball has the urn's proportion `c`
    in each cell. The two cells partition your measure, so by Sure Thing `π(C) = c`. With the
    lines of (10) that is `A = B = 1/3`, and so, by (12), `π(H | C) = π(H | ¬C)`. -/
theorem tag_swap_by_second_partition (hc0 : 0 < c) (hc1 : c < 1) (d e : Ω' → Prop)
    (hd : π.ev d) (he : π.ev e) (dpos : π.P d ≠ 0) (epos : π.P e ≠ 0)
    (de_and : π.P (fun ω => d ω ∧ e ω) = 0) (de_or : π.P (fun ω => d ω ∨ e ω) = 1)
    (cond_d : π.cond C' d = Pr.cond C (ballDay H C))
    (cond_e : π.cond C' e = Pr.cond C (otherDay H C)) :
    π.P C' = c ∧ (q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3) ∧
    π.cond H' C' = π.cond H' (fun ω => ¬ C' ω) := by
  obtain ⟨r1, r2⟩ := rec_second Pr H C hH hC c coin ball indep hc0
  have pc : π.P C' = c :=
    π.sure_thing_cells hC' hd he dpos epos (cond_d.trans r1) (cond_e.trans r2) de_and de_or
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 (lt_le _ _ hc1)
  have hAB := arithSwap _ _ _ _ _ q c (P_C π ha hb hH' hC' excl exh) l1 l3 l5 l7 pc hc0 hc1
  exact ⟨pc, hAB, (display12 Pr H C hH hC c coin ball indep π H' C' a b hH' hC' ha hb excl exh q
    hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 hc1).mpr hAB⟩

end TagSwap

/-! ## Section 10 and Appendix C: the full measure, (24), (23), (C1), (C2), (C3) -/

theorem arith24 (x1 x2 x3 x4 x5 x6 x7 x8 q c : Rat) (fair : c = 1/2)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c))) (h4 : x4 = q*((1-c)/(1+c)))
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) :
    x1 = q/3 ∧ x3 = q/3 ∧ x4 = q/3 ∧ x6 = (1-q)/3 ∧ x7 = (1-q)/3 ∧ x8 = (1-q)/3 ∧
    x2 = 0 ∧ x5 = 0 := by grind

theorem arithC (pH pC hc pnC hnc pM hm pT ht x1 x2 x3 x4 x5 x6 x7 x8 q : Rat)
    (sH : pH = x1 + x2 + 0 + 0 + x5 + x6 + 0 + 0)
    (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0) (sHC : hc = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0)
    (snC : pnC = 0 + x2 + 0 + x4 + 0 + x6 + 0 + x8) (sHnC : hnc = 0 + x2 + 0 + 0 + 0 + x6 + 0 + 0)
    (sM : pM = x1 + 0 + x3 + x4 + x5 + 0 + x7 + x8) (sHM : hm = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0)
    (sT : pT = 0 + x2 + x3 + x4 + 0 + x6 + x7 + x8) (sHT : ht = 0 + x2 + 0 + 0 + 0 + x6 + 0 + 0)
    (h1 : x1 = q/3) (h3 : x3 = q/3) (h4 : x4 = q/3) (h6 : x6 = (1-q)/3) (h7 : x7 = (1-q)/3)
    (h8 : x8 = (1-q)/3) (h2 : x2 = 0) (h5 : x5 = 0) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pH = q/3 + (1-q)/3 ∧ q/3 + (1-q)/3 = 1/3 ∧ pC = (1+q)/3 ∧ hc / pC = q/(1+q) ∧
    hnc / pnC = (1-q)/(2-q) ∧ pM = (2+q)/3 ∧ hm / pM = q/(2+q) ∧ pT = (3-q)/3 ∧
    ht / pT = (1-q)/(3-q) := by grind

theorem arithThirds (q : Rat) : q/3 + (1-q)/3 = q*(1/3) + (1-q)*(1/3) := by grind

theorem arithC2 (q : Rat) (hq0 : 0 ≤ q) : q/(1+q) = 1/2 ↔ q = 1 := by grind

theorem arithC3j (q : Rat) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (q = 1/2 → q/(2+q) = 1/5 ∧ (1-q)/(3-q) = 1/5) ∧ (q/(2+q) = 1/3 ↔ q = 1) ∧
    ((1-q)/(3-q) = 1/3 ↔ q = 0) := by grind

section FullMeasure

variable {Ω : Type} (π : Measure Ω) (H C a b : Ω → Prop)
  (hH : π.ev H) (hC : π.ev C) (ha : π.ev a) (hb : π.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (q : Rat) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
  (L1 : π.P (fun ω => a ω ∧ H ω ∧ C ω) = q/3)
  (L2 : π.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = q/3)
  (L3 : π.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = q/3)
  (L4 : π.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = (1-q)/3)
  (L5 : π.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = (1-q)/3)
  (L6 : π.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = (1-q)/3)
  (L7 : π.P (fun ω => a ω ∧ H ω ∧ ¬ C ω) = 0)
  (L8 : π.P (fun ω => b ω ∧ H ω ∧ C ω) = 0)
include hH hC ha hb excl exh hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8

theorem full_sums :
    π.P H = q/3 + (1-q)/3 ∧ q/3 + (1-q)/3 = 1/3 ∧ π.P C = (1+q)/3 ∧
    π.cond H C = q/(1+q) ∧ π.cond H (fun ω => ¬ C ω) = (1-q)/(2-q) ∧
    π.P (M H C) = (2+q)/3 ∧ π.cond H (M H C) = q/(2+q) ∧ π.P (T H C) = (3-q)/3 ∧
    π.cond H (T H C) = (1-q)/(3-q) := by
  unfold Measure.cond
  exact arithC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (P_H π ha hb hH hC excl exh)
    (P_C π ha hb hH hC excl exh) (P_HC π ha hb hH hC excl exh) (P_nC π ha hb hH hC excl exh)
    (P_HnC π ha hb hH hC excl exh) (P_M π ha hb hH hC excl exh) (P_HM π ha hb hH hC excl exh)
    (P_T π ha hb hH hC excl exh) (P_HT π ha hb hH hC excl exh) L1 L2 L3 L4 L5 L6 L7 L8 hq0 hq1

/-- **(23)**, section 10, source lines 1147-1150, as sums of the lines of (24):
    ```
    \prsb(H)=q\cdot\third+(1-q)\cdot\third=\third\qquad
    \prsb(C)=\frac{1+q}{3}
    ```
    Choice (here and in (C1) to (C3)): the hypotheses are the six lines of (24) and its two lines
    at 0, `a`, `b` exclusive and exhaustive as sets, `0 ≤ q ≤ 1`. The paper's left side is by Sure
    Thing; here it is the sum of the heads lines, `q/3 + (1-q)/3`. -/
theorem display23_from_lines :
    π.P H = q * (1/3) + (1-q) * (1/3) ∧ q * (1/3) + (1-q) * (1/3) = 1/3 ∧
    π.P C = (1+q)/3 := by
  obtain ⟨e1, e2, e3, _⟩ := full_sums π H C a b hH hC ha hb excl exh q hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8
  refine ⟨?_, ?_, e3⟩
  · rw [e1]; exact arithThirds q
  · exact (arithThirds q).symm.trans e2

/-- **(C1)**, Appendix C, source lines 1311-1315:
    ```
    \prsb(C)=\frac{1+q}{3}\qquad
    \prsb(H\mid C)=\frac{q}{1+q}\qquad
    \prsb(H\mid\lnot C)=\frac{1-q}{2-q}
    ``` -/
theorem displayC1 :
    π.P C = (1+q)/3 ∧ π.cond H C = q/(1+q) ∧ π.cond H (fun ω => ¬ C ω) = (1-q)/(2-q) := by
  obtain ⟨_, _, e3, e4, e5, _⟩ := full_sums π H C a b hH hC ha hb excl exh q hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8
  exact ⟨e3, e4, e5⟩

/-- **(C2)**, Appendix C, source line 1320:
    ```
    \prsb(H\mid C)=\half\ \text{ iff }\ q=1.
    ``` -/
theorem displayC2 : π.cond H C = 1/2 ↔ q = 1 := by
  obtain ⟨_, _, _, e4, _⟩ := full_sums π H C a b hH hC ha hb excl exh q hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8
  rw [e4]; exact arithC2 q hq0

/-- **(C3)**, Appendix C, source lines 1325-1330:
    ```
    \prsb(\hear{M})=\frac{2+q}{3},\quad
    \prsb(H\mid\hear{M})=\frac{q}{2+q}\qquad
    \prsb(\hear{T})=\frac{3-q}{3},\quad
    \prsb(H\mid\hear{T})=\frac{1-q}{3-q}
    ```
    Choice: `[M]` and `[T]` in your measure are the recording's events, heads with a Monday
    ball or tails, heads with a Tuesday ball or tails (they contain the lines the justification
    lists). -/
theorem displayC3 :
    π.P (M H C) = (2+q)/3 ∧ π.cond H (M H C) = q/(2+q) ∧
    π.P (T H C) = (3-q)/3 ∧ π.cond H (T H C) = (1-q)/(3-q) := by
  obtain ⟨_, _, _, _, _, e6, e7, e8, e9⟩ :=
    full_sums π H C a b hH hC ha hb excl exh q hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8
  exact ⟨e6, e7, e8, e9⟩

/-- The justification of (C3), source line 1332: at `q = 1/2` both conditionals are 1/5;
    `π(H | [M]) = Pr(H | [M])` (which is 1/3, step (2)) iff `q = 1`; `π(H | [T]) = Pr(H | [T])`
    iff `q = 0`. -/
theorem displayC3_justification :
    (q = 1/2 → π.cond H (M H C) = 1/5 ∧ π.cond H (T H C) = 1/5) ∧
    (π.cond H (M H C) = 1/3 ↔ q = 1) ∧ (π.cond H (T H C) = 1/3 ↔ q = 0) := by
  obtain ⟨_, _, _, _, _, _, e7, _, e9⟩ :=
    full_sums π H C a b hH hC ha hb excl exh q hq0 hq1 L1 L2 L3 L4 L5 L6 L7 L8
  rw [e7, e9]; exact arithC3j q hq0 hq1

end FullMeasure

/-! ### (24) and (23) from the construction (fair urn), and your values beside (22) -/

theorem bounds_half (c : Rat) (h : c = 1/2) : 0 < c ∧ c ≤ 1 := by subst h; exact ⟨by grind, by grind⟩

theorem bounds_99 (c : Rat) (h : c = 99/100) : 0 < c ∧ c ≤ 1 := by subst h; exact ⟨by grind, by grind⟩

theorem arith22 (pC pHa pa x1 x2 x3 x4 x5 x6 x7 x8 q c : Rat) (c99 : c = 99/100)
    (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0) (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0)
    (sa : pa = x1 + x2 + x3 + x4 + 0 + 0 + 0 + 0)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c))) (h4 : x4 = q*((1-c)/(1+c)))
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) (hA : q/(1+c) = 1/3) (hB : (1-q)/(2-c) = 1/3) :
    pC = 99/100 ∧ pHa / pa = 99/199 ∧ x1 = 33/100 ∧ x3 = 33/100 ∧ x7 = 33/100 ∧
    x4 = 1/300 ∧ x6 = 1/300 ∧ x8 = 1/300 := by grind

theorem arith22b (pHb pb x5 x6 x7 x8 q c : Rat) (c99 : c = 99/100) (hq1 : q < 1)
    (sHb : pHb = 0 + 0 + 0 + 0 + x5 + x6 + 0 + 0) (sb : pb = 0 + 0 + 0 + 0 + x5 + x6 + x7 + x8)
    (h5 : x5 = (1-q)*0) (h6 : x6 = (1-q)*((1-c)/(2-c))) (h7 : x7 = (1-q)*(c/(2-c)))
    (h8 : x8 = (1-q)*((1-c)/(2-c))) : pHb / pb = 1/101 := by grind

theorem arith22a (pHa pa x1 x2 x3 x4 q c : Rat) (c99 : c = 99/100) (hq0 : 0 < q)
    (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0) (sa : pa = x1 + x2 + x3 + x4 + 0 + 0 + 0 + 0)
    (h1 : x1 = q*(c/(1+c))) (h2 : x2 = q*0) (h3 : x3 = q*(c/(1+c)))
    (h4 : x4 = q*((1-c)/(1+c))) : pHa / pa = 99/199 := by grind

section TagSwap2

variable {Ω Ω' : Type} (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
  (c : Rat) (coin : Pr.P H = 1/2) (ball : Pr.P C = c) (indep : Pr.cond H C = Pr.P H)
  (π : Measure Ω') (H' C' a b : Ω' → Prop)
  (hH' : π.ev H') (hC' : π.ev C') (ha : π.ev a) (hb : π.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) (qa : π.P a = q)
  (con1 : π.cond (fun ω => H' ω ∧ C' ω) a = Pr.cond (fun ω => H ω ∧ C ω) (M H C))
  (con2 : π.cond (fun ω => H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => H ω ∧ ¬ C ω) (M H C))
  (con3 : π.cond (fun ω => ¬ H' ω ∧ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ C ω) (M H C))
  (con4 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (M H C))
  (con5 : π.cond (fun ω => H' ω ∧ C' ω) b = Pr.cond (fun ω => H ω ∧ C ω) (T H C))
  (con6 : π.cond (fun ω => H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => H ω ∧ ¬ C ω) (T H C))
  (con7 : π.cond (fun ω => ¬ H' ω ∧ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ C ω) (T H C))
  (con8 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (T H C))
include hH hC coin ball indep hH' hC' ha hb excl exh hq0 hq1 qa con1 con2 con3 con4 con5 con6
  con7 con8

omit hH' hC' in
/-- **(24)**, section 10, source lines 1155-1161:
    ```
    \prsb(\ea\wedge H\wedge C)&=\prsb(\ea\wedge\lnot H\wedge C)=\prsb(\ea\wedge\lnot H\wedge\lnot C)=\tfrac{q}{3}\\
    \prsb(\eb\wedge H\wedge\lnot C)&=\prsb(\eb\wedge\lnot H\wedge C)=\prsb(\eb\wedge\lnot H\wedge\lnot C)=\tfrac{1-q}{3}\\
    \prsb(\ea\wedge H\wedge\lnot C)&=\prsb(\eb\wedge H\wedge C)=0.
    ```
    Choice: the first assumption is the urn with `c = 1/2`; the construction is assumed at the
    four outcomes, as in (9) to (13); `q = π(a)`, `0 < q < 1`. -/
theorem display24 (fair : c = 1/2) :
    π.P (fun ω => a ω ∧ H' ω ∧ C' ω) = q/3 ∧ π.P (fun ω => a ω ∧ ¬ H' ω ∧ C' ω) = q/3 ∧
    π.P (fun ω => a ω ∧ ¬ H' ω ∧ ¬ C' ω) = q/3 ∧
    π.P (fun ω => b ω ∧ H' ω ∧ ¬ C' ω) = (1-q)/3 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ C' ω) = (1-q)/3 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ ¬ C' ω) = (1-q)/3 ∧
    π.P (fun ω => a ω ∧ H' ω ∧ ¬ C' ω) = 0 ∧ π.P (fun ω => b ω ∧ H' ω ∧ C' ω) = 0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 (bounds_half c fair).1 (bounds_half c fair).2
  exact arith24 _ _ _ _ _ _ _ _ q c fair l1 l2 l3 l4 l5 l6 l7 l8

/-- **(23)** from the construction: (24) and then its sums. -/
theorem display23 (fair : c = 1/2) : π.P H' = 1/3 ∧ π.P C' = (1+q)/3 := by
  obtain ⟨L1, L2, L3, L4, L5, L6, L7, L8⟩ := display24 Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 fair
  obtain ⟨e1, e2, e3, _⟩ := full_sums π H' C' a b hH' hC' ha hb excl exh q (lt_le _ _ hq0)
    (lt_le _ _ hq1) L1 L2 L3 L4 L5 L6 L7 L8
  exact ⟨e1.trans e2, e3⟩

/-- **(22)**, second line, section 8.5, source line 1061:
    ```
    \prsb(C)=\tfrac{99}{100}\qquad \prsb(H\mid\ea)=\tfrac{99}{199}\qquad \prsb(H\mid\eb)=\tfrac{1}{101}.
    ```
    with the sentence after it: a waking under a Monday ball has 33/100, one under the Tuesday
    ball 1/300 (the lines `a∧H∧C`, `a∧¬H∧C`, `b∧¬H∧C` and `a∧¬H∧¬C`, `b∧H∧¬C`, `b∧¬H∧¬C`).
    Choice: the urn of section 6 at `c = 99/100`; `π(C)` and the waking values use the lemma's
    `A = B = 1/3`, (13); `π(H | a)`, `π(H | b)` use only the construction, (8). -/
theorem display22_yours (c99 : c = 99/100) (hAB : q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3) :
    π.P C' = 99/100 ∧ π.cond H' a = 99/199 ∧ π.cond H' b = 1/101 ∧
    π.P (fun ω => a ω ∧ H' ω ∧ C' ω) = 33/100 ∧ π.P (fun ω => a ω ∧ ¬ H' ω ∧ C' ω) = 33/100 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ C' ω) = 33/100 ∧
    π.P (fun ω => a ω ∧ ¬ H' ω ∧ ¬ C' ω) = 1/300 ∧
    π.P (fun ω => b ω ∧ H' ω ∧ ¬ C' ω) = 1/300 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ ¬ C' ω) = 1/300 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lines_c Pr H C hH hC c coin ball indep π H' C' a b
    ha hb excl exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 (bounds_99 c c99).1 (bounds_99 c c99).2
  have pC := P_C π ha hb hH' hC' excl exh
  have pHa := P_Ha π ha hb hH' hC' excl exh
  have pa := P_a π ha hb hH' hC' excl exh
  have pHb := P_Hb π ha hb hH' hC' excl exh
  have pb := P_b π ha hb hH' hC' excl exh
  obtain ⟨e1, _, e3, e4, e5, e6, e7, e8⟩ := arith22 _ _ _ _ _ _ _ _ _ _ _ q c c99 pC pHa pa
    l1 l2 l3 l4 l5 l6 l7 l8 hAB.1 hAB.2
  unfold Measure.cond
  exact ⟨e1, arith22a _ _ _ _ _ _ q c c99 hq0 pHa pa l1 l2 l3 l4,
    arith22b _ _ _ _ _ _ q c c99 hq1 pHb pb l5 l6 l7 l8, e3, e4, e5, e6, e7, e8⟩

end TagSwap2

/-! ## Section 7: the measures set against the proved one -/

theorem arithZeros (t x1 x2 x3 x4 x5 x6 x7 x8 v1 v3 v4 v6 v7 v8 : Rat)
    (s : t = x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) (ht : t = 1)
    (h1 : x1 = v1) (h3 : x3 = v3) (h4 : x4 = v4) (h6 : x6 = v6) (h7 : x7 = v7) (h8 : x8 = v8)
    (sum : v1 + v3 + v4 + v6 + v7 + v8 = 1) (p2 : 0 ≤ x2) (p5 : 0 ≤ x5) : x2 = 0 ∧ x5 = 0 := by
  grind

section LineMeasure

variable {Ω : Type} (m : Measure Ω) (H C a b : Ω → Prop)
  (hH : m.ev H) (hC : m.ev C) (ha : m.ev a) (hb : m.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
include hH hC ha hb excl exh

/-- If the six lines that hold a waking sum to 1, the two lines with no waking have 0. -/
theorem zero_lines {v1 v3 v4 v6 v7 v8 : Rat}
    (h1 : m.P (fun ω => a ω ∧ H ω ∧ C ω) = v1) (h3 : m.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = v3)
    (h4 : m.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = v4) (h6 : m.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = v6)
    (h7 : m.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = v7) (h8 : m.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = v8)
    (sum : v1 + v3 + v4 + v6 + v7 + v8 = 1) :
    m.P (fun ω => a ω ∧ H ω ∧ ¬ C ω) = 0 ∧ m.P (fun ω => b ω ∧ H ω ∧ C ω) = 0 :=
  arithZeros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P_true m ha hb hH hC excl exh) m.total h1 h3 h4 h6 h7
    h8 sum (m.nonneg (m.ev_and ha (m.ev_and hH (m.ev_not hC))))
    (m.nonneg (m.ev_and hb (m.ev_and hH hC)))

end LineMeasure

theorem arith16 (pH pC pa pb pHa pHb paC pHaC x1 x2 x3 x4 x5 x6 x7 x8 : Rat)
    (sH : pH = x1 + x2 + 0 + 0 + x5 + x6 + 0 + 0) (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0)
    (sa : pa = x1 + x2 + x3 + x4 + 0 + 0 + 0 + 0) (sb : pb = 0 + 0 + 0 + 0 + x5 + x6 + x7 + x8)
    (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0) (sHb : pHb = 0 + 0 + 0 + 0 + x5 + x6 + 0 + 0)
    (saC : paC = x1 + 0 + x3 + 0 + 0 + 0 + 0 + 0) (sHaC : pHaC = x1 + 0 + 0 + 0 + 0 + 0 + 0 + 0)
    (h1 : x1 = 1/4) (h6 : x6 = 1/4) (h3 : x3 = 1/8) (h4 : x4 = 1/8) (h7 : x7 = 1/8)
    (h8 : x8 = 1/8) (h2 : x2 = 0) (h5 : x5 = 0) :
    pH = 1/2 ∧ pC = 1/2 ∧ pa = 1/2 ∧ pb = 1/2 ∧ pHa / pa = 1/2 ∧ pHb / pb = 1/2 ∧
    pHaC / paC = 2/3 := by grind

theorem arith16d : (1:Rat)/2 ≠ (1/2)/(1+1/2) ∧ (1:Rat)/2 ≠ 1/3 ∧ (2:Rat)/3 ≠ 1/2 := by grind

section Halfers

variable {Ω : Type} (lam : Measure Ω) (H C a b : Ω → Prop)
  (hH : lam.ev H) (hC : lam.ev C) (ha : lam.ev a) (hb : lam.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (l1 : lam.P (fun ω => a ω ∧ H ω ∧ C ω) = 1/4) (l6 : lam.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = 1/4)
  (l3 : lam.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = 1/8)
  (l4 : lam.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = 1/8)
  (l7 : lam.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = 1/8)
  (l8 : lam.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = 1/8)
include hH hC ha hb excl exh l1 l6 l3 l4 l7 l8

/-- **(15)** is the definition of `λ` (the hypotheses `l1` to `l8` of this section), source lines
    844-848:
    ```
    \lambda(\ea\wedge H\wedge C)&=\lambda(\eb\wedge H\wedge\lnot C)=\quarter\\
    \lambda(\ea\wedge\lnot H\wedge C)&=\lambda(\ea\wedge\lnot H\wedge\lnot C)=\lambda(\eb\wedge\lnot H\wedge C)=\lambda(\eb\wedge\lnot H\wedge\lnot C)=\eighth.
    ```
    **(16)**, section 7.2, source lines 851-855:
    ```
    \lambda(H)=\lambda(C)=\half\qquad \lambda(\ea)=\lambda(\eb)=\half\qquad
    \lambda(H\mid \ea)=\lambda(H\mid \eb)=\half\qquad
    \lambda(H\mid \ea\wedge C)=\twothirds.
    ```
    "These values are sums of probabilities of the combinations in (15) and ratios of such sums."
    Choice: `λ` is any standard measure with the six values of (15), with `a`, `b` exclusive and
    exhaustive as sets; the two other combinations get 0 because the six sum to 1. -/
theorem display16 :
    lam.P H = 1/2 ∧ lam.P C = 1/2 ∧ lam.P a = 1/2 ∧ lam.P b = 1/2 ∧
    lam.cond H a = 1/2 ∧ lam.cond H b = 1/2 ∧ lam.cond H (fun ω => a ω ∧ C ω) = 2/3 := by
  obtain ⟨z2, z5⟩ := zero_lines lam H C a b hH hC ha hb excl exh l1 l3 l4 l6 l7 l8 (by grind)
  unfold Measure.cond
  exact arith16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P_H lam ha hb hH hC excl exh)
    (P_C lam ha hb hH hC excl exh) (P_a lam ha hb hH hC excl exh) (P_b lam ha hb hH hC excl exh)
    (P_Ha lam ha hb hH hC excl exh) (P_Hb lam ha hb hH hC excl exh)
    (P_aC lam ha hb hH hC excl exh) (P_HaC lam ha hb hH hC excl exh) l1 l6 l3 l4 l7 l8 z2 z5

/-- Where `λ` differs (section 7.2, source lines 857-869): `λ(H | a) = 1/2` is not the
    recording's `Pr(H | [M]) = 1/3`, so `λ` does not satisfy the construction at `a`; `λ(H) = 1/2`
    is not the proved 1/3 of (5); `λ(H | a ∧ C) = 2/3` is not the 1/2 of the tag-swapping lemma,
    (13) at the fair urn. Choice: `Pr` has the first assumption. -/
theorem display16_differs {Ω₀ : Type} (Pr : Measure Ω₀) (H₀ C₀ : Ω₀ → Prop) (hH₀ : Pr.ev H₀)
    (hC₀ : Pr.ev C₀) (coin : Pr.P H₀ = 1/2) (ball : Pr.P C₀ = 1/2)
    (indep : Pr.cond H₀ C₀ = Pr.P H₀) :
    lam.cond H a ≠ Pr.cond H₀ (M H₀ C₀) ∧ lam.P H ≠ 1/3 ∧
    lam.cond H (fun ω => a ω ∧ C ω) ≠ 1/2 := by
  obtain ⟨e1, _, _, _, e5, _, e7⟩ :=
    display16 lam H C a b hH hC ha hb excl exh l1 l6 l3 l4 l7 l8
  obtain ⟨_, _, _, _, m, _⟩ := display8 Pr H₀ C₀ hH₀ hC₀ (1/2) coin ball indep (by grind) (by grind)
  rw [e5, m, e1, e7]
  exact arith16d

end Halfers

theorem arith18M (n : Rat) (hn : 0 ≤ n) : (n+2)/(5*n+6) ≠ (n+2)/(3*n+4) := by
  intro h
  have h1 : (n+2)*(2*n+2) = 0 := by grind
  have h2 : 0 < (n+2)*(2*n+2) := Rat.mul_pos (by grind) (by grind)
  grind
theorem arith19a (n : Rat) (hn : 0 ≤ n) : (n+2)/(3*n+4) - 1/3 = 2/(3*(3*n+4)) := by grind
theorem arith19ne (n : Rat) (hn : 0 ≤ n) : (n+2)/(3*n+4) ≠ 1/3 := by grind
theorem arith21a (c ρ s : Rat) (hs : s = ρ*c + (1-ρ)*(1-c)) (hs0 : 0 ≤ s) :
    s/(1+s) = 1/3 ↔ s = 1/2 := by grind
theorem arith21b (c ρ s : Rat) (hs : s = ρ*c + (1-ρ)*(1-c)) :
    s = 1/2 ↔ (2*c-1)*(ρ-1/2) = 0 := by grind
theorem arith_sixths : (1:Rat)/6 + 1/6 + 1/6 + 1/6 + 1/6 + 1/6 = 1 := by grind

theorem arith17 (hc hnc pHa pHb x1 x2 x5 x6 : Rat)
    (sHC : hc = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0) (sHnC : hnc = 0 + x2 + 0 + 0 + 0 + x6 + 0 + 0)
    (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0) (sHb : pHb = 0 + 0 + 0 + 0 + x5 + x6 + 0 + 0)
    (z2 : x2 = 0) (z5 : x5 = 0) (q1 : hc = 1/4) (q2 : hnc = 1/4) :
    pHa = 1/4 ∧ pHb = 1/4 := by grind

theorem arith17b (pHa pHb pa pb : Rat) (e1 : pHa = 1/4) (e2 : pHb = 1/4) (s : pa + pb = 1)
    (t1 : pHa / pa = 1/3) (t2 : pHb / pb = 1/3) : pa = 3/4 ∧ pb = 3/4 ∧ False := by grind

section Kappa17

variable {Ω : Type} (κ : Measure Ω) (H C a b : Ω → Prop)
  (hH : κ.ev H) (hC : κ.ev C) (ha : κ.ev a) (hb : κ.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (only_a : κ.P (fun ω => b ω ∧ H ω ∧ C ω) = 0) (only_b : κ.P (fun ω => a ω ∧ H ω ∧ ¬ C ω) = 0)
  (q1 : κ.P (fun ω => H ω ∧ C ω) = 1/4) (q2 : κ.P (fun ω => H ω ∧ ¬ C ω) = 1/4)
  (q3 : κ.P (fun ω => ¬ H ω ∧ C ω) = 1/4) (q4 : κ.P (fun ω => ¬ H ω ∧ ¬ C ω) = 1/4)
include hH hC ha hb excl exh only_a only_b q1 q2 q3 q4

/-- **(17)**, section 7.2, source lines 862-865:
    ```
    \kappa(H\wedge C)=\kappa(H\wedge\lnot C)=\kappa(\lnot H\wedge C)=\kappa(\lnot H\wedge\lnot C)=\quarter,\text{ and so }
    \kappa(H\wedge \ea)=\kappa(H\wedge \eb)=\quarter.
    ```
    Choice: the first part is the definition of `κ` (hypotheses `q1` to `q4`); "by construction,
    if the outcome is `H ∧ C`, you could only be in `a`, and if `H ∧ ¬C`, `b`" is
    `κ(b ∧ H ∧ C) = κ(a ∧ H ∧ ¬C) = 0` (hypotheses `only_a`, `only_b`); `a`, `b` exclusive and
    exhaustive as sets. -/
theorem display17 : κ.P (fun ω => H ω ∧ a ω) = 1/4 ∧ κ.P (fun ω => H ω ∧ b ω) = 1/4 :=
  arith17 _ _ _ _ _ _ _ _ (P_HC κ ha hb hH hC excl exh)
    (P_HnC κ ha hb hH hC excl exh) (P_Ha κ ha hb hH hC excl exh) (P_Hb κ ha hb hH hC excl exh)
    only_b only_a q1 q2

/-- The sentence after (17), source line 867: if `κ` also gave heads 1/3 in each cell, `κ(a)` and
    `κ(b)` would both be 3/4, and they must sum to 1: no such `κ`. -/
theorem display17_no_third (t1 : κ.cond H a = 1/3) (t2 : κ.cond H b = 1/3) : False := by
  obtain ⟨e1, e2⟩ := display17 κ H C a b hH hC ha hb excl exh only_a only_b q1 q2 q3 q4
  unfold Measure.cond at t1 t2
  exact (arith17b _ _ _ _ e1 e2 (κ.part_sum ha hb excl exh) t1 t2).2.2

end Kappa17

/-! ### (18), (19): self-sampling with `N` outsiders -/

/-- The rule's share of a heads waking, `1/[4(N+1)]`, and of a tails waking, `1/[4(N+2)]`
    (source line 881), and their total over the six wakings, by which `μ_N` renormalizes. -/
def ssH (N : Nat) : Rat := 1/(4*((N:Rat)+1))
def ssT (N : Nat) : Rat := 1/(4*((N:Rat)+2))
def ssZ (N : Nat) : Rat := 2 * ssH N + 4 * ssT N

theorem ss1 (n : Rat) (hn : 0 ≤ n) (h t Z : Rat) (hh : h = 1/(4*(n+1))) (ht : t = 1/(4*(n+2)))
    (hZ : Z = 2*h+4*t) : Z = (3*n+4)/(2*(n+1)*(n+2)) := by grind
theorem ss2 (n : Rat) (hn : 0 ≤ n) (h Z : Rat) (hh : h = 1/(4*(n+1)))
    (hZ : Z = (3*n+4)/(2*(n+1)*(n+2))) : h/Z = (n+2)/(2*(3*n+4)) := by grind
theorem ss3 (n : Rat) (hn : 0 ≤ n) (t Z : Rat) (ht : t = 1/(4*(n+2)))
    (hZ : Z = (3*n+4)/(2*(n+1)*(n+2))) : t/Z = (n+1)/(2*(3*n+4)) := by grind
theorem ss4 (n : Rat) (hn : 0 ≤ n) : (2/(n+1))/(2/(n+1)+4/(n+2)) = (n+2)/(3*n+4) := by grind
theorem natcast_nonneg (N : Nat) : (0:Rat) ≤ (N:Rat) := by grind

theorem ss_vals (N : Nat) : ssH N / ssZ N = ((N:Rat)+2)/(2*(3*(N:Rat)+4)) ∧
    ssT N / ssZ N = ((N:Rat)+1)/(2*(3*(N:Rat)+4)) := by
  have hn := natcast_nonneg N
  have z := ss1 (N:Rat) hn (ssH N) (ssT N) (ssZ N) rfl rfl rfl
  exact ⟨ss2 (N:Rat) hn (ssH N) (ssZ N) rfl z, ss3 (N:Rat) hn (ssT N) (ssZ N) rfl z⟩

theorem arith18 (n pH pHa pa pHb pb pM pHM x1 x2 x3 x4 x5 x6 x7 x8 hz tz : Rat) (hn : 0 ≤ n)
    (ehz : hz = (n+2)/(2*(3*n+4))) (etz : tz = (n+1)/(2*(3*n+4)))
    (sH : pH = x1 + x2 + 0 + 0 + x5 + x6 + 0 + 0)
    (sa : pa = x1 + x2 + x3 + x4 + 0 + 0 + 0 + 0) (sb : pb = 0 + 0 + 0 + 0 + x5 + x6 + x7 + x8)
    (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0) (sHb : pHb = 0 + 0 + 0 + 0 + x5 + x6 + 0 + 0)
    (sM : pM = x1 + 0 + x3 + x4 + x5 + 0 + x7 + x8) (sHM : pHM = x1 + 0 + 0 + 0 + x5 + 0 + 0 + 0)
    (h1 : x1 = hz) (h6 : x6 = hz) (h3 : x3 = tz) (h4 : x4 = tz) (h7 : x7 = tz) (h8 : x8 = tz)
    (z2 : x2 = 0) (z5 : x5 = 0) :
    pH = (n+2)/(3*n+4) ∧ pHa / pa = (n+2)/(3*n+4) ∧ pHb / pb = (n+2)/(3*n+4) ∧
    pHM / pM = (n+2)/(5*n+6) := by grind

theorem arith_ss_sum (hz tz : Rat) (n : Rat) (hn : 0 ≤ n) (ehz : hz = (n+2)/(2*(3*n+4)))
    (etz : tz = (n+1)/(2*(3*n+4))) : hz + tz + tz + hz + tz + tz = 1 := by grind

section Outsiders

variable {Ω : Type} (μ : Measure Ω) (H C a b : Ω → Prop)
  (hH : μ.ev H) (hC : μ.ev C) (ha : μ.ev a) (hb : μ.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω) (N : Nat)
  (w1 : μ.P (fun ω => a ω ∧ H ω ∧ C ω) = ssH N / ssZ N)
  (w6 : μ.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = ssH N / ssZ N)
  (w3 : μ.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = ssT N / ssZ N)
  (w4 : μ.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = ssT N / ssZ N)
  (w7 : μ.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = ssT N / ssZ N)
  (w8 : μ.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = ssT N / ssZ N)
include hH hC ha hb excl exh w1 w6 w3 w4 w7 w8

/-- **(18)**, section 7.3, source lines 883-885:
    ```
    \mu_N(H)=\frac{2/(N+1)}{2/(N+1)+4/(N+2)}=\frac{N+2}{3N+4}\qquad
    \mu_N(H\mid \ea)=\mu_N(H\mid \eb)=\frac{N+2}{3N+4}
    ```
    Choice: `μ_N` is any standard measure that gives each of the two heads wakings
    (`a ∧ H ∧ C`, `b ∧ H ∧ ¬C`) `1/[4(N+1)]` and each of the four tails wakings `1/[4(N+2)]`,
    divided by their total (the renormalization); `a`, `b` exclusive and exhaustive as sets. -/
theorem display18 :
    μ.P H = (2/((N:Rat)+1))/(2/((N:Rat)+1)+4/((N:Rat)+2)) ∧
    (2/((N:Rat)+1))/(2/((N:Rat)+1)+4/((N:Rat)+2)) = ((N:Rat)+2)/(3*(N:Rat)+4) ∧
    μ.cond H a = ((N:Rat)+2)/(3*(N:Rat)+4) ∧ μ.cond H b = ((N:Rat)+2)/(3*(N:Rat)+4) := by
  obtain ⟨ehz, etz⟩ := ss_vals N
  have hn := natcast_nonneg N
  obtain ⟨z2, z5⟩ := zero_lines μ H C a b hH hC ha hb excl exh w1 w3 w4 w6 w7 w8
    (arith_ss_sum _ _ _ hn ehz etz)
  obtain ⟨e1, e2, e3, _⟩ := arith18 (N:Rat) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn ehz etz
    (P_H μ ha hb hH hC excl exh) (P_a μ ha hb hH hC excl exh) (P_b μ ha hb hH hC excl exh)
    (P_Ha μ ha hb hH hC excl exh) (P_Hb μ ha hb hH hC excl exh) (P_M μ ha hb hH hC excl exh)
    (P_HM μ ha hb hH hC excl exh) w1 w6 w3 w4 w7 w8 z2 z5
  unfold Measure.cond
  exact ⟨e1.trans (ss4 _ hn).symm, ss4 _ hn, e2, e3⟩

/-- Source line 896: with the self-sampler's values in place of the recording's,
    `μ_N(H | [M]) = (N+2)/(5N+6)`, and it differs from the cell value `μ_N(H | a)` at every `N`. -/
theorem display18_M :
    μ.cond H (M H C) = ((N:Rat)+2)/(5*(N:Rat)+6) ∧ μ.cond H (M H C) ≠ μ.cond H a := by
  obtain ⟨ehz, etz⟩ := ss_vals N
  have hn := natcast_nonneg N
  obtain ⟨z2, z5⟩ := zero_lines μ H C a b hH hC ha hb excl exh w1 w3 w4 w6 w7 w8
    (arith_ss_sum _ _ _ hn ehz etz)
  obtain ⟨_, _, _, e4⟩ := arith18 (N:Rat) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn ehz etz
    (P_H μ ha hb hH hC excl exh) (P_a μ ha hb hH hC excl exh) (P_b μ ha hb hH hC excl exh)
    (P_Ha μ ha hb hH hC excl exh) (P_Hb μ ha hb hH hC excl exh) (P_M μ ha hb hH hC excl exh)
    (P_HM μ ha hb hH hC excl exh) w1 w6 w3 w4 w7 w8 z2 z5
  obtain ⟨_, _, e2, _⟩ := display18 μ H C a b hH hC ha hb excl exh N w1 w6 w3 w4 w7 w8
  unfold Measure.cond at e2 ⊢
  rw [e4, e2]; exact ⟨rfl, arith18M _ hn⟩

end Outsiders

/-- **(19)**, section 7.3, source lines 888-890:
    ```
    \frac{N+2}{3N+4}-\third=\frac{2}{3(3N+4)}>0.
    ```
    with the sentence after it: the value is 1/2 at `N = 0` and 2/5 at `N = 2`. -/
theorem display19 (N : Nat) :
    ((N:Rat)+2)/(3*(N:Rat)+4) - 1/3 = 2/(3*(3*(N:Rat)+4)) ∧ 0 < 2/(3*(3*(N:Rat)+4)) := by
  have hn := natcast_nonneg N
  exact ⟨arith19a _ hn, pos_div _ _ (by grind) (by grind)⟩

theorem display19_values : ((0:Nat):Rat) = 0 ∧ ((0:Rat)+2)/(3*0+4) = 1/2 ∧
    ((2:Rat)+2)/(3*2+4) = 2/5 := by grind

/-- (19) applied (source line 892): at every finite `N`, `μ_N(H | a)` differs from
    `Pr(H | [M]) = 1/3`, the value the construction requires. -/
theorem display19_differs {Ω : Type} (μ : Measure Ω) (H C a b : Ω → Prop)
    (hH : μ.ev H) (hC : μ.ev C) (ha : μ.ev a) (hb : μ.ev b)
    (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω) (N : Nat)
    (w1 : μ.P (fun ω => a ω ∧ H ω ∧ C ω) = ssH N / ssZ N)
    (w6 : μ.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = ssH N / ssZ N)
    (w3 : μ.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = ssT N / ssZ N)
    (w4 : μ.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = ssT N / ssZ N)
    (w7 : μ.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = ssT N / ssZ N)
    (w8 : μ.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = ssT N / ssZ N) :
    μ.cond H a ≠ 1/3 := by
  obtain ⟨_, _, e, _⟩ := display18 μ H C a b hH hC ha hb excl exh N w1 w6 w3 w4 w7 w8
  rw [e]; exact arith19ne _ (natcast_nonneg N)

/-! ### (20): the Doomsday division -/

theorem arith20 (pS pL π pSr pLr NS NL : Rat) (hS : 0 < pS) (hL : 0 < pL) (hr : π ≠ 0)
    (hNS : 0 < NS) (hNL : 0 < NL) (cS : pSr / pS = 1/NS) (cL : pLr / pL = 1/NL) :
    (pSr / π) / (pLr / π) = pS / pL * (NL / NS) := by grind

theorem arith20b (pS pL NS NL : Rat) (hS : 0 < pS) (hL : 0 < pL) (hNS : 0 < NS) (lt : NS < NL) :
    pS / pL * (NL / NS) > pS / pL := by
  have h1 : 0 < pS / pL := pos_div _ _ hS hL
  have h2 : 1 < NL / NS := by
    have : NL / NS - 1 = (NL - NS) / NS := by grind
    have : 0 < (NL - NS) / NS := pos_div _ _ (by grind) hNS
    grind
  have h3 : 0 < (pS / pL) * (NL / NS - 1) := Rat.mul_pos h1 (by grind)
  grind

/-- **(20)**, section 7.3, source lines 903-905:
    ```
    \frac{\mu(S\mid r)}{\mu(L\mid r)}=\frac{\mu(S)}{\mu(L)}\cdot\frac{N_L}{N_S}
    ```
    Choice: "by self-sampling, the known birth rank `r` is one of the `N_S` positions under `S`
    and one of the `N_L` positions under `L`, uniformly" is `μ(r | S) = 1/N_S`,
    `μ(r | L) = 1/N_L`; positive priors; `μ(r) ≠ 0`. With the sentence after it: since
    `N_L > N_S`, the ratio is raised. -/
theorem display20 {Ω : Type} (μ : Measure Ω) (S L r : Ω → Prop) (NS NL : Rat)
    (hS : 0 < μ.P S) (hL : 0 < μ.P L) (hr : μ.P r ≠ 0) (hNS : 0 < NS) (hNL : 0 < NL)
    (rankS : μ.cond r S = 1/NS) (rankL : μ.cond r L = 1/NL) :
    μ.cond S r / μ.cond L r = μ.P S / μ.P L * (NL / NS) ∧
    (NS < NL → μ.cond S r / μ.cond L r > μ.P S / μ.P L) := by
  have eS : μ.P (fun ω => S ω ∧ r ω) = μ.P (fun ω => r ω ∧ S ω) := μ.Pcongr (fun ω => by grind)
  have eL : μ.P (fun ω => L ω ∧ r ω) = μ.P (fun ω => r ω ∧ L ω) := μ.Pcongr (fun ω => by grind)
  unfold Measure.cond at *
  rw [eS, eL]
  have k := arith20 _ _ _ _ _ _ _ hS hL hr hNS hNL rankS rankL
  refine ⟨k, fun lt => ?_⟩
  rw [k]; exact arith20b _ _ _ _ hS hL hNS lt

/-! ### (21): the temporal prior -/

theorem arith21 (pH pD pHD pHnD pnD pnDnH pW pHW ρ : Rat) (coin : pH = 1/2) (hD : pD = ρ)
    (indep : pHD / pD = pH) (s1 : pH = pHD + pHnD) (s2 : pnD = pHnD + pnDnH) (cc : pD + pnD = 1)
    (dW : pW = pD + pnDnH) (eHW : pHW = pHD) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    pHW = ρ * (1/2) ∧ pW = ρ + (1-ρ)/2 ∧ pHW / pW = (ρ/2)/(ρ + (1-ρ)/2) ∧
    (ρ/2)/(ρ + (1-ρ)/2) = ρ/(1+ρ) ∧ (ρ/(1+ρ) = 1/3 ↔ ρ = 1/2) := by grind

/-- **(21)**, section 7.5, source lines 930-933:
    ```
    \mu_\rho(H\mid W)=\frac{\rho/2}{\rho+(1-\rho)/2}=\frac{\rho}{1+\rho}\qquad
    \mu_\rho(H\mid W)=\third\ \text{ iff }\ \rho=\half.
    ```
    with the line after it: "`H ∧ W` has `ρ·1/2`. `W` has `ρ + (1-ρ)/2`."
    Choice: `D` is the Monday clock-time, `μ(D) = ρ` with `0 < ρ ≤ 1` (at `ρ = 0` the independence
    ratio has no value), independent of the fair coin; in the Monday-only urn `W` is `D`, or not
    `D` and tails ("W is certain on Monday and is ¬H on Tuesday"). -/
theorem display21 {Ω : Type} (μ : Measure Ω) (H D : Ω → Prop) (hH : μ.ev H) (hD : μ.ev D)
    (ρ : Rat) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (coin : μ.P H = 1/2) (prior : μ.P D = ρ)
    (indep : μ.cond H D = μ.P H) :
    μ.P (fun ω => H ω ∧ (D ω ∨ (¬ D ω ∧ ¬ H ω))) = ρ * (1/2) ∧
    μ.P (fun ω => D ω ∨ (¬ D ω ∧ ¬ H ω)) = ρ + (1-ρ)/2 ∧
    μ.cond H (fun ω => D ω ∨ (¬ D ω ∧ ¬ H ω)) = (ρ/2)/(ρ + (1-ρ)/2) ∧
    (ρ/2)/(ρ + (1-ρ)/2) = ρ/(1+ρ) ∧ (ρ/(1+ρ) = 1/3 ↔ ρ = 1/2) := by
  have s1 := μ.split hH hD
  have s2 := μ.split (μ.ev_not hD) hH
  have cc := μ.compl hD
  have dW := μ.add hD (μ.ev_and (μ.ev_not hD) (μ.ev_not hH)) (fun ω h => h.2.1 h.1)
  have e1 : μ.P (fun ω => ¬ D ω ∧ H ω) = μ.P (fun ω => H ω ∧ ¬ D ω) := μ.Pcongr (fun ω => by grind)
  have eHW : μ.P (fun ω => H ω ∧ (D ω ∨ (¬ D ω ∧ ¬ H ω))) = μ.P (fun ω => H ω ∧ D ω) :=
    μ.Pcongr (fun ω => by grind)
  rw [e1] at s2
  unfold Measure.cond at *
  exact arith21 _ _ _ _ _ _ _ _ ρ coin prior indep s1 s2 cc dW eHW hρ0 hρ1

/-- Source line 939, the uneven urn: with `s = ρc + (1-ρ)(1-c)` the rule gives heads `s/(1+s)`,
    which is 1/3 iff `(2c-1)(ρ-1/2) = 0`; at `c = 1/3`, `ρ = 1` gives a quarter. -/
theorem display21_uneven (c ρ : Rat) (hs0 : 0 ≤ ρ*c + (1-ρ)*(1-c)) :
    ((ρ*c + (1-ρ)*(1-c))/(1 + (ρ*c + (1-ρ)*(1-c))) = 1/3 ↔ (2*c-1)*(ρ-1/2) = 0) ∧
    (c = 1/3 → ρ = 1 → (ρ*c + (1-ρ)*(1-c))/(1 + (ρ*c + (1-ρ)*(1-c))) = 1/4) := by
  refine ⟨?_, fun h1 h2 => by subst h1; subst h2; grind⟩
  exact (arith21a c ρ _ rfl hs0).trans (arith21b c ρ _ rfl)

/-! ### (22): the measure `ν` that gives the six wakings the same probability -/

theorem arith22nu (pC pHa pa pHb pb x1 x2 x3 x4 x5 x6 x7 x8 : Rat)
    (sC : pC = x1 + 0 + x3 + 0 + x5 + 0 + x7 + 0) (sHa : pHa = x1 + x2 + 0 + 0 + 0 + 0 + 0 + 0)
    (sa : pa = x1 + x2 + x3 + x4 + 0 + 0 + 0 + 0) (sHb : pHb = 0 + 0 + 0 + 0 + x5 + x6 + 0 + 0)
    (sb : pb = 0 + 0 + 0 + 0 + x5 + x6 + x7 + x8)
    (h1 : x1 = 1/6) (h3 : x3 = 1/6) (h4 : x4 = 1/6) (h6 : x6 = 1/6) (h7 : x7 = 1/6)
    (h8 : x8 = 1/6) (z2 : x2 = 0) (z5 : x5 = 0) :
    pC = 1/2 ∧ pHa / pa = 1/3 ∧ pHb / pb = 1/3 := by grind

/-- **(22)**, first line, section 8.5, source line 1060:
    ```
    \nu(C)=\half\qquad \nu(H\mid\ea)=\third\qquad \nu(H\mid\eb)=\third\\
    ```
    Choice: `ν` is any standard measure giving the six wakings (the six lines of (24)) 1/6 each;
    `a`, `b` exclusive and exhaustive as sets. Your values beside it: `display22_yours`. -/
theorem display22_nu {Ω : Type} (ν : Measure Ω) (H C a b : Ω → Prop)
    (hH : ν.ev H) (hC : ν.ev C) (ha : ν.ev a) (hb : ν.ev b)
    (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
    (w1 : ν.P (fun ω => a ω ∧ H ω ∧ C ω) = 1/6) (w3 : ν.P (fun ω => a ω ∧ ¬ H ω ∧ C ω) = 1/6)
    (w4 : ν.P (fun ω => a ω ∧ ¬ H ω ∧ ¬ C ω) = 1/6)
    (w6 : ν.P (fun ω => b ω ∧ H ω ∧ ¬ C ω) = 1/6)
    (w7 : ν.P (fun ω => b ω ∧ ¬ H ω ∧ C ω) = 1/6)
    (w8 : ν.P (fun ω => b ω ∧ ¬ H ω ∧ ¬ C ω) = 1/6) :
    ν.P C = 1/2 ∧ ν.cond H a = 1/3 ∧ ν.cond H b = 1/3 := by
  obtain ⟨z2, z5⟩ := zero_lines ν H C a b hH hC ha hb excl exh w1 w3 w4 w6 w7 w8 arith_sixths
  unfold Measure.cond
  exact arith22nu _ _ _ _ _ _ _ _ _ _ _ _ _ (P_C ν ha hb hH hC excl exh)
    (P_Ha ν ha hb hH hC excl exh) (P_a ν ha hb hH hC excl exh) (P_Hb ν ha hb hH hC excl exh)
    (P_b ν ha hb hH hC excl exh) w1 w3 w4 w6 w7 w8 z2 z5

theorem arithOne (r : Rat) : r * 1 = r := by grind
theorem arithAssoc (x y z : Rat) : x + (y + z) = x + y + z := by grind
theorem half_ne_zero : (1:Rat)/2 ≠ 0 := by grind
theorem arithSelf (x : Rat) (h : x ≠ 0) : x / x = 1 := by grind
theorem arithSum3 (a b c : Rat) (h : 1 = a*1 + b*1 + c*1) : a + b + c = 1 := by grind
theorem arithM1 (q : Rat) (h : 0 ≤ q*1) : 0 ≤ q := by grind

/-! ## Section 4: (6) and (7) -/

theorem arith6 (pH pnH x : Rat) (c : pH + pnH = 1) (five : pH = 1/3) :
    pH * (1-x) - pnH * x = pH - x ∧ (pH * (1-x) - pnH * x = 0 ↔ x = 1/3) := by grind

/-- **(6)**, section 4, source lines 427-430:
    ```
    x=\third.
    ```
    with the sentence before it: "At a price `x` the ticket is worth
    `π(H)(1-x) - π(¬H)x = π(H) - x`, so the price at which you take either side is `π(H)`."
    Choice: the price at which you take either side is the `x` at which the ticket is worth 0;
    `π(H) = 1/3` is (5). -/
theorem display6 {Ω : Type} (π : Measure Ω) (H : Ω → Prop) (hH : π.ev H)
    (five : π.P H = 1/3) (x : Rat) :
    π.P H * (1-x) - π.P (fun ω => ¬ H ω) * x = π.P H - x ∧
    (π.P H * (1-x) - π.P (fun ω => ¬ H ω) * x = 0 ↔ x = 1/3) :=
  arith6 _ _ x (π.compl hH) five

/-- Section 4, source line 433 (the text before (7)): `V(buy) = g(1-x) - (1-g)2x` is 0 at
    `x = g/(2-g)`, which at `g = 1/3` is 1/5; `V(sell)` is its negation. -/
theorem edt_price (g x : Rat) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (g*(1-x) - (1-g)*(2*x) = 0 ↔ x = g/(2-g)) ∧ (1-g)*(2*x) - g*(1-x) = -(g*(1-x) - (1-g)*(2*x)) ∧
    (1:Rat)/3/(2-1/3) = 1/5 := by grind

/-- **(7)**, section 4, source lines 434-436:
    ```
    \frac{g}{2-g}=\third\quad\text{iff}\quad g=\half.
    ```
    Choice: `g` is a probability, `0 ≤ g ≤ 1`. -/
theorem display7 (g : Rat) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : g/(2-g) = 1/3 ↔ g = 1/2 := by grind

theorem arith7c (g pH : Rat) (e : pH = g) (h : g/(2-g) = 1/3) (hg1 : g ≤ 1) (five : pH = 1/3) :
    False := by grind

/-- The sentence after (7), source lines 438-440: `g` is the same given either act, so by Sure
    Thing it is `π(H)`; EDT's price 1/3 then needs `π(H) = 1/2`, which contradicts (5).
    Choice: the two acts `buy`, `sell` are exclusive and exhaustive as sets, each with positive
    value, and `π(H | buy) = π(H | sell) = g`. -/
theorem display7_contradicts_five {Ω : Type} (π : Measure Ω) (H buy sell : Ω → Prop)
    (hH : π.ev H) (hbuy : π.ev buy) (hsell : π.ev sell)
    (excl : ∀ ω, ¬ (buy ω ∧ sell ω)) (exh : ∀ ω, buy ω ∨ sell ω)
    (pos1 : π.P buy ≠ 0) (pos2 : π.P sell ≠ 0) (g : Rat) (hg1 : g ≤ 1)
    (gb : π.cond H buy = g) (gs : π.cond H sell = g) (price : g/(2-g) = 1/3)
    (five : π.P H = 1/3) : False :=
  arith7c g _ (π.sure_thing_cells hH hbuy hsell pos1 pos2 gb gs (π.part_and excl)
    (π.part_or exh)) price hg1 five

/-! ## (25), and Sure Thing for a finite partition of `n` cells (end of section 1.3) -/

/-- The disjunction of a list of events. -/
def orL {Ω : Type} : List (Ω → Prop) → Ω → Prop
  | [] => fun _ => False
  | B :: Bs => fun ω => B ω ∨ orL Bs ω

theorem arithCons (x y r a b : Rat) (h1 : x = r * a) (h2 : y = r * b) : x + y = r * (a + b) := by
  grind
theorem arithNil (r : Rat) : (0:Rat) = r * 0 := by grind
theorem arithProd (pX pXB pB r : Rat) (hB : pB ≠ 0) (h : pXB / pB = r) : pXB = r * pB := by grind
theorem arithEnd (pX x y por pnor r : Rat) (s : pX = x + y) (hx : x = r * por) (n : y ≤ pnor)
    (p : 0 ≤ y) (c : por + pnor = 1) (h : por = 1) : pX = r := by grind

namespace Measure

variable {Ω : Type} (m : Measure Ω)

theorem ev_false : m.ev (fun _ => False) := by
  have h := m.ev_not m.ev_true
  have e : (fun (_ : Ω) => ¬ True) = (fun _ => False) := by funext ω; simp
  rw [e] at h; exact h

theorem ev_orL (Bs : List (Ω → Prop)) (hBs : ∀ B ∈ Bs, m.ev B) : m.ev (orL Bs) := by
  induction Bs with
  | nil => exact m.ev_false
  | cons B Bs ih =>
    exact m.ev_or (hBs B (List.mem_cons_self ..))
      (ih (fun A hA => hBs A (List.mem_cons_of_mem _ hA)))

theorem disj_orL (B : Ω → Prop) (Bs : List (Ω → Prop))
    (h : ∀ A ∈ Bs, ∀ ω, ¬ (B ω ∧ A ω)) : ∀ ω, ¬ (B ω ∧ orL Bs ω) := by
  induction Bs with
  | nil => intro ω k; exact k.2
  | cons A Bs ih =>
    intro ω k
    cases k.2 with
    | inl x => exact h A (List.mem_cons_self ..) ω ⟨k.1, x⟩
    | inr x => exact ih (fun A' hA' => h A' (List.mem_cons_of_mem _ hA')) ω ⟨k.1, x⟩

/-- In product form, cell by cell: `π(X ∧ (B₁ ∨ … ∨ Bₙ)) = r π(B₁ ∨ … ∨ Bₙ)` and
    `π(B₁ ∨ … ∨ Bₙ) = Σ π(Bᵢ)`. -/
theorem prod_orL {X : Ω → Prop} (hX : m.ev X) (r : Rat) (Bs : List (Ω → Prop))
    (hBs : ∀ B ∈ Bs, m.ev B) (disj : List.Pairwise (fun A B => ∀ ω, ¬ (A ω ∧ B ω)) Bs)
    (prod : ∀ B ∈ Bs, m.P (fun ω => X ω ∧ B ω) = r * m.P B) :
    m.P (fun ω => X ω ∧ orL Bs ω) = r * m.P (orL Bs) ∧
    m.P (orL Bs) = (Bs.map m.P).sum ∧
    (Bs.map (fun B => r * m.P B)).sum = r * (Bs.map m.P).sum := by
  induction Bs with
  | nil =>
    have e : m.P (fun ω => X ω ∧ orL [] ω) = 0 := by
      rw [m.Pcongr (B := fun _ => False) (fun ω => ⟨fun k => k.2, fun k => k.elim⟩)]
      exact m.P_false
    have e2 : m.P (orL ([] : List (Ω → Prop))) = 0 := m.P_false
    refine ⟨?_, ?_, ?_⟩
    · rw [e, e2]; exact arithNil r
    · rw [e2]; rfl
    · simp only [List.map_nil, List.sum_nil]; exact arithNil r
  | cons B Bs ih =>
    obtain ⟨d1, d2⟩ := List.pairwise_cons.mp disj
    have hB := hBs B (List.mem_cons_self ..)
    have hBs' : ∀ A ∈ Bs, m.ev A := fun A hA => hBs A (List.mem_cons_of_mem _ hA)
    obtain ⟨i1, i2, i3⟩ := ih hBs' d2 (fun A hA => prod A (List.mem_cons_of_mem _ hA))
    have dj := disj_orL B Bs d1
    have aX := m.add (m.ev_and hX hB) (m.ev_and hX (m.ev_orL Bs hBs'))
      (fun ω k => dj ω ⟨k.1.2, k.2.2⟩)
    have aB := m.add hB (m.ev_orL Bs hBs') dj
    have eX : m.P (fun ω => X ω ∧ orL (B :: Bs) ω)
        = m.P (fun ω => (X ω ∧ B ω) ∨ (X ω ∧ orL Bs ω)) :=
      m.Pcongr (fun ω => by simp only [orL]; grind)
    have eB : m.P (orL (B :: Bs)) = m.P (fun ω => B ω ∨ orL Bs ω) := rfl
    have pB := prod B (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · rw [eX, aX, eB, aB, pB, i1]; exact arithCons _ _ r _ _ rfl rfl
    · rw [eB, aB, i2]; simp only [List.map_cons, List.sum_cons]
    · simp only [List.map_cons, List.sum_cons]; rw [i3]; exact arithCons _ _ r _ _ rfl rfl

end Measure

/-- **(25)**, section 11 (beyond measure), source lines 1202-1205:
    ```
    \prsb(X\wedge B_i)=r\,\prsb(B_i)\text{ for every cell }B_i\text{ of a finite partition}\ \models\
    \prsb(X)=\sum_i r\,\prsb(B_i)=r.
    ```
    Choice: the partition is a list of events, exclusive as sets (pairwise), exhaustive in the
    measure, `π(B₁ ∨ … ∨ Bₙ) = 1`. -/
theorem display25 {Ω : Type} (m : Measure Ω) {X : Ω → Prop} (hX : m.ev X) (r : Rat)
    (Bs : List (Ω → Prop)) (hBs : ∀ B ∈ Bs, m.ev B)
    (disj : List.Pairwise (fun A B => ∀ ω, ¬ (A ω ∧ B ω)) Bs) (exhaust : m.P (orL Bs) = 1)
    (prod : ∀ B ∈ Bs, m.P (fun ω => X ω ∧ B ω) = r * m.P B) :
    m.P X = (Bs.map (fun B => r * m.P B)).sum ∧ (Bs.map (fun B => r * m.P B)).sum = r := by
  obtain ⟨p1, p2, p3⟩ := m.prod_orL hX r Bs hBs disj prod
  have hO := m.ev_orL Bs hBs
  have s := m.split hX hO
  have c := m.compl hO
  have n : m.P (fun ω => X ω ∧ ¬ orL Bs ω) ≤ m.P (fun ω => ¬ orL Bs ω) :=
    m.mono (m.ev_and hX (m.ev_not hO)) (m.ev_not hO) (fun ω k => k.2)
  have p := m.nonneg (m.ev_and hX (m.ev_not hO))
  have hXr : m.P X = r := arithEnd _ _ _ _ _ r s p1 n p c exhaust
  have hsum : (Bs.map (fun B => r * m.P B)).sum = r := by
    rw [p3, ← p2, exhaust]; exact arithOne r
  exact ⟨hXr.trans hsum.symm, hsum⟩

/-- **Sure Thing for a finite partition** (section 1.3, source line 263):
    "for a finite partition `B₁, …, Bₙ`: `π(X | Bᵢ) = r` for every `i` ⊨ `π(X) = r`."
    Choice: as in (25); each conditional probability is defined, `π(Bᵢ) ≠ 0`. -/
theorem sure_thing_n {Ω : Type} (m : Measure Ω) {X : Ω → Prop} (hX : m.ev X) (r : Rat)
    (Bs : List (Ω → Prop)) (hBs : ∀ B ∈ Bs, m.ev B)
    (disj : List.Pairwise (fun A B => ∀ ω, ¬ (A ω ∧ B ω)) Bs) (exhaust : m.P (orL Bs) = 1)
    (pos : ∀ B ∈ Bs, m.P B ≠ 0) (ratio : ∀ B ∈ Bs, m.cond X B = r) : m.P X = r := by
  have prod : ∀ B ∈ Bs, m.P (fun ω => X ω ∧ B ω) = r * m.P B := by
    intro B hB
    have h := ratio B hB
    unfold Measure.cond at h
    exact arithProd 0 _ _ r (pos B hB) h
  exact ((display25 m hX r Bs hBs disj exhaust prod).1).trans
    (display25 m hX r Bs hBs disj exhaust prod).2

/-! ## Appendix A: the start day randomized, (A1) to (A4) -/

theorem arithA1 (hs pT hT pW hW : Rat) (o1 : hs = 1/2/2) (cT : hs + pT = 1) (eT : hT = (1-1/2)/2)
    (eW : hW = 0) : hT / pT = 1/3 ∧ hW / pW = 0 := by grind

/-- **(A1)**, Appendix A, source lines 1234-1238:
    ```
    \hear{M}=S\qquad \hear{T}=\lnot S\vee\lnot H\qquad \hear{W}=\lnot H\wedge\lnot S\\
    \prany(H\mid\hear{M})=\half\qquad \prany(H\mid\hear{T})=\third\qquad \prany(H\mid\hear{W})=0.
    ```
    Choice: the first line is taken as the definitions of the three receptions; `Pr(H) = 1/2`,
    `Pr(S) = 1/2` and independence, as the text before (A1) ("the four outcomes ... have 1/4
    each"). -/
theorem displayA1 {Ω : Type} (Pr : Measure Ω) (H S : Ω → Prop) (hH : Pr.ev H) (hS : Pr.ev S)
    (coin : Pr.P H = 1/2) (start : Pr.P S = 1/2) (indep : Pr.cond H S = Pr.P H) :
    Pr.cond H S = 1/2 ∧ Pr.cond H (fun ω => ¬ S ω ∨ ¬ H ω) = 1/3 ∧
    Pr.cond H (fun ω => ¬ H ω ∧ ¬ S ω) = 0 := by
  obtain ⟨o1, _, o2, _, _, _, _⟩ := rec_values Pr H S hH hS (1/2) coin start indep (by grind)
  have cT := Pr.compl (Pr.ev_and hH hS)
  have eT' : Pr.P (fun ω => ¬ (H ω ∧ S ω)) = Pr.P (fun ω => ¬ S ω ∨ ¬ H ω) :=
    Pr.Pcongr (fun ω => by grind)
  have eT : Pr.P (fun ω => H ω ∧ (¬ S ω ∨ ¬ H ω)) = Pr.P (fun ω => H ω ∧ ¬ S ω) :=
    Pr.Pcongr (fun ω => by grind)
  have eW : Pr.P (fun ω => H ω ∧ (¬ H ω ∧ ¬ S ω)) = 0 := by
    rw [Pr.Pcongr (B := fun _ => False) (fun ω => by grind)]; exact Pr.P_false
  rw [eT'] at cT
  rw [o2] at eT
  unfold Measure.cond
  obtain ⟨a1, a2⟩ := arithA1 _ _ _ (Pr.P (fun ω => ¬ H ω ∧ ¬ S ω)) _ o1 cT eT eW
  refine ⟨?_, a1, a2⟩
  unfold Measure.cond at indep; rw [indep, coin]

theorem arithA3f (pH x1 x2 x3 qM qT qW : Rat) (s : pH = x1 + x2 + x3) (h1 : x1 = qM * (1/2))
    (h2 : x2 = qT * (1/3)) (h3 : x3 = qW * 0) (sum : qM + qT + qW = 1) (p1 : 0 ≤ qM)
    (p2 : 0 ≤ qT) (p3 : 0 ≤ qW) (h : pH = 1/2) : qM = 1 := by
  have k : 3 * qM + 2 * qT = 3 := by grind
  clear s h1 h2 h3 h
  grind

theorem arithA3b (pH x1 x2 x3 qM qT qW : Rat) (s : pH = x1 + x2 + x3) (h1 : x1 = qM * (1/2))
    (h2 : x2 = qT * (1/3)) (h3 : x3 = qW * 0) (sum : qM + qT + qW = 1) (p1 : 0 ≤ qM)
    (p2 : 0 ≤ qT) (p3 : 0 ≤ qW) (h : qM = 1) : pH = 1/2 := by grind

theorem arithA3 (pH x1 x2 x3 qM qT qW : Rat) (s : pH = x1 + x2 + x3) (h1 : x1 = qM * (1/2))
    (h2 : x2 = qT * (1/3)) (h3 : x3 = qW * 0) (sum : qM + qT + qW = 1) (p1 : 0 ≤ qM)
    (p2 : 0 ≤ qT) (p3 : 0 ≤ qW) :
    pH = (1/2)*qM + (1/3)*qT ∧ (1/2)*qM + (1/3)*qT ≤ 1/3 + qM/6 ∧ 1/3 + qM/6 ≤ 1/2 ∧
    (pH = 1/2 ↔ qM = 1) :=
  ⟨by grind, by grind, by grind, ⟨arithA3f pH x1 x2 x3 qM qT qW s h1 h2 h3 sum p1 p2 p3,
    arithA3b pH x1 x2 x3 qM qT qW s h1 h2 h3 sum p1 p2 p3⟩⟩

theorem arithA2 (pT qD v : Rat) (h1 : pT = qD * v) (hv : v = 1) : pT = qD := by grind

/-- Three exclusive and exhaustive cells: every event is the sum of its parts in them. -/
theorem split3 {Ω : Type} (m : Measure Ω) {X a1 a2 a3 : Ω → Prop} (hX : m.ev X)
    (h1 : m.ev a1) (h2 : m.ev a2) (h3 : m.ev a3) (e12 : ∀ ω, ¬ (a1 ω ∧ a2 ω))
    (e13 : ∀ ω, ¬ (a1 ω ∧ a3 ω)) (e23 : ∀ ω, ¬ (a2 ω ∧ a3 ω))
    (exh : ∀ ω, a1 ω ∨ a2 ω ∨ a3 ω) :
    m.P X = m.P (fun ω => X ω ∧ a1 ω) + m.P (fun ω => X ω ∧ a2 ω) + m.P (fun ω => X ω ∧ a3 ω) := by
  have s := m.split_cells hX h1 (m.ev_or h2 h3) (fun ω k => k.2.elim (fun x => e12 ω ⟨k.1, x⟩)
    (fun x => e13 ω ⟨k.1, x⟩)) exh
  have a := m.add (m.ev_and hX h2) (m.ev_and hX h3) (fun ω k => e23 ω ⟨k.1.2, k.2.2⟩)
  have e : m.P (fun ω => X ω ∧ (a2 ω ∨ a3 ω))
      = m.P (fun ω => (X ω ∧ a2 ω) ∨ (X ω ∧ a3 ω)) := m.Pcongr (fun ω => by grind)
  rw [e, a] at s
  exact s.trans (arithAssoc _ _ _)

/-- **(A2)**, Appendix A, source lines 1244-1246, is the construction for the three cases, and
    **(A3)**, source lines 1249-1251:
    ```
    \prsb(X\wedge \ea_D)=q_D\,\prany(X\mid\hear{D})\qquad D\in\{M,T,W\}.        (A2)
    \prsb(H)=\half q_M+\third q_T\le\third+\frac{q_M}{6}\le\half\qquad \prsb(H)=\half\ \text{ iff }\ q_M=1.   (A3)
    ```
    Choice: (A2) is assumed at `X = H` and at the sure event `X = ⊤` (which makes `q_D = π(a_D)`);
    the three cases are exclusive and exhaustive as sets; `Pr` as in (A1); `H'` is `H` in your
    measure. -/
theorem displayA3 {Ω Ω' : Type} (Pr : Measure Ω) (H S : Ω → Prop) (hH : Pr.ev H) (hS : Pr.ev S)
    (coin : Pr.P H = 1/2) (start : Pr.P S = 1/2) (indep : Pr.cond H S = Pr.P H)
    (π : Measure Ω') (H' aM aT aW : Ω' → Prop) (hH' : π.ev H') (haM : π.ev aM)
    (haT : π.ev aT) (haW : π.ev aW) (eMT : ∀ ω, ¬ (aM ω ∧ aT ω)) (eMW : ∀ ω, ¬ (aM ω ∧ aW ω))
    (eTW : ∀ ω, ¬ (aT ω ∧ aW ω)) (exh : ∀ ω, aM ω ∨ aT ω ∨ aW ω) (qM qT qW : Rat)
    (A2M : π.P (fun ω => H' ω ∧ aM ω) = qM * Pr.cond H S)
    (A2T : π.P (fun ω => H' ω ∧ aT ω) = qT * Pr.cond H (fun ω => ¬ S ω ∨ ¬ H ω))
    (A2W : π.P (fun ω => H' ω ∧ aW ω) = qW * Pr.cond H (fun ω => ¬ H ω ∧ ¬ S ω))
    (A2M' : π.P (fun ω => True ∧ aM ω) = qM * Pr.cond (fun _ => True) S)
    (A2T' : π.P (fun ω => True ∧ aT ω) = qT * Pr.cond (fun _ => True) (fun ω => ¬ S ω ∨ ¬ H ω))
    (A2W' : π.P (fun ω => True ∧ aW ω) = qW * Pr.cond (fun _ => True) (fun ω => ¬ H ω ∧ ¬ S ω))
    (posT : Pr.P (fun ω => ¬ S ω ∨ ¬ H ω) ≠ 0) (posW : Pr.P (fun ω => ¬ H ω ∧ ¬ S ω) ≠ 0) :
    π.P H' = (1/2)*qM + (1/3)*qT ∧ (1/2)*qM + (1/3)*qT ≤ 1/3 + qM/6 ∧ 1/3 + qM/6 ≤ 1/2 ∧
    (π.P H' = 1/2 ↔ qM = 1) := by
  obtain ⟨vM, vT, vW⟩ := displayA1 Pr H S hH hS coin start indep
  have posS : Pr.P S ≠ 0 := by rw [start]; exact half_ne_zero
  have sure : ∀ D : Ω → Prop, Pr.P D ≠ 0 → Pr.cond (fun _ => True) D = 1 := by
    intro D hD; unfold Measure.cond
    rw [Pr.Pcongr (B := D) (fun ω => ⟨fun k => k.2, fun k => ⟨trivial, k⟩⟩)]
    exact arithSelf _ hD
  rw [vM] at A2M; rw [vT] at A2T; rw [vW] at A2W
  rw [sure S posS] at A2M'; rw [sure _ posT] at A2T'; rw [sure _ posW] at A2W'
  have sH := split3 π hH' haM haT haW eMT eMW eTW exh
  have sT := split3 π π.ev_true haM haT haW eMT eMW eTW exh
  rw [π.total] at sT
  have nM := π.nonneg (π.ev_and π.ev_true haM)
  have nT := π.nonneg (π.ev_and π.ev_true haT)
  have nW := π.nonneg (π.ev_and π.ev_true haW)
  rw [A2M'] at nM; rw [A2T'] at nT; rw [A2W'] at nW
  rw [A2M', A2T', A2W'] at sT
  exact arithA3 _ _ _ _ qM qT qW sH A2M A2T A2W (arithSum3 _ _ _ sT) (arithM1 _ nM)
    (arithM1 _ nT) (arithM1 _ nW)
/-! ## Section 5.1: the subdivision lemma and conditionalization, copied from YourProof.lean -/

theorem arithScale (t x e : Rat) (ht : t ≠ 0) (he : e ≠ 0) : (t * x) / (t * e) = x / e := by
  grind

section Conditionalization

variable {Ω : Type} (m : Measure Ω)

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


/-- **(S5)**, section 5.1, source lines 583-587:
    ```
    \text{For a partition }E_{1},\dots,E_{n}\text{ of positive probability, }n\text{ suppositions in place of two:}\\
    \text{if }E_{i}\text{ then }c_{i}\text{: }\prsb(X\mid E_{i})=c_{i}\text{, and with }E_{i}\text{ learned, }\prsb_{+}(X)=c_{i}\text{, each }i.
    ```
    with its justification: "Each `E_i` subdivided as `E` was: the subdivision lemma and (S1) inside
    it, and (S2) and (S3) for each."
    Choice: `c_i` is `π(X | E_i)` (the definition in the display); the partition is a list of
    events exclusive as sets and exhaustive in the measure, each with positive value; "with `E_i`
    learned, `Pr_+(X) = c_i`" is read as (S3) is read in YourProof.lean: any later measure on the
    expanded algebra in which `E_i` is certain and its two cells have the ratios they are defined
    with. -/
theorem displayS5 {Ω : Type} (m : Measure Ω) (X : Ω → Prop) (Es : List (Ω → Prop))
    (hEs : ∀ E ∈ Es, m.ev E) (disj : List.Pairwise (fun A B => ∀ ω, ¬ (A ω ∧ B ω)) Es)
    (exhaust : m.P (orL Es) = 1) (pos : ∀ E ∈ Es, m.P E ≠ 0)
    (s : Rat) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ E ∈ Es,
      ((m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ Z p) = m.cond X E ∧
       (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ ¬ Z p) = m.cond X E) ∧
      ∀ later : Measure (Ω × Bool), later.ev (lift X) →
        later.ev (fun p => lift E p ∧ Z p) → later.ev (fun p => lift E p ∧ ¬ Z p) →
        later.P (lift E) = 1 →
        later.P (fun p => lift E p ∧ Z p) ≠ 0 → later.P (fun p => lift E p ∧ ¬ Z p) ≠ 0 →
        later.cond (lift X) (fun p => lift E p ∧ Z p)
          = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ Z p) →
        later.cond (lift X) (fun p => lift E p ∧ ¬ Z p)
          = (m.subdivide s hs0 hs1).cond (lift X) (fun p => lift E p ∧ ¬ Z p) →
        later.P (lift X) = m.cond X E := by
  intro E hE
  exact ⟨m.subdivision_lemma s hs0 hs1 X E (pos E hE),
    fun later hX hc1 hc2 cert p1 p2 s1 s2 =>
      m.conditionalization s hs0 hs1 (pos E hE) later hX hc1 hc2 cert p1 p2 s1 s2⟩

/-! ## Appendix A: the measure λ of (A4), as a finite model -/

section ModelA

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


/-- The six points of Appendix A: an outcome with a day on which it has a waking
    (`H∧S`: Monday; `H∧¬S`: Tuesday; `¬H∧S`: Monday and Tuesday; `¬H∧¬S`: Tuesday and Wednesday). -/
inductive APt | HSM | HnST | nHSM | nHST | nHnST | nHnSW

/-- `λ` of (A4): a quarter on each outcome, each tails outcome divided equally between its two
    wakings. -/
noncomputable def lamA : Measure APt where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 1/4 * ind (E .HSM) + 1/4 * ind (E .HnST) + 1/8 * ind (E .nHSM)
        + 1/8 * ind (E .nHST) + 1/8 * ind (E .nHnST) + 1/8 * ind (E .nHnSW)
  nonneg := by
    intro A _
    have w4 : (0 : Rat) ≤ 1/4 := by grind
    have w8 : (0 : Rat) ≤ 1/8 := by grind
    have h1 := wind_nonneg (1/4) w4 (A .HSM); have h2 := wind_nonneg (1/4) w4 (A .HnST)
    have h3 := wind_nonneg (1/8) w8 (A .nHSM); have h4 := wind_nonneg (1/8) w8 (A .nHST)
    have h5 := wind_nonneg (1/8) w8 (A .nHnST); have h6 := wind_nonneg (1/8) w8 (A .nHnSW)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .HSM); have h2 := ind_or (h .HnST); have h3 := ind_or (h .nHSM)
    have h4 := ind_or (h .nHST); have h5 := ind_or (h .nHnST); have h6 := ind_or (h .nHnSW)
    simp only [h1, h2, h3, h4, h5, h6]; grind

def HA : APt → Prop | .HSM => True | .HnST => True | _ => False
def SA : APt → Prop | .HSM => True | .nHSM => True | .nHST => True | _ => False
def aMA : APt → Prop | .HSM => True | .nHSM => True | _ => False
def aTA : APt → Prop | .HnST => True | .nHST => True | .nHnST => True | _ => False
def aWA : APt → Prop | .nHnSW => True | _ => False

/-- **(A4)**, Appendix A, source lines 1256-1262:
    ```
    \bigl(\lambda(\ea_M),\lambda(\ea_T),\lambda(\ea_W)\bigr)=\bigl(\tfrac38,\half,\tfrac18\bigr)\qquad
    \bigl(\lambda(H\mid \ea_M),\lambda(H\mid \ea_T),\lambda(H\mid \ea_W)\bigr)=\bigl(\twothirds,\half,0\bigr)\\
    \lambda(H)=\half.
    ```
    with the text around it: `λ` keeps a quarter on each outcome, the coin and the start day are
    independent in `λ`, and `λ(H | a_M) = 2/3` is not `Pr(H | [M]) = 1/2` of (A1).
    Choice: `a_D` is the set of wakings with day `D`'s announcement (`a_M` the Monday points). -/
theorem displayA4 :
    lamA.P aMA = 3/8 ∧ lamA.P aTA = 1/2 ∧ lamA.P aWA = 1/8 ∧
    lamA.cond HA aMA = 2/3 ∧ lamA.cond HA aTA = 1/2 ∧ lamA.cond HA aWA = 0 ∧ lamA.P HA = 1/2 ∧
    lamA.P (fun p => HA p ∧ SA p) = 1/4 ∧ lamA.P (fun p => HA p ∧ ¬ SA p) = 1/4 ∧
    lamA.P (fun p => ¬ HA p ∧ SA p) = 1/4 ∧ lamA.P (fun p => ¬ HA p ∧ ¬ SA p) = 1/4 ∧
    lamA.cond HA SA = lamA.P HA ∧ lamA.cond HA aMA ≠ 1/2 := by
  simp only [lamA, Measure.cond, HA, SA, aMA, aTA, aWA, ind_true, ind_false, and_self, and_true,
    and_false, not_true, not_false_eq_true]
  grind

end ModelA

/-! ## A finite model of the uneven urn: every condition of (8)-(13) and of
    `tag_swap_by_second_partition` met at once, for every `c` with `0 < c < 1` -/

section ModelC

/-- The four outcomes: heads and a Monday ball, heads and a Tuesday ball, tails and a Monday
    ball, tails and a Tuesday ball. -/
inductive OutC | R1 | R2 | R3 | R4

def HoutC : OutC → Prop | .R1 => True | .R2 => True | .R3 => False | .R4 => False
def CoutC : OutC → Prop | .R1 => True | .R2 => False | .R3 => True | .R4 => False

/-- The recording's measure at urn `c`: `H∧C` and `¬H∧C` at `c/2`, `H∧¬C` and `¬H∧¬C` at
    `(1-c)/2`. -/
noncomputable def PrModelC (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) : Measure OutC where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => c/2 * ind (E .R1) + (1-c)/2 * ind (E .R2) + c/2 * ind (E .R3)
        + (1-c)/2 * ind (E .R4)
  nonneg := by
    intro A _
    have w1 : (0 : Rat) ≤ c/2 := by grind
    have w2 : (0 : Rat) ≤ (1-c)/2 := by grind
    have h1 := wind_nonneg (c/2) w1 (A .R1); have h2 := wind_nonneg ((1-c)/2) w2 (A .R2)
    have h3 := wind_nonneg (c/2) w1 (A .R3); have h4 := wind_nonneg ((1-c)/2) w2 (A .R4)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1); have h2 := ind_or (h .R2)
    have h3 := ind_or (h .R3); have h4 := ind_or (h .R4)
    simp only [h1, h2, h3, h4]; grind

/-- The six points: an outcome with a day on which it has a waking. -/
inductive PtC | R1M | R2T | R3M | R3T | R4M | R4T

def HptC : PtC → Prop | .R1M => True | .R2T => True | _ => False
def CptC : PtC → Prop | .R1M => True | .R3M => True | .R3T => True | _ => False
/-- `a`: the Monday points; `b`: the Tuesday points. -/
def aptC : PtC → Prop | .R1M => True | .R3M => True | .R4M => True | _ => False
def bptC : PtC → Prop | .R2T => True | .R3T => True | .R4T => True | _ => False
/-- `d`: today is the day the ball marks; `e`: the other day. -/
def dptC : PtC → Prop | .R1M => True | .R3M => True | .R2T => True | .R4T => True | _ => False
def eptC : PtC → Prop | .R4M => True | .R3T => True | _ => False

/-- Your measure at urn `c`: `(R1,M)`, `(R3,M)`, `(R3,T)` at `c/3`; `(R4,M)`, `(R2,T)`, `(R4,T)` at
    `(1-c)/3`. -/
noncomputable def piModelC (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) : Measure PtC where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => c/3 * ind (E .R1M) + (1-c)/3 * ind (E .R2T) + c/3 * ind (E .R3M)
        + c/3 * ind (E .R3T) + (1-c)/3 * ind (E .R4M) + (1-c)/3 * ind (E .R4T)
  nonneg := by
    intro A _
    have wq : (0 : Rat) ≤ c/3 := by grind
    have wq' : (0 : Rat) ≤ (1-c)/3 := by grind
    have h1 := wind_nonneg (c/3) wq (A .R1M); have h2 := wind_nonneg ((1-c)/3) wq' (A .R2T)
    have h3 := wind_nonneg (c/3) wq (A .R3M); have h4 := wind_nonneg (c/3) wq (A .R3T)
    have h5 := wind_nonneg ((1-c)/3) wq' (A .R4M); have h6 := wind_nonneg ((1-c)/3) wq' (A .R4T)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1M); have h2 := ind_or (h .R2T); have h3 := ind_or (h .R3M)
    have h4 := ind_or (h .R3T); have h5 := ind_or (h .R4M); have h6 := ind_or (h .R4T)
    simp only [h1, h2, h3, h4, h5, h6]; grind

variable (c : Rat) (hc0 : 0 < c) (hc1 : c < 1)

/-- The recording model has the first assumption at urn `c`. -/
theorem modelC_recording :
    (PrModelC c hc0 hc1).P HoutC = 1/2 ∧ (PrModelC c hc0 hc1).P CoutC = c ∧
    (PrModelC c hc0 hc1).cond HoutC CoutC = (PrModelC c hc0 hc1).P HoutC := by
  simp only [PrModelC, Measure.cond, HoutC, CoutC, ind_true, ind_false, and_self, and_true,
    and_false]
  grind

/-- Your model: `q = π(a) = (1+c)/3`, strictly between 0 and 1, and `a`, `b` exclusive and
    exhaustive as sets. -/
theorem modelC_cells :
    (piModelC c hc0 hc1).P aptC = (1+c)/3 ∧ 0 < (1+c)/3 ∧ (1+c)/3 < 1 ∧
    (∀ ω, ¬ (aptC ω ∧ bptC ω)) ∧ (∀ ω, aptC ω ∨ bptC ω) := by
  refine ⟨?_, by grind, by grind, ?_, ?_⟩
  · simp only [piModelC, aptC, ind_true, ind_false]; grind
  · intro ω; cases ω <;> simp [aptC, bptC]
  · intro ω; cases ω <;> simp [aptC, bptC]

/-- The eight construction equations `con1` to `con8` of section TagSwap hold between the two
    models. -/
theorem modelC_construction :
    (piModelC c hc0 hc1).cond (fun ω => HptC ω ∧ CptC ω) aptC
      = (PrModelC c hc0 hc1).cond (fun ω => HoutC ω ∧ CoutC ω) (M HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => HptC ω ∧ ¬ CptC ω) aptC
      = (PrModelC c hc0 hc1).cond (fun ω => HoutC ω ∧ ¬ CoutC ω) (M HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => ¬ HptC ω ∧ CptC ω) aptC
      = (PrModelC c hc0 hc1).cond (fun ω => ¬ HoutC ω ∧ CoutC ω) (M HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => ¬ HptC ω ∧ ¬ CptC ω) aptC
      = (PrModelC c hc0 hc1).cond (fun ω => ¬ HoutC ω ∧ ¬ CoutC ω) (M HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => HptC ω ∧ CptC ω) bptC
      = (PrModelC c hc0 hc1).cond (fun ω => HoutC ω ∧ CoutC ω) (T HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => HptC ω ∧ ¬ CptC ω) bptC
      = (PrModelC c hc0 hc1).cond (fun ω => HoutC ω ∧ ¬ CoutC ω) (T HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => ¬ HptC ω ∧ CptC ω) bptC
      = (PrModelC c hc0 hc1).cond (fun ω => ¬ HoutC ω ∧ CoutC ω) (T HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond (fun ω => ¬ HptC ω ∧ ¬ CptC ω) bptC
      = (PrModelC c hc0 hc1).cond (fun ω => ¬ HoutC ω ∧ ¬ CoutC ω) (T HoutC CoutC) := by
  simp only [piModelC, PrModelC, Measure.cond, HptC, CptC, aptC, bptC, HoutC, CoutC, M, T,
    ind_true, ind_false, and_self, and_true, and_false, or_true, or_false,
    not_true_eq_false, not_false_eq_true]
  grind

/-- The second partition: `π(d) ≠ 0`, `π(e) ≠ 0`, `π(d ∧ e) = 0`, `π(d ∨ e) = 1`,
    `π(C | d) = Pr(C | ballDay)`, `π(C | e) = Pr(C | otherDay)`. -/
theorem modelC_second :
    (piModelC c hc0 hc1).P dptC ≠ 0 ∧ (piModelC c hc0 hc1).P eptC ≠ 0 ∧
    (piModelC c hc0 hc1).P (fun ω => dptC ω ∧ eptC ω) = 0 ∧
    (piModelC c hc0 hc1).P (fun ω => dptC ω ∨ eptC ω) = 1 ∧
    (piModelC c hc0 hc1).cond CptC dptC
      = (PrModelC c hc0 hc1).cond CoutC (ballDay HoutC CoutC) ∧
    (piModelC c hc0 hc1).cond CptC eptC
      = (PrModelC c hc0 hc1).cond CoutC (otherDay HoutC CoutC) := by
  simp only [piModelC, PrModelC, Measure.cond, CptC, dptC, eptC, HoutC, CoutC, ballDay, otherDay,
    M, T, ind_true, ind_false, and_self, and_true, and_false, or_true,
    or_false, not_true_eq_false, not_false_eq_true]
  grind

theorem modelC_AB (h0 : 0 < c) (h1 : c < 1) : (1+c)/3/(1+c) = 1/3 ∧ (1-(1+c)/3)/(2-c) = 1/3 := by grind

/-- `display13` applied to the two models: its conclusions hold in the model, at every
    `0 < c < 1`. -/
theorem modelC_display13 :
    (piModelC c hc0 hc1).cond HptC CptC = 1/3 ∧
    (piModelC c hc0 hc1).cond HptC (fun ω => ¬ CptC ω) = 1/3 ∧
    (piModelC c hc0 hc1).P HptC = 1/3 ∧ (piModelC c hc0 hc1).P CptC = c ∧
    (piModelC c hc0 hc1).cond aptC CptC = 2/3 ∧
    (piModelC c hc0 hc1).cond HptC (fun ω => aptC ω ∧ CptC ω) = 1/2 ∧
    (piModelC c hc0 hc1).cond HptC (fun ω => bptC ω ∧ CptC ω) = 0 := by
  obtain ⟨coin, ball, indep⟩ := modelC_recording c hc0 hc1
  obtain ⟨qa, hq0, hq1, excl, exh⟩ := modelC_cells c hc0 hc1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := modelC_construction c hc0 hc1
  exact display13 (PrModelC c hc0 hc1) HoutC CoutC trivial trivial c coin ball indep
    (piModelC c hc0 hc1) HptC CptC aptC bptC trivial trivial trivial trivial excl exh
    ((1+c)/3) hq0 hq1 qa k1 k2 k3 k4 k5 k6 k7 k8 hc0 hc1 (modelC_AB c hc0 hc1)

/-- `tag_swap_by_second_partition` applied to the two models with the cells `d`, `e`: its
    conclusions hold in the model, at every `0 < c < 1`. -/
theorem modelC_tag_swap :
    (piModelC c hc0 hc1).P CptC = c ∧
    ((1+c)/3/(1+c) = 1/3 ∧ (1-(1+c)/3)/(2-c) = 1/3) ∧
    (piModelC c hc0 hc1).cond HptC CptC = (piModelC c hc0 hc1).cond HptC (fun ω => ¬ CptC ω) := by
  obtain ⟨coin, ball, indep⟩ := modelC_recording c hc0 hc1
  obtain ⟨qa, hq0, hq1, excl, exh⟩ := modelC_cells c hc0 hc1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := modelC_construction c hc0 hc1
  obtain ⟨dpos, epos, de_and, de_or, cd, ce⟩ := modelC_second c hc0 hc1
  exact tag_swap_by_second_partition (PrModelC c hc0 hc1) HoutC CoutC trivial trivial c coin ball
    indep (piModelC c hc0 hc1) HptC CptC aptC bptC trivial trivial trivial trivial excl exh
    ((1+c)/3) hq0 hq1 qa k1 k2 k3 k4 k5 k6 k7 k8 hc0 hc1 dptC eptC trivial trivial dpos epos
    de_and de_or cd ce

end ModelC

/-! ## Addendum 22 Nov (audit of statements): (14) as the paper derives it, (22) with A = B = 1/3
    derived, the uneven urn of section 7.5 with a measure, the limit of (19), footnote values,
    and the gas stations of section 6.1 -/

theorem bounds_99_lt (c : Rat) (h : c = 99/100) : 0 < c ∧ c < 1 := by
  subst h; exact ⟨by grind, by grind⟩

section TagSwap3

variable {Ω Ω' : Type} (Pr : Measure Ω) (H C : Ω → Prop) (hH : Pr.ev H) (hC : Pr.ev C)
  (c : Rat) (coin : Pr.P H = 1/2) (ball : Pr.P C = c) (indep : Pr.cond H C = Pr.P H)
  (π : Measure Ω') (H' C' a b : Ω' → Prop)
  (hH' : π.ev H') (hC' : π.ev C') (ha : π.ev a) (hb : π.ev b)
  (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
  (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) (qa : π.P a = q)
  (con1 : π.cond (fun ω => H' ω ∧ C' ω) a = Pr.cond (fun ω => H ω ∧ C ω) (M H C))
  (con2 : π.cond (fun ω => H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => H ω ∧ ¬ C ω) (M H C))
  (con3 : π.cond (fun ω => ¬ H' ω ∧ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ C ω) (M H C))
  (con4 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) a = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (M H C))
  (con5 : π.cond (fun ω => H' ω ∧ C' ω) b = Pr.cond (fun ω => H ω ∧ C ω) (T H C))
  (con6 : π.cond (fun ω => H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => H ω ∧ ¬ C ω) (T H C))
  (con7 : π.cond (fun ω => ¬ H' ω ∧ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ C ω) (T H C))
  (con8 : π.cond (fun ω => ¬ H' ω ∧ ¬ C' ω) b = Pr.cond (fun ω => ¬ H ω ∧ ¬ C ω) (T H C))
include hH hC coin ball indep hH' hC' ha hb excl exh hq0 hq1 qa con1 con2 con3 con4 con5 con6
  con7 con8

/-- **(14) at every urn**, audit F2 part (i). Source lines 799-805 ("given the tag-swapping lemma
    ... The value given C is the same for any distribution of the balls (see (13))") and the
    justification of (12), line 756. At every urn `0 < c < 1`, under the hypotheses of
    `tag_swap_by_second_partition` (which derive `A = B = 1/3` from the cells `d`, `e`),
    `π(H | C) = 1/3`: `display13` with the `A = B = 1/3` that `tag_swap_by_second_partition`
    gives. -/
theorem display14_every_urn (hc0 : 0 < c) (hc1 : c < 1) (d e : Ω' → Prop)
    (hd : π.ev d) (he : π.ev e) (dpos : π.P d ≠ 0) (epos : π.P e ≠ 0)
    (de_and : π.P (fun ω => d ω ∧ e ω) = 0) (de_or : π.P (fun ω => d ω ∨ e ω) = 1)
    (cond_d : π.cond C' d = Pr.cond C (ballDay H C))
    (cond_e : π.cond C' e = Pr.cond C (otherDay H C)) :
    π.cond H' C' = 1/3 :=
  (display13 Pr H C hH hC c coin ball indep π H' C' a b hH' hC' ha hb excl exh q hq0 hq1 qa
    con1 con2 con3 con4 con5 con6 con7 con8 hc0 hc1
    (tag_swap_by_second_partition Pr H C hH hC c coin ball indep π H' C' a b hH' hC' ha hb excl
      exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 hc0 hc1 d e hd he dpos epos
      de_and de_or cond_d cond_e).2.1).1

/-- **(22), second line, with `A = B = 1/3` derived**, audit F3. The same conclusions as
    `display22_yours`, with the hypotheses of `tag_swap_by_second_partition` (cells `d`, `e`) in
    place of `hAB`. -/
theorem display22_by_second_partition (c99 : c = 99/100) (d e : Ω' → Prop)
    (hd : π.ev d) (he : π.ev e) (dpos : π.P d ≠ 0) (epos : π.P e ≠ 0)
    (de_and : π.P (fun ω => d ω ∧ e ω) = 0) (de_or : π.P (fun ω => d ω ∨ e ω) = 1)
    (cond_d : π.cond C' d = Pr.cond C (ballDay H C))
    (cond_e : π.cond C' e = Pr.cond C (otherDay H C)) :
    π.P C' = 99/100 ∧ π.cond H' a = 99/199 ∧ π.cond H' b = 1/101 ∧
    π.P (fun ω => a ω ∧ H' ω ∧ C' ω) = 33/100 ∧ π.P (fun ω => a ω ∧ ¬ H' ω ∧ C' ω) = 33/100 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ C' ω) = 33/100 ∧
    π.P (fun ω => a ω ∧ ¬ H' ω ∧ ¬ C' ω) = 1/300 ∧
    π.P (fun ω => b ω ∧ H' ω ∧ ¬ C' ω) = 1/300 ∧
    π.P (fun ω => b ω ∧ ¬ H' ω ∧ ¬ C' ω) = 1/300 :=
  display22_yours Pr H C hH hC c coin ball indep π H' C' a b hH' hC' ha hb excl exh q hq0 hq1 qa
    con1 con2 con3 con4 con5 con6 con7 con8 c99
    (tag_swap_by_second_partition Pr H C hH hC c coin ball indep π H' C' a b hH' hC' ha hb excl
      exh q hq0 hq1 qa con1 con2 con3 con4 con5 con6 con7 con8 (bounds_99_lt c c99).1
      (bounds_99_lt c c99).2 d e hd he dpos epos de_and de_or cond_d cond_e).2.1

end TagSwap3

theorem arithEdge (PX x1 x2 e ne c : Rat) (s : PX = x1 + x2) (cc : e + ne = 1) (he : e = 1)
    (n : x2 ≤ ne) (p : 0 ≤ x2) (h : x1 / e = c) : PX = c := by grind

/-- `certain_gives_ratio`, copied from YourProof.lean: in any measure in which `E` is certain and
    `X` has the ratio `c` given `E`, the unconditional probability of `X` is `c`. -/
theorem Measure.certain_gives_ratio {Ω : Type} (m : Measure Ω) {X E : Ω → Prop} {c : Rat}
    (hX : m.ev X) (hE : m.ev E) (E_certain : m.P E = 1) (ratio : m.cond X E = c) : m.P X = c := by
  have s := m.split hX hE
  have cc := m.compl hE
  have n : m.P (fun ω => X ω ∧ ¬ E ω) ≤ m.P (fun ω => ¬ E ω) :=
    m.mono (m.ev_and hX (m.ev_not hE)) (m.ev_not hE) (fun ω h => h.2)
  have p := m.nonneg (m.ev_and hX (m.ev_not hE))
  unfold Measure.cond at ratio
  exact arithEdge _ _ _ _ _ _ s cc E_certain n p ratio

/-- **(14) with `C` certain**, audit F2 part (ii): step (S3) at the edge applied to the ball.
    "With `C` certain the case is the one with Monday balls only" (line 756): any standard
    measure in which `C` is certain and heads has, given `C`, the ratio 1/3 gives heads 1/3. -/
theorem display14_C_certain {Ω : Type} (π : Measure Ω) (H C : Ω → Prop) (hH : π.ev H)
    (hC : π.ev C) (C_certain : π.P C = 1) (ratio : π.cond H C = 1/3) : π.P H = 1/3 :=
  π.certain_gives_ratio hH hC C_certain ratio

/-- The instance of `display22_by_second_partition` on the model `piModelC` at `c = 99/100`. -/
theorem modelC99_display22 :
    (piModelC (99/100) (bounds_99_lt _ rfl).1 (bounds_99_lt _ rfl).2).P CptC = 99/100 ∧
    (piModelC (99/100) (bounds_99_lt _ rfl).1 (bounds_99_lt _ rfl).2).cond HptC aptC = 99/199 ∧
    (piModelC (99/100) (bounds_99_lt _ rfl).1 (bounds_99_lt _ rfl).2).cond HptC bptC = 1/101 := by
  have h0 := (bounds_99_lt (99/100) rfl).1
  have h1 := (bounds_99_lt (99/100) rfl).2
  obtain ⟨coin, ball, indep⟩ := modelC_recording (99/100) h0 h1
  obtain ⟨qa, hq0, hq1, excl, exh⟩ := modelC_cells (99/100) h0 h1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := modelC_construction (99/100) h0 h1
  obtain ⟨dpos, epos, de_and, de_or, cd, ce⟩ := modelC_second (99/100) h0 h1
  obtain ⟨r1, r2, r3, _⟩ := display22_by_second_partition (PrModelC (99/100) h0 h1) HoutC CoutC
    trivial trivial (99/100) coin ball indep (piModelC (99/100) h0 h1) HptC CptC aptC bptC
    trivial trivial trivial trivial excl exh ((1+99/100)/3) hq0 hq1 qa k1 k2 k3 k4 k5 k6 k7 k8
    rfl dptC eptC trivial trivial dpos epos de_and de_or cd ce
  exact ⟨r1, r2, r3⟩

/-! ### The uneven urn of section 7.5 with a measure (audit F5) -/

theorem arith21u (pHW pW x1 x3 x4 x6 x7 x8 ρ c : Rat)
    (sHW : pHW = x1 + 0 + 0 + 0 + 0 + x6 + 0 + 0) (sW : pW = x1 + 0 + x3 + x4 + 0 + x6 + x7 + x8)
    (h1 : x1 = ρ*((1/2)*c)) (h3 : x3 = ρ*((1/2)*c))
    (h4 : x4 = ρ*((1/2)*(1-c))) (h6 : x6 = (1-ρ)*((1/2)*(1-c)))
    (h7 : x7 = (1-ρ)*((1/2)*c)) (h8 : x8 = (1-ρ)*((1/2)*(1-c))) :
    pHW = (ρ*c + (1-ρ)*(1-c))/2 ∧ pW = (1 + (ρ*c + (1-ρ)*(1-c)))/2 := by grind

theorem arithS0 (ρ c : Rat) (h1 : 0 ≤ ρ*c) (h2 : 0 ≤ (1-ρ)*(1-c)) : 0 ≤ ρ*c + (1-ρ)*(1-c) := by
  grind

theorem arith21u2 (pHW pW s : Rat) (hs0 : 0 ≤ s) (e1 : pHW = s/2) (e2 : pW = (1+s)/2) :
    pHW / pW = s/(1+s) := by grind

/-- **The uneven urn, source line 939**, with a measure:
    "with `s = ρc + (1-ρ)(1-c)` ... `H ∧ W` has `s/2` and `W` has `(1+s)/2`. The rule gives heads
    `s/(1+s)`. That is 1/3 iff `(2c-1)(ρ-1/2) = 0` ... At `c = 1/3`, for example, `ρ = 1` gives a
    quarter."
    Choice: `D` is the Monday clock-time, `C` the Monday ball, `H` heads; "the coin, the ball and
    the prior are independent of one another" is stated as the product values of the eight
    conjunctions (`μ(D ∧ H ∧ C) = ρ · 1/2 · c`, and so on); `W`, the clock-time is a waking time,
    is tails, or heads with the clock-time the day on the ball. -/
theorem display21_uneven_measure {Ω : Type} (μ : Measure Ω) (H C D : Ω → Prop) (hH : μ.ev H)
    (hC : μ.ev C) (hD : μ.ev D) (ρ c : Rat) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc0 : 0 < c) (hc1 : c < 1)
    (p1 : μ.P (fun ω => D ω ∧ H ω ∧ C ω) = ρ*((1/2)*c))
    (p2 : μ.P (fun ω => D ω ∧ H ω ∧ ¬ C ω) = ρ*((1/2)*(1-c)))
    (p3 : μ.P (fun ω => D ω ∧ ¬ H ω ∧ C ω) = ρ*((1/2)*c))
    (p4 : μ.P (fun ω => D ω ∧ ¬ H ω ∧ ¬ C ω) = ρ*((1/2)*(1-c)))
    (p5 : μ.P (fun ω => ¬ D ω ∧ H ω ∧ C ω) = (1-ρ)*((1/2)*c))
    (p6 : μ.P (fun ω => ¬ D ω ∧ H ω ∧ ¬ C ω) = (1-ρ)*((1/2)*(1-c)))
    (p7 : μ.P (fun ω => ¬ D ω ∧ ¬ H ω ∧ C ω) = (1-ρ)*((1/2)*c))
    (p8 : μ.P (fun ω => ¬ D ω ∧ ¬ H ω ∧ ¬ C ω) = (1-ρ)*((1/2)*(1-c))) :
    μ.P (fun ω => H ω ∧ (¬ H ω ∨ (H ω ∧ ((D ω ∧ C ω) ∨ (¬ D ω ∧ ¬ C ω)))))
      = (ρ*c + (1-ρ)*(1-c))/2 ∧
    μ.P (fun ω => ¬ H ω ∨ (H ω ∧ ((D ω ∧ C ω) ∨ (¬ D ω ∧ ¬ C ω))))
      = (1 + (ρ*c + (1-ρ)*(1-c)))/2 ∧
    μ.cond H (fun ω => ¬ H ω ∨ (H ω ∧ ((D ω ∧ C ω) ∨ (¬ D ω ∧ ¬ C ω))))
      = (ρ*c + (1-ρ)*(1-c))/(1 + (ρ*c + (1-ρ)*(1-c))) ∧
    ((ρ*c + (1-ρ)*(1-c))/(1 + (ρ*c + (1-ρ)*(1-c))) = 1/3 ↔ (2*c-1)*(ρ-1/2) = 0) ∧
    (c = 1/3 → ρ = 1 → (ρ*c + (1-ρ)*(1-c))/(1 + (ρ*c + (1-ρ)*(1-c))) = 1/4) := by
  have excl : ∀ ω, ¬ (D ω ∧ ¬ D ω) := fun ω k => k.2 k.1
  have exh : ∀ ω, D ω ∨ ¬ D ω := fun ω => Classical.em _
  have hnD := μ.ev_not hD
  have sHW := decomp_eval μ hD hnD hH hC excl exh
    (X := fun ω => H ω ∧ (¬ H ω ∨ (H ω ∧ ((D ω ∧ C ω) ∨ (¬ D ω ∧ ¬ C ω)))))
    (μ.ev_and hH (μ.ev_or (μ.ev_not hH) (μ.ev_and hH (μ.ev_or (μ.ev_and hD hC)
      (μ.ev_and hnD (μ.ev_not hC))))))
    (by lterm) (by lterm) (by lterm) (by lterm)
    (by lterm) (by lterm) (by lterm) (by lterm)
  have sW := decomp_eval μ hD hnD hH hC excl exh
    (X := fun ω => ¬ H ω ∨ (H ω ∧ ((D ω ∧ C ω) ∨ (¬ D ω ∧ ¬ C ω))))
    (μ.ev_or (μ.ev_not hH) (μ.ev_and hH (μ.ev_or (μ.ev_and hD hC)
      (μ.ev_and hnD (μ.ev_not hC)))))
    (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm) (by lterm)
  have hs0 : 0 ≤ ρ*c + (1-ρ)*(1-c) :=
    arithS0 ρ c (Rat.mul_nonneg hρ0 (by grind)) (Rat.mul_nonneg (by grind) (by grind))
  obtain ⟨e1, e2⟩ := arith21u _ _ _ _ _ _ _ _ ρ c sHW sW p1 p3 p4 p6 p7 p8
  refine ⟨e1, e2, ?_, (display21_uneven c ρ hs0).1, (display21_uneven c ρ hs0).2⟩
  unfold Measure.cond
  exact arith21u2 _ _ _ hs0 e1 e2

/-! ### Item 7: the limit of (19), and footnote values of sections 5.1 and 5.3 -/

/-- Every rational is below some natural number. -/
theorem rat_arch (x : Rat) : ∃ N : Nat, x ≤ (N : Rat) := by
  refine ⟨x.ceil.toNat, ?_⟩
  have h1 := @Rat.le_ceil x
  have h2 : x.ceil ≤ (x.ceil.toNat : Int) := Int.self_le_toNat _
  have h3 : ((x.ceil : Int) : Rat) ≤ (((x.ceil.toNat : Nat) : Int) : Rat) := by
    exact_mod_cast h2
  have h4 : (((x.ceil.toNat : Nat) : Int) : Rat) = ((x.ceil.toNat : Nat) : Rat) := by
    exact_mod_cast rfl
  rw [h4] at h3
  exact Rat.le_trans h1 h3

theorem div_lt_of_lt_mul (x y e : Rat) (hy : 0 < y) (h : x < e * y) : x / y < e := by
  have hi : 0 < y⁻¹ := Rat.inv_pos.mpr hy
  have k := Rat.mul_lt_mul_of_pos_right h hi
  rw [Rat.div_def]
  have e1 : e * y * y⁻¹ = e := by grind
  rw [e1] at k; exact k

theorem natcast_le (a b : Nat) (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by exact_mod_cast h

/-- From `n ≥ k/ε` (with `ε > 0`), `ε n ≥ k`. -/
theorem eps_mul (eps k n : Rat) (he : 0 < eps) (h : k / eps ≤ n) : k ≤ eps * n := by
  have k1 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt he)
  have e1 : eps * (k / eps) = k := by grind
  rw [e1] at k1; exact k1

/-- **(19), its limit** (source line 892, "its limit is 1/3"): the difference is exactly
    `2/(3(3N+4))` at every `N`, and for every positive rational `ε` there is an `N₀` beyond
    which it is below `ε`. -/
theorem display19_limit :
    (∀ N : Nat, ((N:Rat)+2)/(3*(N:Rat)+4) - 1/3 = 2/(3*(3*(N:Rat)+4))) ∧
    ∀ eps : Rat, 0 < eps → ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      ((N:Rat)+2)/(3*(N:Rat)+4) - 1/3 < eps := by
  refine ⟨fun N => arith19a _ (natcast_nonneg N), fun eps he => ?_⟩
  obtain ⟨N0, hN0⟩ := rat_arch (1/eps)
  refine ⟨N0, fun N hN => ?_⟩
  have hn := natcast_nonneg N
  have k : (1:Rat)/eps ≤ (N:Rat) := Rat.le_trans hN0 (natcast_le _ _ hN)
  have t := eps_mul eps 1 _ he k
  rw [arith19a _ hn]
  exact div_lt_of_lt_mul _ _ _ (by grind) (by grind)

/-- **Footnote, section 5.1** (source line 499, the die): the ratio gives the 2 a third
    (`(1/6)/(1/2)`); the rule that shares the odd faces' half equally gives `1/6 + 1/6 = 1/3` with
    three outcomes listed and `1/6 + 1/4 = 5/12` with two; the two values differ. -/
theorem footnote_die : ((1:Rat)/6)/(1/2) = 1/3 ∧ (1:Rat)/6 + (1/2)/3 = 1/3 ∧
    (1:Rat)/6 + 1/6 = 1/3 ∧ (1:Rat)/6 + (1/2)/2 = 5/12 ∧ (1:Rat)/6 + 1/4 = 5/12 ∧
    (1:Rat)/3 ≠ 5/12 := by grind

/-- The value of `Y` after a doubt at level `n`, each level at 0.8 sure, starting from 0.9
    (Jeffrey's rule with the 0.9 / 0.1 of the measurement): `v (n+1) = 0.8 v n + 0.2 (1 - v n)`. -/
def toyV : Nat → Rat
  | 0 => 9/10
  | n + 1 => (8/10) * toyV n + (2/10) * (1 - toyV n)

theorem toyV_closed (n : Nat) : toyV n = 1/2 + (2/5) * (3/5)^n := by
  induction n with
  | zero => simp only [toyV]; grind
  | succ n ih => simp only [toyV]; rw [ih]; grind

theorem pow_pos' (r : Rat) (hr : 0 < r) (n : Nat) : 0 < r^n := by
  induction n with
  | zero => grind
  | succ n ih =>
    have := Rat.mul_pos ih hr
    grind

/-- Bernoulli: `r^n (1 + n(1-r)) ≤ 1` for `0 < r < 1`. -/
theorem bernoulli' (r : Rat) (hr0 : 0 < r) (hr1 : r < 1) (n : Nat) :
    r^n * (1 + (n:Rat)*(1-r)) ≤ 1 := by
  induction n with
  | zero => grind
  | succ n ih =>
    have hx := Rat.le_of_lt (pow_pos' r hr0 n)
    have hn := natcast_nonneg n
    have q : 0 ≤ ((n:Rat)+1) * ((1-r)*(1-r)) :=
      Rat.mul_nonneg (by grind) (Rat.mul_nonneg (by grind) (by grind))
    have step : r * (1 + ((n:Rat)+1)*(1-r)) ≤ 1 + (n:Rat)*(1-r) := by grind
    have k := Rat.mul_le_mul_of_nonneg_left step hx
    have e : ((n+1 : Nat) : Rat) = (n:Rat) + 1 := by exact_mod_cast rfl
    have ep : r^(n+1) = r^n * r := Rat.pow_succ _ _
    rw [e, ep]
    have e2 : r ^ n * r * (1 + ((n:Rat) + 1) * (1 - r)) = r ^ n * (r * (1 + ((n:Rat) + 1) * (1 - r))) := by
      grind
    rw [e2]
    exact Rat.le_trans k ih

/-- `a r^n` falls below every positive `ε` from some `n` on (`0 < r < 1`, `0 < a`). -/
theorem geom_small (a r : Rat) (ha : 0 < a) (hr0 : 0 < r) (hr1 : r < 1) (eps : Rat) (he : 0 < eps) :
    ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → a * r^n < eps := by
  obtain ⟨N0, hN0⟩ := rat_arch (a / (eps * (1-r)))
  refine ⟨N0, fun n hn => ?_⟩
  have hnr := Rat.le_trans hN0 (natcast_le _ _ hn)
  have epr : 0 < eps * (1-r) := Rat.mul_pos he (by grind)
  have t := eps_mul (eps * (1-r)) a _ epr hnr
  have b := bernoulli' r hr0 hr1 n
  have x0 := pow_pos' r hr0 n
  have b2 := Rat.mul_le_mul_of_nonneg_left b (Rat.le_of_lt he)
  have t2 := Rat.mul_le_mul_of_nonneg_left t (Rat.le_of_lt x0)
  have ex := Rat.mul_pos he x0
  grind

/-- **Footnote, section 5.3** (source line 678, the toy model): with `Y` at 1/2 before and the
    measurement 0.9 reliable, `Y` has 0.9 if you are sure of what she said and 0.74 if you are
    0.8 sure; "with the same doubt at every level" the values `toyV n` decrease to 1/2: above
    1/2 at every level and below `1/2 + ε` from some level on. Choice: the doubt at each level is
    Jeffrey's rule at 0.8 between the two reports, with ratios 0.9 and 0.1. -/
theorem footnote_toy :
    (1:Rat) * (9/10) + 0 * (1/10) = 9/10 ∧ (8/10:Rat) * (9/10) + (2/10) * (1/10) = 74/100 ∧
    toyV 0 = 9/10 ∧ toyV 1 = 74/100 ∧ (∀ n, toyV (n+1) < toyV n) ∧ (∀ n, 1/2 < toyV n) ∧
    ∀ eps : Rat, 0 < eps → ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → toyV n < 1/2 + eps := by
  refine ⟨by grind, by grind, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [toyV]; grind
  · intro n; rw [toyV_closed, toyV_closed]
    have := pow_pos' (3/5) (by grind) n
    have e : (3/5 : Rat)^(n+1) = (3/5)^n * (3/5) := Rat.pow_succ _ _
    rw [e]; grind
  · intro n; rw [toyV_closed]; have := pow_pos' (3/5) (by grind) n; grind
  · intro eps he
    obtain ⟨N0, h⟩ := geom_small (2/5) (3/5) (by grind) (by grind) (by grind) eps he
    exact ⟨N0, fun n hn => by rw [toyV_closed]; have := h n hn; grind⟩

/-- The sequence named in the audit brief, `1/2 + (3/10)(4/5)^n`: it decreases, stays above 1/2,
    and is below `1/2 + ε` from some `n` on. (Its first values are 0.8 and 0.74; the footnote's
    0.9 is `toyV 0`.) -/
theorem brief_sequence :
    (∀ n : Nat, (1:Rat)/2 + (3/10)*(4/5)^(n+1) < 1/2 + (3/10)*(4/5)^n) ∧
    (∀ n : Nat, (1:Rat)/2 < 1/2 + (3/10)*(4/5)^n) ∧
    ((1:Rat)/2 + (3/10)*(4/5)^0 = 8/10) ∧ ((1:Rat)/2 + (3/10)*(4/5)^1 = 74/100) ∧
    ∀ eps : Rat, 0 < eps → ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → (1:Rat)/2 + (3/10)*(4/5)^n < 1/2 + eps := by
  refine ⟨fun n => ?_, fun n => ?_, by grind, by grind, fun eps he => ?_⟩
  · have := pow_pos' (4/5) (by grind) n
    have e : (4/5 : Rat)^(n+1) = (4/5)^n * (4/5) := Rat.pow_succ _ _
    rw [e]; grind
  · have := pow_pos' (4/5) (by grind) n; grind
  · obtain ⟨N0, h⟩ := geom_small (3/10) (4/5) (by grind) (by grind) (by grind) eps he
    exact ⟨N0, fun n hn => by have := h n hn; grind⟩

/-! ### Section 6.1: Schell(ing)'s gas stations, the manifesto's measure as a finite model -/

section GasStation

/-- A point: the coin (heads), the where urn's ball (names the Monday station), the whether
    urn's ball (meet), the tails urn's ball (names the Monday station). -/
abbrev GasPt := Bool × Bool × Bool × Bool

/-- The manifesto's measure: a fair coin, the where urn naming the Monday station with `w`, the
    whether urn giving `meet` with `s`, the tails urn naming the Monday station with 1/2, all four
    independent. The paper's manifesto has `w = s = 1/2`. -/
noncomputable def gasModel (w s : Rat) (hw0 : 0 ≤ w) (hw1 : 0 ≤ 1 - w) (hs0 : 0 ≤ s)
    (hs1 : 0 ≤ 1 - s) : Measure GasPt where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => (1/2)*w*s*(1/2) * ind (E (true, true, true, true))
        + (1/2)*w*s*(1/2) * ind (E (true, true, true, false))
        + (1/2)*w*(1-s)*(1/2) * ind (E (true, true, false, true))
        + (1/2)*w*(1-s)*(1/2) * ind (E (true, true, false, false))
        + (1/2)*(1-w)*s*(1/2) * ind (E (true, false, true, true))
        + (1/2)*(1-w)*s*(1/2) * ind (E (true, false, true, false))
        + (1/2)*(1-w)*(1-s)*(1/2) * ind (E (true, false, false, true))
        + (1/2)*(1-w)*(1-s)*(1/2) * ind (E (true, false, false, false))
        + (1/2)*w*s*(1/2) * ind (E (false, true, true, true))
        + (1/2)*w*s*(1/2) * ind (E (false, true, true, false))
        + (1/2)*w*(1-s)*(1/2) * ind (E (false, true, false, true))
        + (1/2)*w*(1-s)*(1/2) * ind (E (false, true, false, false))
        + (1/2)*(1-w)*s*(1/2) * ind (E (false, false, true, true))
        + (1/2)*(1-w)*s*(1/2) * ind (E (false, false, true, false))
        + (1/2)*(1-w)*(1-s)*(1/2) * ind (E (false, false, false, true))
        + (1/2)*(1-w)*(1-s)*(1/2) * ind (E (false, false, false, false))
  nonneg := by
    intro A _
    have n0 := wind_nonneg ((1/2)*w*s*(1/2)) (by have := Rat.mul_nonneg hw0 hs0; grind) (A (true, true, true, true))
    have n1 := wind_nonneg ((1/2)*w*s*(1/2)) (by have := Rat.mul_nonneg hw0 hs0; grind) (A (true, true, true, false))
    have n2 := wind_nonneg ((1/2)*w*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw0 hs1; grind) (A (true, true, false, true))
    have n3 := wind_nonneg ((1/2)*w*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw0 hs1; grind) (A (true, true, false, false))
    have n4 := wind_nonneg ((1/2)*(1-w)*s*(1/2)) (by have := Rat.mul_nonneg hw1 hs0; grind) (A (true, false, true, true))
    have n5 := wind_nonneg ((1/2)*(1-w)*s*(1/2)) (by have := Rat.mul_nonneg hw1 hs0; grind) (A (true, false, true, false))
    have n6 := wind_nonneg ((1/2)*(1-w)*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw1 hs1; grind) (A (true, false, false, true))
    have n7 := wind_nonneg ((1/2)*(1-w)*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw1 hs1; grind) (A (true, false, false, false))
    have n8 := wind_nonneg ((1/2)*w*s*(1/2)) (by have := Rat.mul_nonneg hw0 hs0; grind) (A (false, true, true, true))
    have n9 := wind_nonneg ((1/2)*w*s*(1/2)) (by have := Rat.mul_nonneg hw0 hs0; grind) (A (false, true, true, false))
    have n10 := wind_nonneg ((1/2)*w*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw0 hs1; grind) (A (false, true, false, true))
    have n11 := wind_nonneg ((1/2)*w*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw0 hs1; grind) (A (false, true, false, false))
    have n12 := wind_nonneg ((1/2)*(1-w)*s*(1/2)) (by have := Rat.mul_nonneg hw1 hs0; grind) (A (false, false, true, true))
    have n13 := wind_nonneg ((1/2)*(1-w)*s*(1/2)) (by have := Rat.mul_nonneg hw1 hs0; grind) (A (false, false, true, false))
    have n14 := wind_nonneg ((1/2)*(1-w)*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw1 hs1; grind) (A (false, false, false, true))
    have n15 := wind_nonneg ((1/2)*(1-w)*(1-s)*(1/2)) (by have := Rat.mul_nonneg hw1 hs1; grind) (A (false, false, false, false))
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have a0 := ind_or (h (true, true, true, true)); have a1 := ind_or (h (true, true, true, false)); have a2 := ind_or (h (true, true, false, true)); have a3 := ind_or (h (true, true, false, false)); have a4 := ind_or (h (true, false, true, true)); have a5 := ind_or (h (true, false, true, false)); have a6 := ind_or (h (true, false, false, true)); have a7 := ind_or (h (true, false, false, false)); have a8 := ind_or (h (false, true, true, true)); have a9 := ind_or (h (false, true, true, false)); have a10 := ind_or (h (false, true, false, true)); have a11 := ind_or (h (false, true, false, false)); have a12 := ind_or (h (false, false, true, true)); have a13 := ind_or (h (false, false, true, false)); have a14 := ind_or (h (false, false, false, true)); have a15 := ind_or (h (false, false, false, false))
    simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]; grind

/-- Heads. -/
def gH : GasPt → Prop := fun p => p.1 = true
/-- You meet at the Monday station: heads, the where urn names Monday, and `meet`; or tails and
    the tails urn names Monday. -/
def gMon : GasPt → Prop := fun p =>
  (p.1 = true ∧ p.2.1 = true ∧ p.2.2.1 = true) ∨ (p.1 = false ∧ p.2.2.2 = true)
/-- You meet at the Tuesday station. -/
def gTue : GasPt → Prop := fun p =>
  (p.1 = true ∧ p.2.1 = false ∧ p.2.2.1 = true) ∨ (p.1 = false ∧ p.2.2.2 = false)

theorem nn_half : (0:Rat) ≤ 1/2 := by grind
theorem nn_half' : (0:Rat) ≤ 1 - 1/2 := by grind
theorem nn_one : (0:Rat) ≤ 1 := by grind
theorem nn_one' : (0:Rat) ≤ 1 - 1 := by grind

/-- **Section 6.1, source line 788**: at the manifesto's urns, heads has 1/3 at a meeting at the
    Monday station and 1/3 at a meeting at the Tuesday station ("of the meetings at the Monday
    station tails has twice what heads has"). -/
theorem gas_manifesto :
    (gasModel (1/2) (1/2) nn_half nn_half' nn_half nn_half').cond gH gMon = 1/3 ∧
    (gasModel (1/2) (1/2) nn_half nn_half' nn_half nn_half').cond gH gTue = 1/3 := by
  simp [gasModel, Measure.cond, gH, gMon, gTue, ind_true, ind_false]
  grind

/-- Source line 790, the where urn moved (`w` the proportion of Monday balls, `s = 1/2`): of all
    the meetings tails still has twice what heads has, `Pr(H | a meeting) = 1/3` at every `w`;
    the egoist (`w = 1`) has two thirds of the meetings at his station, heads 1/2 there and 0 at
    the other. -/
theorem gas_where_urn (w : Rat) (hw0 : 0 ≤ w) (hw1 : 0 ≤ 1 - w) :
    (gasModel w (1/2) hw0 hw1 nn_half nn_half').cond gH (fun p => gMon p ∨ gTue p) = 1/3 := by
  simp [gasModel, Measure.cond, gH, gMon, gTue, ind_true, ind_false]
  grind

theorem gas_egoist :
    (gasModel 1 (1/2) nn_one nn_one' nn_half nn_half').cond gH gMon = 1/2 ∧
    (gasModel 1 (1/2) nn_one nn_one' nn_half nn_half').cond gH gTue = 0 ∧
    (gasModel 1 (1/2) nn_one nn_one' nn_half nn_half').cond gMon (fun p => gMon p ∨ gTue p)
      = 2/3 := by
  simp [gasModel, Measure.cond, gH, gMon, gTue, ind_true, ind_false]
  grind

/-- Source line 792, the whether urn moved (`meet` drawn with `s` on heads, `w = 1/2`): heads has
    `s/(1+s)` at a meeting, at either station; at `s = 1` (you always meet) the coin's 1/2. -/
theorem gas_whether_urn (s : Rat) (hs0 : 0 ≤ s) (hs1 : 0 ≤ 1 - s) :
    (gasModel (1/2) s nn_half nn_half' hs0 hs1).cond gH gMon = s/(1+s) ∧
    (gasModel (1/2) s nn_half nn_half' hs0 hs1).cond gH gTue = s/(1+s) ∧
    (s = 1 → s/(1+s) = 1/2) := by
  simp [gasModel, Measure.cond, gH, gMon, gTue, ind_true, ind_false]
  grind

end GasStation

end Displays

-- What the theorems rest on (Lean prints every axiom used):
#print axioms Displays.display8
#print axioms Displays.display9
#print axioms Displays.display9_equal_iff
#print axioms Displays.display10
#print axioms Displays.display11
#print axioms Displays.display12
#print axioms Displays.display13
#print axioms Displays.display14
#print axioms Displays.display14_at_c1
#print axioms Displays.display24
#print axioms Displays.display23
#print axioms Displays.display23_from_lines
#print axioms Displays.displayC1
#print axioms Displays.displayC2
#print axioms Displays.displayC3
#print axioms Displays.displayC3_justification
#print axioms Displays.display16
#print axioms Displays.display16_differs
#print axioms Displays.tag_swap_by_second_partition
#print axioms Displays.display17
#print axioms Displays.display17_no_third
#print axioms Displays.display18
#print axioms Displays.display18_M
#print axioms Displays.display19
#print axioms Displays.display19_differs
#print axioms Displays.display20
#print axioms Displays.display21
#print axioms Displays.display21_uneven
#print axioms Displays.display22_nu
#print axioms Displays.display22_yours
#print axioms Displays.display6
#print axioms Displays.edt_price
#print axioms Displays.display7
#print axioms Displays.display7_contradicts_five
#print axioms Displays.display25
#print axioms Displays.sure_thing_n
#print axioms Displays.displayA1
#print axioms Displays.displayA3
#print axioms Displays.displayA4
#print axioms Displays.displayS5
#print axioms Displays.modelC_recording
#print axioms Displays.modelC_cells
#print axioms Displays.modelC_construction
#print axioms Displays.modelC_second
#print axioms Displays.modelC_display13
#print axioms Displays.modelC_tag_swap
#print axioms Displays.display14_every_urn
#print axioms Displays.display14_C_certain
#print axioms Displays.display22_by_second_partition
#print axioms Displays.modelC99_display22
#print axioms Displays.display21_uneven_measure
#print axioms Displays.display19_limit
#print axioms Displays.footnote_die
#print axioms Displays.footnote_toy
#print axioms Displays.brief_sequence
#print axioms Displays.gas_manifesto
#print axioms Displays.gas_where_urn
#print axioms Displays.gas_egoist
#print axioms Displays.gas_whether_urn
