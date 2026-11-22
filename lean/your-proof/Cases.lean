/-
  The cases and the remaining sentences of the paper "Your proof", checked in Lean 4.36.0 with
  nothing beyond Lean's own library. Line numbers are those of the paper's LaTeX source of
  22 November 2026.
  Stand-alone: the `Measure` structure and the lemmas it needs are copied from YourProof.lean
  and Displays.lean.

  The letters are the paper's: `π` is your measure (`\prsb`), and `Pr` is the recording's
  (`\prany`). Each theorem's comment quotes the sentence it states, with its line in the
  snapshot, and names every choice made in stating it. What Lean certifies is that each
  statement follows from what is written in front of it. That a statement says what the
  paper's sentence says is checked by reading the two side by side.

  Where the paper describes a case with chances, the case is built as a finite model: a list of
  points with weights (`ind` is 1 on a true statement and 0 on a false one), and the values are
  computed on it.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Cases

/-! ## The measure (copied from YourProof.lean / Displays.lean) -/

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

theorem arithEdge (PX x1 x2 e ne c : Rat) (s : PX = x1 + x2) (cc : e + ne = 1) (he : e = 1)
    (n : x2 ≤ ne) (p : 0 ≤ x2) (h : x1 / e = c) : PX = c := by grind

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

/-- Sure Thing over two cells that partition the measure (copied from YourProof.lean). -/
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

/-- Total probability (copied from YourProof.lean). -/
theorem total_probability {X E : Ω → Prop} (hX : m.ev X) (hE : m.ev E)
    (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0) :
    m.P X = m.P E * m.cond X E + m.P (fun ω => ¬ E ω) * m.cond X (fun ω => ¬ E ω) := by
  have s := m.split hX hE
  unfold cond
  exact arithTP _ _ _ _ _ s hE0 hE1

/-- In any measure in which `E` is certain and `X` has the ratio `c` given `E`, `X` has `c`
    (copied from YourProof.lean). -/
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

/-! ## Finite models (copied from Displays.lean) -/

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

theorem pos_div (x y : Rat) (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  have h := Rat.mul_pos hx (Rat.inv_pos.mpr hy)
  rw [Rat.div_def]; exact h

theorem nn_mul (x y : Rat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := Rat.mul_nonneg hx hy

/-! ## Part 1 (a) and (j): sections 1-2 and (B2), on the model of Appendix B

The recording's measure on the four outcomes and yours on the six points, copied from
YourProof.lean (`PrModel`, `piModel q`). -/

section AppB

/-- The four outcomes: `R1 = H∧C`, `R2 = H∧¬C`, `R3 = ¬H∧C`, `R4 = ¬H∧¬C` (Appendix B). -/
inductive Outcome | R1 | R2 | R3 | R4
  deriving DecidableEq

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

def Hout : Outcome → Prop | .R1 => True | .R2 => True | .R3 => False | .R4 => False
def Cout : Outcome → Prop | .R1 => True | .R2 => False | .R3 => True | .R4 => False
/-- `[M]`, you are awakened on Monday, on the outcomes: heads with a Monday ball, or tails
    (section 1.3: a waking on Monday on `H∧C`, `¬H∧C`, `¬H∧¬C`). -/
def Mout : Outcome → Prop := fun n => (Hout n ∧ Cout n) ∨ ¬ Hout n
/-- `[T]`, you are awakened on Tuesday: heads with a Tuesday ball, or tails. -/
def Tout : Outcome → Prop := fun n => (Hout n ∧ ¬ Cout n) ∨ ¬ Hout n

/-- The six points (B1): an outcome together with a day on which it has a waking. -/
inductive Point | R1M | R2T | R3M | R3T | R4M | R4T
  deriving DecidableEq

/-- The map that forgets the day, `p(R^n, D) = R^n` (source line 1281). -/
def pmap : Point → Outcome
  | .R1M => .R1 | .R2T => .R2 | .R3M => .R3 | .R3T => .R3 | .R4M => .R4 | .R4T => .R4

/-- The sets of (B2), written out point by point as the display lists them. -/
def Hpt : Point → Prop | .R1M => True | .R2T => True | _ => False
def Cpt : Point → Prop | .R1M => True | .R3M => True | .R3T => True | _ => False
def Mpt : Point → Prop | .R2T => False | _ => True
def Tpt : Point → Prop | .R1M => False | _ => True
def apt : Point → Prop | .R1M => True | .R3M => True | .R4M => True | _ => False
def bpt : Point → Prop | .R2T => True | .R3T => True | .R4T => True | _ => False

/-- Your measure on the six points (B3): `q/3` on each Monday point, `(1-q)/3` on each Tuesday
    point (copied from YourProof.lean). -/
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

/-- **(B2) in sets**, Appendix B, source lines 1274-1281: "An event of the experiment contains
    every point of an outcome of which it contains one; `[M]` contains `R^1, R^3, R^4` ... and
    `[T]` contains `R^2, R^3, R^4` ...; `a` is the Monday points and `b` the Tuesday points. So
    `a ∩ b = ∅` and `a ∪ b = S`, while `[M] ∩ [T]` is the four tails points; and
    `p(a) ∩ p(b) = {R^3, R^4}`: on the four outcomes alone there is no `a`."
    Statement: the point sets `H`, `C`, `[M]`, `[T]` of (B2) are the preimages under `p` of the
    outcome events of section 1.3 (`Mout = (H∧C) ∨ ¬H`, `Tout = (H∧¬C) ∨ ¬H`); `a ∩ b = ∅`,
    `a ∪ b = S`; `[M] ∩ [T]` is the set of tails points; an outcome is in `p(a)` and in `p(b)`
    iff it is `R^3` or `R^4`; and `a` is not the preimage of any set of outcomes.
    Choice: "contains every point of an outcome of which it contains one" is stated as being a
    preimage under `p`. -/
theorem B2_sets :
    (∀ x, Hpt x ↔ Hout (pmap x)) ∧ (∀ x, Cpt x ↔ Cout (pmap x)) ∧
    (∀ x, Mpt x ↔ Mout (pmap x)) ∧ (∀ x, Tpt x ↔ Tout (pmap x)) ∧
    (∀ x, ¬ (apt x ∧ bpt x)) ∧ (∀ x, apt x ∨ bpt x) ∧
    (∀ x, (Mpt x ∧ Tpt x) ↔ ¬ Hpt x) ∧
    (∀ n, ((∃ x, apt x ∧ pmap x = n) ∧ (∃ y, bpt y ∧ pmap y = n)) ↔ (n = .R3 ∨ n = .R4)) ∧
    ¬ (∃ A : Outcome → Prop, ∀ x, apt x ↔ A (pmap x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp [Hpt, Hout, pmap]
  · intro x; cases x <;> simp [Cpt, Cout, pmap]
  · intro x; cases x <;> simp [Mpt, Mout, Hout, Cout, pmap]
  · intro x; cases x <;> simp [Tpt, Tout, Hout, Cout, pmap]
  · intro x; cases x <;> simp [apt, bpt]
  · intro x; cases x <;> simp [apt, bpt]
  · intro x; cases x <;> simp [Mpt, Tpt, Hpt]
  · intro n; cases n
    · simp only [reduceCtorEq, or_self, iff_false]
      intro ⟨⟨_, _, _⟩, ⟨y, hy, e⟩⟩; cases y <;> simp_all [bpt, pmap]
    · simp only [reduceCtorEq, or_self, iff_false]
      intro ⟨⟨x, hx, e⟩, _⟩; cases x <;> simp_all [apt, pmap]
    · simp only [true_or, iff_true]
      exact ⟨⟨.R3M, by simp [apt], rfl⟩, ⟨.R3T, by simp [bpt], rfl⟩⟩
    · simp only [or_true, iff_true]
      exact ⟨⟨.R4M, by simp [apt], rfl⟩, ⟨.R4T, by simp [bpt], rfl⟩⟩
  · intro ⟨A, hA⟩
    have h1 := (hA .R3M).mp (by simp [apt])
    have h2 := (hA .R3T).mpr (by simpa [pmap] using h1)
    simp [apt] at h2

/-- **Sections 1-2 on the model**, source line 253: "So has `[M] ∨ [T]` [value 1] ...
    `[M] ∧ [T]`, by contrast, is left open; it is tails, and so `π([M] ∧ [T]) < 1`"; source line
    247 (the construction): "`π([M] | a) = 1` ... `π([T] | b) = 1`"; source lines 255 and 291:
    "`a` or `b` exhausts the possibilities in `π`, but they cannot both take place", i.e. (4).
    Statement, on `piModel q` at every `0 < q < 1`: `π([M] ∨ [T]) = 1`, `π([M] ∧ [T]) = 2/3`
    (the two tails points of each day), which is `< 1`; `π([M] | a) = 1`, `π([T] | b) = 1`;
    `π(a ∧ b) = 0`, `π(a ∨ b) = 1`, `π(a) = q`, `π(b) = 1 - q`.
    Existing: `piModel_values` (YourProof.lean) has `π(a) = q`, `π(b) = 1-q`, `π(a∧b) = 0`,
    `π(a∨b) = 1`; repeated here so that the model has all of section 1.4 in one place. -/
theorem sec1_on_model (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) :
    (piModel q hq0 hq1).P (fun x => Mpt x ∨ Tpt x) = 1 ∧
    (piModel q hq0 hq1).P (fun x => Mpt x ∧ Tpt x) = 2/3 ∧
    (piModel q hq0 hq1).P (fun x => Mpt x ∧ Tpt x) < 1 ∧
    (piModel q hq0 hq1).cond Mpt apt = 1 ∧ (piModel q hq0 hq1).cond Tpt bpt = 1 ∧
    (piModel q hq0 hq1).P (fun x => apt x ∧ bpt x) = 0 ∧
    (piModel q hq0 hq1).P (fun x => apt x ∨ bpt x) = 1 ∧
    (piModel q hq0 hq1).P apt = q ∧ (piModel q hq0 hq1).P bpt = 1 - q := by
  simp only [piModel, Measure.cond, Mpt, Tpt, apt, bpt, ind_true, ind_false, and_self, and_true,
    and_false, or_true, or_false, true_or, false_or, true_and, false_and]
  grind

end AppB

/-! ## Product models on two, three and four coordinates

Most cases in the paper are independent draws: a coin, a ball, a side, a pick. A point is a
tuple of booleans, one per draw, and its weight is the product of the draws' probabilities
(`wt x true = x`, `wt x false = 1 - x`). Independence of the draws is built in this way. -/

/-- The probability of one draw's value: `x` for `true`, `1 - x` for `false`. -/
def wt (x : Rat) : Bool → Rat
  | true => x
  | false => 1 - x

theorem wt_nonneg (x : Rat) (h0 : 0 ≤ x) (h1 : x ≤ 1) (b : Bool) : 0 ≤ wt x b := by
  cases b <;> simp only [wt] <;> grind

theorem wt3_nonneg (x y z : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (a b c : Bool) : 0 ≤ wt x a * wt y b * wt z c :=
  nn_mul _ _ (nn_mul _ _ (wt_nonneg x hx0 hx1 a) (wt_nonneg y hy0 hy1 b)) (wt_nonneg z hz0 hz1 c)

/-- Three independent draws with probabilities `x`, `y`, `z` of `true`. -/
noncomputable def prod3 (x y z : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : Measure (Bool × Bool × Bool) where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E =>
      wt x true * wt y true * wt z true * ind (E (true, true, true))
    + wt x true * wt y true * wt z false * ind (E (true, true, false))
    + wt x true * wt y false * wt z true * ind (E (true, false, true))
    + wt x true * wt y false * wt z false * ind (E (true, false, false))
    + wt x false * wt y true * wt z true * ind (E (false, true, true))
    + wt x false * wt y true * wt z false * ind (E (false, true, false))
    + wt x false * wt y false * wt z true * ind (E (false, false, true))
    + wt x false * wt y false * wt z false * ind (E (false, false, false))
  nonneg := by
    intro A _
    have n := wt3_nonneg x y z hx0 hx1 hy0 hy1 hz0 hz1
    have h1 := wind_nonneg _ (n true true true) (A (true, true, true))
    have h2 := wind_nonneg _ (n true true false) (A (true, true, false))
    have h3 := wind_nonneg _ (n true false true) (A (true, false, true))
    have h4 := wind_nonneg _ (n true false false) (A (true, false, false))
    have h5 := wind_nonneg _ (n false true true) (A (false, true, true))
    have h6 := wind_nonneg _ (n false true false) (A (false, true, false))
    have h7 := wind_nonneg _ (n false false true) (A (false, false, true))
    have h8 := wind_nonneg _ (n false false false) (A (false, false, false))
    grind
  total := by simp only [ind_true, wt]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h (true, true, true)); have h2 := ind_or (h (true, true, false))
    have h3 := ind_or (h (true, false, true)); have h4 := ind_or (h (true, false, false))
    have h5 := ind_or (h (false, true, true)); have h6 := ind_or (h (false, true, false))
    have h7 := ind_or (h (false, false, true)); have h8 := ind_or (h (false, false, false))
    simp only [h1, h2, h3, h4, h5, h6, h7, h8]; grind

/-- Two independent draws with probabilities `x`, `y` of `true`. -/
noncomputable def prod2 (x y : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Measure (Bool × Bool) where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E =>
      wt x true * wt y true * ind (E (true, true)) + wt x true * wt y false * ind (E (true, false))
    + wt x false * wt y true * ind (E (false, true)) + wt x false * wt y false * ind (E (false, false))
  nonneg := by
    intro A _
    have n := fun a b => nn_mul _ _ (wt_nonneg x hx0 hx1 a) (wt_nonneg y hy0 hy1 b)
    have h1 := wind_nonneg _ (n true true) (A (true, true))
    have h2 := wind_nonneg _ (n true false) (A (true, false))
    have h3 := wind_nonneg _ (n false true) (A (false, true))
    have h4 := wind_nonneg _ (n false false) (A (false, false))
    grind
  total := by simp only [ind_true, wt]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h (true, true)); have h2 := ind_or (h (true, false))
    have h3 := ind_or (h (false, true)); have h4 := ind_or (h (false, false))
    simp only [h1, h2, h3, h4]; grind

/-- Four independent draws with probabilities `x`, `y`, `z`, `v` of `true`. -/
noncomputable def prod4 (x y z v : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : Measure (Bool × Bool × Bool × Bool) where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E =>
      wt x true * wt y true * wt z true * wt v true * ind (E (true, true, true, true))
    + wt x true * wt y true * wt z true * wt v false * ind (E (true, true, true, false))
    + wt x true * wt y true * wt z false * wt v true * ind (E (true, true, false, true))
    + wt x true * wt y true * wt z false * wt v false * ind (E (true, true, false, false))
    + wt x true * wt y false * wt z true * wt v true * ind (E (true, false, true, true))
    + wt x true * wt y false * wt z true * wt v false * ind (E (true, false, true, false))
    + wt x true * wt y false * wt z false * wt v true * ind (E (true, false, false, true))
    + wt x true * wt y false * wt z false * wt v false * ind (E (true, false, false, false))
    + wt x false * wt y true * wt z true * wt v true * ind (E (false, true, true, true))
    + wt x false * wt y true * wt z true * wt v false * ind (E (false, true, true, false))
    + wt x false * wt y true * wt z false * wt v true * ind (E (false, true, false, true))
    + wt x false * wt y true * wt z false * wt v false * ind (E (false, true, false, false))
    + wt x false * wt y false * wt z true * wt v true * ind (E (false, false, true, true))
    + wt x false * wt y false * wt z true * wt v false * ind (E (false, false, true, false))
    + wt x false * wt y false * wt z false * wt v true * ind (E (false, false, false, true))
    + wt x false * wt y false * wt z false * wt v false * ind (E (false, false, false, false))
  nonneg := by
    intro A _
    have n := fun a b c d => nn_mul _ _ (wt3_nonneg x y z hx0 hx1 hy0 hy1 hz0 hz1 a b c)
      (wt_nonneg v hv0 hv1 d)
    have h0 := wind_nonneg _ (n true true true true) (A (true, true, true, true))
    have h1 := wind_nonneg _ (n true true true false) (A (true, true, true, false))
    have h2 := wind_nonneg _ (n true true false true) (A (true, true, false, true))
    have h3 := wind_nonneg _ (n true true false false) (A (true, true, false, false))
    have h4 := wind_nonneg _ (n true false true true) (A (true, false, true, true))
    have h5 := wind_nonneg _ (n true false true false) (A (true, false, true, false))
    have h6 := wind_nonneg _ (n true false false true) (A (true, false, false, true))
    have h7 := wind_nonneg _ (n true false false false) (A (true, false, false, false))
    have h8 := wind_nonneg _ (n false true true true) (A (false, true, true, true))
    have h9 := wind_nonneg _ (n false true true false) (A (false, true, true, false))
    have h10 := wind_nonneg _ (n false true false true) (A (false, true, false, true))
    have h11 := wind_nonneg _ (n false true false false) (A (false, true, false, false))
    have h12 := wind_nonneg _ (n false false true true) (A (false, false, true, true))
    have h13 := wind_nonneg _ (n false false true false) (A (false, false, true, false))
    have h14 := wind_nonneg _ (n false false false true) (A (false, false, false, true))
    have h15 := wind_nonneg _ (n false false false false) (A (false, false, false, false))
    grind
  total := by simp only [ind_true, wt]; grind
  add := by
    intro A B _ _ h
    have h0 := ind_or (h (true, true, true, true))
    have h1 := ind_or (h (true, true, true, false))
    have h2 := ind_or (h (true, true, false, true))
    have h3 := ind_or (h (true, true, false, false))
    have h4 := ind_or (h (true, false, true, true))
    have h5 := ind_or (h (true, false, true, false))
    have h6 := ind_or (h (true, false, false, true))
    have h7 := ind_or (h (true, false, false, false))
    have h8 := ind_or (h (false, true, true, true))
    have h9 := ind_or (h (false, true, true, false))
    have h10 := ind_or (h (false, true, false, true))
    have h11 := ind_or (h (false, true, false, false))
    have h12 := ind_or (h (false, false, true, true))
    have h13 := ind_or (h (false, false, true, false))
    have h14 := ind_or (h (false, false, false, true))
    have h15 := ind_or (h (false, false, false, false))
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]; grind

/-! ## Section 3.1: Gilad's room and Gilad's box (and their returns in sections 7 and 7.5) -/

section Gilad

/-- A point of Gilad's room: (the coin lands heads, the urn's ball is `Monday`, your side is
    `Monday`). -/
abbrev GPt := Bool × Bool × Bool

/-- Gilad's room with the urn at `c` (the probability of a `Monday` ball) and your side `Monday`
    with probability `σ`; coin, urn and side independent ("the two draws are run separately";
    "Sides were assigned before the toss and the draw"). -/
noncomputable def gilad (c σ : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    Measure GPt :=
  prod3 (1/2) c σ (by grind) (by grind) hc0 hc1 hσ0 hσ1

def gH : GPt → Prop := fun p => p.1 = true
def gC : GPt → Prop := fun p => p.2.1 = true
def gS : GPt → Prop := fun p => p.2.2 = true
/-- You hear the recording (you are in the room; in Gilad's box, a ball is in your box): tails,
    or heads with the urn's ball naming your side. -/
def gIn : GPt → Prop := fun p => p.1 = false ∨ (p.2.1 = p.2.2)
/-- Your partner is behind the wall (the other box holds a ball): tails, or heads with the urn's
    ball naming the other side. -/
def gOther : GPt → Prop := fun p => p.1 = false ∨ (p.2.1 ≠ p.2.2)

theorem half_bounds : (0:Rat) ≤ 1/2 ∧ (1/2:Rat) ≤ 1 := by grind

/-- **Gilad's room, section 3.1**, source line 360: "on either side we find Amin's ratios,
    `Pr(H | [M]) = Pr(H | [T]) = 1/3`. Sure Thing ... is a proof that 1/3 is the couple's game
    answer to GILAD'S Q. The probability that your partner is behind the wall is 2/3."
    Source line 362: "you are at 1/3 after learning what your side is called (regardless)."
    Statement, on the model at the even urn and even side: heads has 1/3 given you are in the
    room and on the `Monday` side, 1/3 given the `Tuesday` side, 1/3 given you are in the room;
    your partner is behind the wall with 2/3 given you are in the room.
    Choices: the urn is even and the side is assigned with even odds (footnote, source line
    808: "determined randomly with even odds"); "in the room" is the event that you hear the
    recording (a cell of the model, not a certainty: the values are conditional on it). -/
theorem gilad_room :
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gH
      (fun p => gIn p ∧ gS p) = 1/3 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gH
      (fun p => gIn p ∧ ¬ gS p) = 1/3 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gH gIn = 1/3 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gOther gIn
      = 2/3 := by
  simp [gilad, prod3, Measure.cond, gH, gS, gIn, gOther, wt, ind_true, ind_false]
  grind

/-- **The urn left uneven, section 3.1**, source line 364: "`Monday` balls were not stipulated
    to be evenly distributed with `Tuesday` within the urn. Ultimately ... it does not matter for
    the answer to GILAD'S Q."
    Statement, at every urn `0 ≤ c ≤ 1` with the side at even odds: heads has `c/(1+c)` on the
    `Monday` side, `(1-c)/(2-c)` on the `Tuesday` side, 1/3 in the room; the `Monday` side has
    `(1+c)/3` given you are in the room.
    Choice: the side at even odds, as in the footnote of source line 808. -/
theorem gilad_any_urn (c : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (gilad c (1/2) hc0 hc1 half_bounds.1 half_bounds.2).cond gH (fun p => gIn p ∧ gS p)
      = c/(1+c) ∧
    (gilad c (1/2) hc0 hc1 half_bounds.1 half_bounds.2).cond gH (fun p => gIn p ∧ ¬ gS p)
      = (1-c)/(2-c) ∧
    (gilad c (1/2) hc0 hc1 half_bounds.1 half_bounds.2).cond gH gIn = 1/3 ∧
    (gilad c (1/2) hc0 hc1 half_bounds.1 half_bounds.2).cond gS gIn = (1+c)/3 := by
  simp [gilad, prod3, Measure.cond, gH, gS, gIn, wt, ind_true, ind_false]
  grind

/-- **Gilad's box, section 3.1**, source line 377: "A ball in your box has probability 1/2 under
    heads and 1 under tails, so heads is 1/3, and the other box holds a ball with 2/3."
    Statement, on the same model (a ball in your box is `gIn`): `π(ball | H) = 1/2`,
    `π(ball | ¬H) = 1`, `π(H | ball) = 1/3`, `π(other box has a ball | ball) = 2/3`.
    Choice: the urn even and the box assigned with even odds. -/
theorem gilad_box :
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gIn gH = 1/2 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gIn
      (fun p => ¬ gH p) = 1 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gH gIn = 1/3 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gOther gIn
      = 2/3 := by
  simp [gilad, prod3, Measure.cond, gH, gIn, gOther, wt, ind_true, ind_false]
  grind

/-- **Gilad's urn with `Monday` balls only, section 7**, source line 807: "Whoever is on Monday's
    side and knows it's this side is the same as Beauty being informed this is a Monday awakening
    ...: 1/2. Whoever is on Tuesday's side and knows it is Beauty told it is Tuesday: the
    probability of a heads toss is 0. You, not knowing which side you're on, are Beauty at a
    waking: 1/3."
    Source line 943 (section 7.5): "`ρ` ... is the probability `s` that your side is Monday's,
    and with Monday balls only the room gives heads `s/(1+s)`, which is (21). The side was
    assigned before the toss and nothing distinguishes you from your partner, so `s = 1/2`."
    Statement, at `c = 1` and side `Monday` with probability `σ`, `0 < σ < 1`: heads 1/2 on the
    `Monday` side, 0 on the `Tuesday` side, `σ/(1+σ)` in the room; at `σ = 1/2` that is 1/3. -/
theorem gilad_monday_only (σ : Rat) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (gilad 1 σ (by grind) (by grind) (by grind) (by grind)).cond gH (fun p => gIn p ∧ gS p) = 1/2 ∧
    (gilad 1 σ (by grind) (by grind) (by grind) (by grind)).cond gH (fun p => gIn p ∧ ¬ gS p) = 0 ∧
    (gilad 1 σ (by grind) (by grind) (by grind) (by grind)).cond gH gIn = σ/(1+σ) ∧
    (σ = 1/2 → σ/(1+σ) = 1/3) := by
  simp [gilad, prod3, Measure.cond, gH, gS, gIn, wt, ind_true, ind_false]
  grind

end Gilad

/-! ## Section 3: a quick check from the outside (on the Appendix B model) -/

section Outside

theorem arith_sum_le (A B C D : Rat) (a : A ≤ B) (b : C ≤ D) (h : 2*(A + C) = 1)
    (e : 3*(B + D) = 1) : False := by grind

/-- **My two guesses, section 3**, source line 310: "If `[M]` is correct, `[T]` takes place as
    well only on tails, so by ASSUM-1 `Pr([T] | [M]) = Pr(¬H | [M]) = (1/2)/(3/4) = 2/3`, tails
    2/3, heads 1/3. My second guess mirrors the first: `Pr([M] | [T]) = Pr(¬H | [T]) =
    (1/2)/(3/4) = 2/3`, tails 2/3, heads 1/3."
    Source line 639 (section 5.1): "Of the four outcomes of the coin and the ball, a quarter
    each, three have Monday's announcement and one of those has heads."
    Statement, on the recording's model of Appendix B: `[M] ∧ [T]` is tails as sets;
    `Pr(¬H ∧ [M]) = 1/2`, `Pr([M]) = 3/4`, `Pr([T] | [M]) = Pr(¬H | [M]) = 2/3`,
    `Pr(H | [M]) = 1/3`, `Pr(H ∧ [M]) = 1/4`; the same with the days exchanged. -/
theorem two_guesses :
    (∀ n, (Mout n ∧ Tout n) ↔ ¬ Hout n) ∧
    PrModel.P (fun n => ¬ Hout n ∧ Mout n) = 1/2 ∧ PrModel.P Mout = 3/4 ∧
    PrModel.cond Tout Mout = 2/3 ∧ PrModel.cond (fun n => ¬ Hout n) Mout = 2/3 ∧
    PrModel.cond Hout Mout = 1/3 ∧ PrModel.P (fun n => Hout n ∧ Mout n) = 1/4 ∧
    PrModel.P (fun n => ¬ Hout n ∧ Tout n) = 1/2 ∧ PrModel.P Tout = 3/4 ∧
    PrModel.cond Mout Tout = 2/3 ∧ PrModel.cond (fun n => ¬ Hout n) Tout = 2/3 ∧
    PrModel.cond Hout Tout = 1/3 := by
  refine ⟨fun n => by cases n <;> simp [Mout, Tout, Hout, Cout], ?_⟩
  simp [PrModel, Measure.cond, Mout, Tout, Hout, Cout, ind_true, ind_false]
  grind

/-- **The footnote to "No other answer is possible", section 3**, source line 316:
    "`π(H)` is the sum over the two guesses, each weighted by its probability:
    `q·1/3 + (1-q)·1/3 = 1/3` at every `q`. For 1/2, one of two things would be needed. One guess
    would have to give `H` more than 1/3 ... Or a third guess would be needed".
    Statement: the sum is 1/3 at every `q`; and with two guesses only, weights `q`, `1-q` in
    `[0,1]`, a sum of 1/2 needs one of the two values above 1/3.
    Choice: "a third guess" is not stated (it is the alternative to the two-cell sum). -/
theorem guesses_footnote :
    (∀ q : Rat, q * (1/3) + (1-q) * (1/3) = 1/3) ∧
    (∀ q x y : Rat, 0 ≤ q → q ≤ 1 → q * x + (1-q) * y = 1/2 → 1/3 < x ∨ 1/3 < y) := by
  refine ⟨fun q => by grind, fun q x y h0 h1 h => ?_⟩
  cases Classical.em (1/3 < x) with
  | inl hx => exact Or.inl hx
  | inr hx =>
    cases Classical.em (1/3 < y) with
    | inl hy => exact Or.inr hy
    | inr hy =>
      have a : q * x ≤ q * (1/3) := Rat.mul_le_mul_of_nonneg_left (by grind) h0
      have b : (1-q) * y ≤ (1-q) * (1/3) := Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
      exact (arith_sum_le _ _ _ _ a b (by grind) (by grind)).elim

/-- Jill's measure: the recording's measure conditioned on `[M]` (Jeffrey's rule at `u = 1` is
    not needed: the conditional measure is written out). -/
noncomputable def jill : Measure Outcome where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => PrModel.cond E Mout
  nonneg := by
    intro A _
    simp only [PrModel, Measure.cond, Mout, Hout, Cout, ind_true, ind_false]
    have h1 := wind_nonneg (1/4) (by grind) (A .R1 ∧ (True ∧ True ∨ ¬ True))
    have h3 := wind_nonneg (1/4) (by grind) (A .R3 ∧ (False ∧ True ∨ ¬ False))
    have h4 := wind_nonneg (1/4) (by grind) (A .R4 ∧ (False ∧ False ∨ ¬ False))
    simp only [and_true, true_and, and_false, false_and, not_true_eq_false, not_false_eq_true,
      or_false, false_or, or_true, true_or] at h1 h3 h4 ⊢
    simp only [ind_true, ind_false]
    have h2 : (1:Rat)/4 * ind (A .R2 ∧ (True ∧ False ∨ ¬ True)) = 0 := by simp [ind]
    grind
  total := by simp [PrModel, Measure.cond, Mout, Hout, Cout, ind_true, ind_false]; grind
  add := by
    intro A B _ _ h
    simp only [Measure.cond]
    have e := PrModel.add (A := fun n => A n ∧ Mout n) (B := fun n => B n ∧ Mout n) trivial trivial
      (fun n x => h n ⟨x.1.1, x.2.1⟩)
    have e2 : PrModel.P (fun n => (A n ∨ B n) ∧ Mout n)
        = PrModel.P (fun n => (A n ∧ Mout n) ∨ (B n ∧ Mout n)) :=
      PrModel.Pcongr (fun n => by grind)
    rw [e2, e]; grind

/-- **Jack and Jill, section 3**, source line 325: "`π_Jack = Pr`, the measure of ASSUM-1 alone
    ... and `π_Jack(H) = 1/2`. ... `π_Jill = Pr(· | [M])`, and `π_Jill(H) = 1/3`." ... "In `a`,
    your measure is Jill's. ... `π(X | a) = π_Jill(X) = Pr(X | [M])`. In `b`, your value is
    `Pr(X | [T])`. Heads is 1/3 in each, and 1/3 by Sure Thing."
    Statement: `Pr(H) = 1/2`; Jill's measure (the recording's conditioned on `[M]`) gives `[M]`
    the value 1 and heads 1/3, and equals `Pr(· | [M])` on every event; on the Appendix B model
    at every `q`, `π(H | a) = π_Jill(H)`, `π(H | b) = Pr(H | [T]) = 1/3` and `π(H) = 1/3`.
    Choice: "your measure is Jill's in `a`" is stated at `X = H` on the model; at all four
    outcomes it is `model_construction_all` of YourProof.lean. -/
theorem jack_and_jill (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) :
    PrModel.P Hout = 1/2 ∧ jill.P Mout = 1 ∧ jill.P Hout = 1/3 ∧
    (∀ X, jill.P X = PrModel.cond X Mout) ∧
    (piModel q hq0 hq1).cond Hpt apt = jill.P Hout ∧
    (piModel q hq0 hq1).cond Hpt bpt = PrModel.cond Hout Tout ∧
    PrModel.cond Hout Tout = 1/3 ∧ (piModel q hq0 hq1).P Hpt = 1/3 := by
  refine ⟨?_, ?_, ?_, fun X => rfl, ?_, ?_, ?_, ?_⟩ <;>
  simp [jill, PrModel, piModel, Measure.cond, Mout, Tout, Hout, Cout, Hpt, apt, bpt, ind_true,
    ind_false] <;> grind

/-- **If it is Tuesday and Jill remembers Monday, section 3**, source line 329: "her measure
    would have provably different values: heads at 0 if you were awake on Monday, and at 1 if
    you were asleep on either day."
    Statement, on the recording's model: `Pr(H | [T] ∧ [M]) = 0`; `Pr(H | [T] ∧ ¬[M]) = 1`;
    `Pr(H | ¬[M] ∨ ¬[T]) = 1`.
    Choices: "it is Tuesday" with you awake is `[T]`; "awake on Monday" is `[M]`; "asleep on
    either day" is `¬[M] ∨ ¬[T]` (stated also with `[T]` and asleep on Monday). -/
theorem jill_remembers :
    PrModel.cond Hout (fun n => Tout n ∧ Mout n) = 0 ∧
    PrModel.cond Hout (fun n => Tout n ∧ ¬ Mout n) = 1 ∧
    PrModel.cond Hout (fun n => ¬ Mout n ∨ ¬ Tout n) = 1 := by
  simp [PrModel, Measure.cond, Mout, Tout, Hout, Cout, ind_true, ind_false]
  grind

end Outside

/-! ## Section 4: the price, and EDT's price per run -/

section EDT

/-- **Any other price, section 4**, source line 421: "At any other price one side has a positive
    expected value and the other a negative one, and hating money only swaps which is which."
    Statement: with `π(H) = 1/3` (5), the ticket at price `x` is worth `1/3 - x` to the buyer
    (display (6)) and `x - 1/3` to the seller; at every `x ≠ 1/3` one of the two is positive and
    the other negative.
    Choice: the seller's value is the negation of the buyer's (the two sides of one ticket). -/
theorem other_price (x : Rat) (hx : x ≠ 1/3) :
    (1/3 - x > 0 ∧ x - 1/3 < 0) ∨ (1/3 - x < 0 ∧ x - 1/3 > 0) := by
  cases Classical.em (x < 1/3) with
  | inl h => exact Or.inl ⟨by grind, by grind⟩
  | inr h => exact Or.inr ⟨by grind, by grind⟩

/-- **EDT's price per run, section 4**, source line 433: "At 1/5, the buyer at every waking gains
    four fifths on the single heads ticket and loses two fifths on the two tails tickets
    together. By the recording, the coin outcomes are equally probable. So the buyer gains 1/5
    per run on average, and the seller loses that amount. At 1/3 neither side does."
    Statement: the buyer at every waking holds one ticket on heads and two on tails; per run
    the buyer's payoff at price `x` is `1 - x` on heads and `-2x` on tails; with the recording's
    `Pr(H) = Pr(¬H) = 1/2` (the model of Appendix B), the buyer's expected payoff per run is
    `Pr(H)(1-x) + Pr(¬H)(-2x)`; at `x = 1/5` the heads ticket gains `4/5`, the two tails tickets
    lose `2/5`, and the expectation is `1/5` for the buyer and `-1/5` for the seller; at
    `x = 1/3` both are 0.
    Choice: the seller's payoff is the negation of the buyer's. -/
theorem edt_per_run :
    (1:Rat) - 1/5 = 4/5 ∧ (2:Rat) * (1/5) = 2/5 ∧
    PrModel.P Hout * (1 - 1/5) + PrModel.P (fun n => ¬ Hout n) * (-(2 * (1/5))) = 1/5 ∧
    -(PrModel.P Hout * (1 - 1/5) + PrModel.P (fun n => ¬ Hout n) * (-(2 * (1/5)))) = -(1/5) ∧
    PrModel.P Hout * (1 - 1/3) + PrModel.P (fun n => ¬ Hout n) * (-(2 * (1/3))) = 0 := by
  simp [PrModel, Hout, ind_true, ind_false]
  grind

end EDT

/-! ## Section 5.1: the peanut butter, the die, and the footnote on partitions -/

section Bayes

theorem arith_pb (a b xe e f g : Rat) (s1 : xe = a + b) (s2 : e = f + g) (he : e ≠ 0)
    (hf : f ≠ 0) (hg : g ≠ 0) (ind : a / e = (xe / e) * (f / e)) :
    a / f = xe / e ∧ b / g = xe / e := by
  have k : a = xe * f / e := by grind
  constructor <;> grind

/-- **The peanut butter, section 5.1**, source line 595: "take anything you are about to find out
    that is independent of the ratio, for instance whether there is any peanut butter left in the
    refrigerator. Its conjunction with `E`, and the conjunction of its negation with `E`, split
    `E` such that the distribution within each side is equal: `X` has two-thirds on each, by the
    definition of independence. So whichever you find when you open the refrigerator, if you
    learn `E`, your unconditional probability of `X` is two-thirds."
    Statement: in any standard measure, an event `F` of the same algebra that is independent of
    `X` within `E`, `π(X ∧ F | E) = π(X | E) π(F | E)`, with `π(E ∧ F)` and `π(E ∧ ¬F)` not 0,
    gives `π(X | E ∧ F) = π(X | E ∧ ¬F) = π(X | E)`; and any later measure in which `E ∧ F` (or
    `E ∧ ¬F`) is certain and the ratio is kept gives `X` the value `π(X | E)`.
    Choices: "independent of the ratio" is independence of `X` and `F` within `E` (the product
    rule of conditionals given `E`); "if you learn `E`" with the refrigerator opened is a later
    measure with `E ∧ F` (or `E ∧ ¬F`) certain and the same conditional values, as in (B). -/
theorem peanut_butter {Ω : Type} (m : Measure Ω) (X E F : Ω → Prop) (hX : m.ev X) (hE : m.ev E)
    (hF : m.ev F) (hE0 : m.P E ≠ 0) (hEF : m.P (fun ω => E ω ∧ F ω) ≠ 0)
    (hEnF : m.P (fun ω => E ω ∧ ¬ F ω) ≠ 0)
    (indep : m.cond (fun ω => X ω ∧ F ω) E = m.cond X E * m.cond F E) :
    m.cond X (fun ω => E ω ∧ F ω) = m.cond X E ∧
    m.cond X (fun ω => E ω ∧ ¬ F ω) = m.cond X E ∧
    (∀ lat : Measure Ω, lat.ev X → lat.ev (fun ω => E ω ∧ F ω) →
      lat.P (fun ω => E ω ∧ F ω) = 1 →
      lat.cond X (fun ω => E ω ∧ F ω) = m.cond X (fun ω => E ω ∧ F ω) → lat.P X = m.cond X E) ∧
    (∀ lat : Measure Ω, lat.ev X → lat.ev (fun ω => E ω ∧ ¬ F ω) →
      lat.P (fun ω => E ω ∧ ¬ F ω) = 1 →
      lat.cond X (fun ω => E ω ∧ ¬ F ω) = m.cond X (fun ω => E ω ∧ ¬ F ω) →
      lat.P X = m.cond X E) := by
  have s1 := m.split (m.ev_and hX hE) hF
  have s2 := m.split hE hF
  have e1 : m.P (fun ω => X ω ∧ (E ω ∧ F ω)) = m.P (fun ω => (X ω ∧ E ω) ∧ F ω) :=
    m.Pcongr (fun ω => by grind)
  have e2 : m.P (fun ω => X ω ∧ (E ω ∧ ¬ F ω)) = m.P (fun ω => (X ω ∧ E ω) ∧ ¬ F ω) :=
    m.Pcongr (fun ω => by grind)
  have e3 : m.P (fun ω => (X ω ∧ F ω) ∧ E ω) = m.P (fun ω => (X ω ∧ E ω) ∧ F ω) :=
    m.Pcongr (fun ω => by grind)
  have e4 : m.P (fun ω => F ω ∧ E ω) = m.P (fun ω => E ω ∧ F ω) :=
    m.Pcongr (fun ω => by grind)
  unfold Measure.cond at indep
  rw [e3, e4] at indep
  obtain ⟨r1, r2⟩ := arith_pb _ _ _ _ _ _ s1 s2 hE0 hEF hEnF indep
  have c1 : m.cond X (fun ω => E ω ∧ F ω) = m.cond X E := by
    unfold Measure.cond; rw [e1]; exact r1
  have c2 : m.cond X (fun ω => E ω ∧ ¬ F ω) = m.cond X E := by
    unfold Measure.cond; rw [e2]; exact r2
  refine ⟨c1, c2, fun lat hX' hEF' cert same => ?_, fun lat hX' hEF' cert same => ?_⟩
  · exact lat.certain_gives_ratio hX' hEF' cert (same.trans c1)
  · exact lat.certain_gives_ratio hX' hEF' cert (same.trans c2)

/-- A point of the skewed die with the refrigerator: (the face, peanut butter is left). The odd
    faces are taken together as one point; nothing in the case asks which odd face. -/
inductive Face | two | four | six | odd
  deriving DecidableEq

/-- The skewed die of source line 595 ("heavily skewed towards the even numbers and, among them,
    towards 2"): faces 2, 4, 6 at 2/5, 1/10, 1/10, the odd faces together at 2/5; the peanut
    butter left with probability `β`, independent of the die. -/
noncomputable def skewDie (β : Rat) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : Measure (Face × Bool) where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 2/5 * wt β true * ind (E (.two, true)) + 2/5 * wt β false * ind (E (.two, false))
    + 1/10 * wt β true * ind (E (.four, true)) + 1/10 * wt β false * ind (E (.four, false))
    + 1/10 * wt β true * ind (E (.six, true)) + 1/10 * wt β false * ind (E (.six, false))
    + 2/5 * wt β true * ind (E (.odd, true)) + 2/5 * wt β false * ind (E (.odd, false))
  nonneg := by
    intro A _
    have n := wt_nonneg β hβ0 hβ1
    have h1 := wind_nonneg _ (nn_mul (2/5) _ (by grind) (n true)) (A (.two, true))
    have h2 := wind_nonneg _ (nn_mul (2/5) _ (by grind) (n false)) (A (.two, false))
    have h3 := wind_nonneg _ (nn_mul (1/10) _ (by grind) (n true)) (A (.four, true))
    have h4 := wind_nonneg _ (nn_mul (1/10) _ (by grind) (n false)) (A (.four, false))
    have h5 := wind_nonneg _ (nn_mul (1/10) _ (by grind) (n true)) (A (.six, true))
    have h6 := wind_nonneg _ (nn_mul (1/10) _ (by grind) (n false)) (A (.six, false))
    have h7 := wind_nonneg _ (nn_mul (2/5) _ (by grind) (n true)) (A (.odd, true))
    have h8 := wind_nonneg _ (nn_mul (2/5) _ (by grind) (n false)) (A (.odd, false))
    grind
  total := by simp only [ind_true, wt]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h (.two, true)); have h2 := ind_or (h (.two, false))
    have h3 := ind_or (h (.four, true)); have h4 := ind_or (h (.four, false))
    have h5 := ind_or (h (.six, true)); have h6 := ind_or (h (.six, false))
    have h7 := ind_or (h (.odd, true)); have h8 := ind_or (h (.odd, false))
    simp only [h1, h2, h3, h4, h5, h6, h7, h8]; grind

def dX : Face × Bool → Prop := fun p => p.1 = .two
def dE : Face × Bool → Prop := fun p => p.1 = .two ∨ p.1 = .four ∨ p.1 = .six
def dF : Face × Bool → Prop := fun p => p.2 = true

/-- **The skewed die, section 5.1**, source lines 593-595: "`Pr(X | E) = 2/3`, where `X` is a die
    landing 2 and `E` is the event that it lands even ... the die is uneven, heavily skewed
    towards the even numbers and, among them, towards 2 ... `X` has two-thirds on each [side of
    the peanut butter]".
    Statement, on the model at every `0 < β < 1`: `Pr(E) = 3/5` (above 1/2), `Pr(X | E) = 2/3`,
    the peanut butter is independent of `X` within `E`, and `Pr(X | E ∧ F) = Pr(X | E ∧ ¬F)
    = 2/3`.
    Choice: the weights 2/5, 1/10, 1/10 on 2, 4, 6 are one die with the stated skew; the paper
    gives only the ratio 2/3. -/
theorem skewed_die (β : Rat) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (skewDie β (by grind) (by grind)).P dE = 3/5 ∧
    (skewDie β (by grind) (by grind)).cond dX dE = 2/3 ∧
    (skewDie β (by grind) (by grind)).cond (fun p => dX p ∧ dF p) dE
      = (skewDie β (by grind) (by grind)).cond dX dE * (skewDie β (by grind) (by grind)).cond dF dE ∧
    (skewDie β (by grind) (by grind)).cond dX (fun p => dE p ∧ dF p) = 2/3 ∧
    (skewDie β (by grind) (by grind)).cond dX (fun p => dE p ∧ ¬ dF p) = 2/3 := by
  simp [skewDie, Measure.cond, dX, dE, dF, wt, ind_true, ind_false]
  grind

/-- A fair die. -/
inductive Die | d1 | d2 | d3 | d4 | d5 | d6
  deriving DecidableEq

noncomputable def fairDie : Measure Die where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 1/6 * ind (E .d1) + 1/6 * ind (E .d2) + 1/6 * ind (E .d3) + 1/6 * ind (E .d4)
    + 1/6 * ind (E .d5) + 1/6 * ind (E .d6)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (1/6) (by grind) (A .d1); have h2 := wind_nonneg (1/6) (by grind) (A .d2)
    have h3 := wind_nonneg (1/6) (by grind) (A .d3); have h4 := wind_nonneg (1/6) (by grind) (A .d4)
    have h5 := wind_nonneg (1/6) (by grind) (A .d5); have h6 := wind_nonneg (1/6) (by grind) (A .d6)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .d1); have h2 := ind_or (h .d2); have h3 := ind_or (h .d3)
    have h4 := ind_or (h .d4); have h5 := ind_or (h .d5); have h6 := ind_or (h .d6)
    simp only [h1, h2, h3, h4, h5, h6]; grind

/-- **The fair die, section 5.1**, source line 601: "If one event is that a fair die is tossed and
    the other is that it lands on one, then by definition, more or less, the ratio is 1/6."
    Source line 609: "Take a fair die, `E` that it falls even, `X` that it falls on 2:
    `π(X | E) = 1/3`. To say 1/2 you need to say: wait, I learned `F` too, that it did not fall on
    4. Then what you learned is `E ∧ F`, and `X` given `E` is still 1/3".
    Statement, on the fair die (the toss certain, as the event of all six faces): `Pr(1 | tossed)
    = 1/6`; `Pr(2 | even) = 1/3`; `Pr(2 | even ∧ not 4) = 1/2`. -/
theorem fair_die :
    fairDie.cond (fun d => d = .d1) (fun _ => True) = 1/6 ∧
    fairDie.cond (fun d => d = .d2) (fun d => d = .d2 ∨ d = .d4 ∨ d = .d6) = 1/3 ∧
    fairDie.cond (fun d => d = .d2) (fun d => (d = .d2 ∨ d = .d4 ∨ d = .d6) ∧ d ≠ .d4) = 1/2 := by
  simp [fairDie, Measure.cond, ind_true, ind_false]
  grind

/-- **The footnote on partitions, section 5.1**, source line 610: "For any partition
    `E_1, E_2, ...` of positive probability, finite or not, run the proof on `E_i` against its
    complement, the union of the rest: (S1) to (S3) give `π(X | E_i)` under `E_i`, and
    `π_+(X) = π(X | E_i)` with `E_i` learned, for each `i` on its own, so nothing depends on how
    many cells there are."
    Statement: for a family of events indexed by any type `ι` (finite or not), for each `i` with
    `π(E_i)` and `π(¬E_i)` not 0: the two-cell split against the complement,
    `π(X) = π(E_i) π(X | E_i) + π(¬E_i) π(X | ¬E_i)`; and any later measure with `E_i` certain
    and the ratio kept gives `π_+(X) = π(X | E_i)`.
    Choices: "with `E_i` learned" is a later measure in which `E_i` is certain and `X` keeps its
    ratio given `E_i` (the hypothesis of (B) as YourProof.lean's `certain_gives_ratio` uses it);
    the subdivision of `E_i` (S1) is not repeated (it is `subdivision_lemma` in YourProof.lean).
    No statement sums over infinitely many cells: the measure here is finitely additive, and the
    footnote's claim is made for each `i` on its own. -/
theorem partition_footnote {Ω ι : Type} (m : Measure Ω) (X : Ω → Prop) (Es : ι → Ω → Prop)
    (hX : m.ev X) (hE : ∀ i, m.ev (Es i)) (pos : ∀ i, m.P (Es i) ≠ 0)
    (posc : ∀ i, m.P (fun ω => ¬ Es i ω) ≠ 0) (i : ι) :
    m.P X = m.P (Es i) * m.cond X (Es i)
      + m.P (fun ω => ¬ Es i ω) * m.cond X (fun ω => ¬ Es i ω) ∧
    ∀ lat : Measure Ω, lat.ev X → lat.ev (Es i) → lat.P (Es i) = 1 →
      lat.cond X (Es i) = m.cond X (Es i) → lat.P X = m.cond X (Es i) :=
  ⟨m.total_probability hX (hE i) (pos i) (posc i),
   fun lat hX' hE' cert same => lat.certain_gives_ratio hX' hE' cert same⟩

end Bayes

/-! ## Section 5.2: Amina's recording -/

section Amina

/-- Amina's case at confidence `u` that the recording is yours: the six points of Appendix B
    with your measure scaled by `u` (the recording is yours, `R`), and two points for the case in
    which it is not (heads, tails), with heads at `h` there. -/
inductive APt | R1M | R2T | R3M | R3T | R4M | R4T | nH | nT
  deriving DecidableEq

noncomputable def aminaPi (u q h : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : Measure APt where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => u*(q/3) * ind (E .R1M) + u*((1-q)/3) * ind (E .R2T) + u*(q/3) * ind (E .R3M)
    + u*((1-q)/3) * ind (E .R3T) + u*(q/3) * ind (E .R4M) + u*((1-q)/3) * ind (E .R4T)
    + (1-u)*h * ind (E .nH) + (1-u)*(1-h) * ind (E .nT)
  nonneg := by
    intro A _
    have a := nn_mul u (q/3) hu0 (by grind)
    have b := nn_mul u ((1-q)/3) hu0 (by grind)
    have c := nn_mul (1-u) h (by grind) hh0
    have d := nn_mul (1-u) (1-h) (by grind) (by grind)
    have h1 := wind_nonneg _ a (A .R1M); have h2 := wind_nonneg _ b (A .R2T)
    have h3 := wind_nonneg _ a (A .R3M); have h4 := wind_nonneg _ b (A .R3T)
    have h5 := wind_nonneg _ a (A .R4M); have h6 := wind_nonneg _ b (A .R4T)
    have h7 := wind_nonneg _ c (A .nH); have h8 := wind_nonneg _ d (A .nT)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1M); have h2 := ind_or (h .R2T); have h3 := ind_or (h .R3M)
    have h4 := ind_or (h .R3T); have h5 := ind_or (h .R4M); have h6 := ind_or (h .R4T)
    have h7 := ind_or (h .nH); have h8 := ind_or (h .nT)
    simp only [h1, h2, h3, h4, h5, h6, h7, h8]; grind

def aH : APt → Prop | .R1M => True | .R2T => True | .nH => True | _ => False
def aR : APt → Prop | .nH => False | .nT => False | _ => True
def aA : APt → Prop | .R1M => True | .R3M => True | .R4M => True | _ => False
def aB : APt → Prop | .R2T => True | .R3T => True | .R4T => True | _ => False

/-- **0.9 that Amina's recording is yours, section 5.2**, source lines 651-653: "You cannot say
    that heads is 0.9 times 1/3: heads and tails would not sum to 1 without giving tails extra
    probability. The 0.9 multiplies everything defined, heads at 1/3 and tails at 2/3 alike, and
    the remaining 0.1 is for the case in which the recording is not yours."
    Statement, on the model at `u = 9/10`, every `0 < q < 1` and every `h`: `π_A(R) = 9/10`;
    the proof runs inside `R`: `π_A(H | R ∧ a) = π_A(H | R ∧ b) = 1/3` and `π_A(H | R) = 1/3`;
    `π_A(H ∧ R) = 3/10` and `π_A(¬H ∧ R) = 6/10`; `π_A(¬R) = 1/10`; and if heads were
    `0.9 · 1/3 = 3/10`, tails would be `7/10 = 6/10 + 1/10`, i.e. `h = 0`, the whole of `¬R`
    given to tails.
    Choice: the recording's protocol inside `R` is the Appendix B model; outside `R` the coin
    has an open value `h`. -/
theorem amina_point_nine (q h : Rat) (hq0 : 0 < q) (hq1 : q < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aR = 9/10 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aH
      (fun x => aR x ∧ aA x) = 1/3 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aH
      (fun x => aR x ∧ aB x) = 1/3 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aH aR = 1/3 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P
      (fun x => aH x ∧ aR x) = 3/10 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P
      (fun x => ¬ aH x ∧ aR x) = 6/10 ∧
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P
      (fun x => ¬ aR x) = 1/10 ∧
    ((aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aH = 3/10 ↔
      ((aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P
        (fun x => ¬ aH x) = 6/10 + 1/10 ∧ h = 0)) := by
  simp [aminaPi, Measure.cond, aH, aR, aA, aB, ind_true, ind_false]
  grind

/-- **Bayes's theorem when Amin walks in, section 5.2**, source lines 657-661:
    `π_A(H | R) = π_A(R | H) π_A(H) / π_A(R) = (0.9 · 1/3)/0.9 = 1/3`. "With no bias,
    `π_A(R | H)` is the 0.9 of `π_A(R)` and the two cancel: your probability for heads was 1/3
    before he walked in. Heads at 0.9 times 1/3 would need `π_A(R | H) = 1`, heads making you
    certain of Amina."
    Statement, on the model at `u = 9/10`: Bayes's formula holds; `π_A(R | H) = 9/10` iff
    `h = 1/3` ("no bias"), and then `π_A(H) = 1/3` and the formula's value is
    `(9/10 · 1/3)/(9/10) = 1/3`; `π_A(H) = 3/10` iff `π_A(R | H) = 1`.
    Choice: "no bias" is `π_A(R | H) = π_A(R)`. -/
theorem amina_bayes (q h : Rat) (hq0 : 0 < q) (hq1 : q < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aH aR
      = (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aR aH
        * (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aH
        / (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aR ∧
    ((aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aR aH = 9/10
      ↔ h = 1/3) ∧
    (h = 1/3 → (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aH
      = 1/3) ∧
    ((9:Rat)/10 * (1/3)) / (9/10) = 1/3 ∧
    ((aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).P aH = 3/10 ↔
      (aminaPi (9/10) q h (by grind) (by grind) (by grind) (by grind) hh0 hh1).cond aR aH = 1) := by
  simp [aminaPi, Measure.cond, aH, aR, ind_true, ind_false]
  grind

/-- **The footnote on second-order probability, section 5.2**, source line 652: "you give a coin
    0.55 for heads, toss it a hundred times to check, and get 55 heads. Had you tossed it a
    thousand times and got 550, your answer ... could be just the same, 0.55."
    Statement: `550/1000 = 55/100` (0.55). (Changed after the audit of 22 Nov: the conjunct
    `55/100 = 55/100`, true by reflexivity, was dropped.) -/
theorem coin_055 : (550:Rat)/1000 = 55/100 := by grind

end Amina

/-! ## Section 5.3: Jeffrey's rule (copied from YourProof.lean) -/

section Jeffrey

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

namespace Measure

variable {Ω : Type} (m : Measure Ω)

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

/-- **Jeffrey's rule (J)** (copied from YourProof.lean): with the probability of `E` changed to
    `u`, `P_j(X) = u P_i(X | E) + (1 - u) P_i(X | ¬E)`. -/
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

/-- (J) gives `E` the value `u` (copied from YourProof.lean). -/
theorem jeffrey_E {E : Ω → Prop} (hE : m.ev E) (hE0 : m.P E ≠ 0)
    (hE1 : m.P (fun ω => ¬ E ω) ≠ 0) (u : Rat) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (m.jeffrey E hE hE0 hE1 u hu0 hu1).P E = u := by
  have e1 : (fun ω => E ω ∧ E ω) = E := by funext ω; simp
  have e2 : (fun ω => E ω ∧ ¬ E ω) = (fun (_ : Ω) => False) := by funext ω; simp
  show u * (m.P (fun ω => E ω ∧ E ω) / m.P E)
      + (1 - u) * (m.P (fun ω => E ω ∧ ¬ E ω) / m.P (fun ω => ¬ E ω)) = u
  rw [e1, e2, m.P_false]; exact arithJu u _ _ hE0

end Measure

theorem arithJzero (c nc : Rat) : (0 : Rat) * c + (1 - 0) * nc = nc := by grind

/-- **(J) at the edges, section 5.3**, source line 672: "as Jeffrey himself notes ..., when
    `u = 1` (or when it goes to 0) we have (B), by learning `E` or `¬E` respectively."
    Statement: (J) at `u = 0` gives every event its conditional value given `¬E`.
    Existing: `jeffrey_at_one` (YourProof.lean) gives the value given `E` at `u = 1`. -/
theorem jeffrey_at_zero {Ω : Type} (m : Measure Ω) {E : Ω → Prop} (hE : m.ev E)
    (hE0 : m.P E ≠ 0) (hE1 : m.P (fun ω => ¬ E ω) ≠ 0) (X : Ω → Prop) :
    (m.jeffrey E hE hE0 hE1 0 (by grind) (by grind)).P X = m.cond X (fun ω => ¬ E ω) := by
  show (0 : Rat) * m.cond X E + (1 - 0) * m.cond X (fun ω => ¬ E ω) = m.cond X (fun ω => ¬ E ω)
  exact arithJzero _ _

/-- **Conditioning commutes, section 5.3**, source line 689: "Conditioning commutes: a
    conjunction has no order. With `E` and `F` for the two things learned ..., (B) gives
    `P_j(X) = P_i(X | E ∧ F)` when `E` is learned first and `P_j(X) = P_i(X | F ∧ E)` when `F`
    is. These are one unconditional value."
    Statement: in any standard measure, `P(X | E ∧ F) = P(X | F ∧ E)`. -/
theorem conditioning_commutes {Ω : Type} (m : Measure Ω) (X E F : Ω → Prop) :
    m.cond X (fun ω => E ω ∧ F ω) = m.cond X (fun ω => F ω ∧ E ω) := by
  unfold Measure.cond
  rw [m.Pcongr (A := fun ω => X ω ∧ (E ω ∧ F ω)) (B := fun ω => X ω ∧ (F ω ∧ E ω))
    (fun ω => by grind), m.Pcongr (A := fun ω => E ω ∧ F ω) (B := fun ω => F ω ∧ E ω)
    (fun ω => by grind)]

/-- A prior on two events `E` (first coordinate) and `F` (second): `E ∧ F` and `¬E ∧ ¬F` at
    2/5 each, `E ∧ ¬F` and `¬E ∧ F` at 1/10 each (the two items bear on each other). -/
noncomputable def twoItems : Measure (Bool × Bool) where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 2/5 * ind (E (true, true)) + 1/10 * ind (E (true, false))
    + 1/10 * ind (E (false, true)) + 2/5 * ind (E (false, false))
  nonneg := by
    intro A _
    have h1 := wind_nonneg (2/5) (by grind) (A (true, true))
    have h2 := wind_nonneg (1/10) (by grind) (A (true, false))
    have h3 := wind_nonneg (1/10) (by grind) (A (false, true))
    have h4 := wind_nonneg (2/5) (by grind) (A (false, false))
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h (true, true)); have h2 := ind_or (h (true, false))
    have h3 := ind_or (h (false, true)); have h4 := ind_or (h (false, false))
    simp only [h1, h2, h3, h4]; grind

def iE : Bool × Bool → Prop := fun p => p.1 = true
def iF : Bool × Bool → Prop := fun p => p.2 = true

theorem tI_E0 : twoItems.P iE ≠ 0 := by simp [twoItems, iE, ind_true, ind_false]; grind
theorem tI_E1 : twoItems.P (fun p => ¬ iE p) ≠ 0 := by
  simp [twoItems, iE, ind_true, ind_false]; grind
theorem tI_F0 : twoItems.P iF ≠ 0 := by simp [twoItems, iF, ind_true, ind_false]; grind
theorem tI_F1 : twoItems.P (fun p => ¬ iF p) ≠ 0 := by
  simp [twoItems, iF, ind_true, ind_false]; grind

/-- (J) on `E` to 9/10, from the prior. -/
noncomputable def afterE : Measure (Bool × Bool) :=
  twoItems.jeffrey iE trivial tI_E0 tI_E1 (9/10) (by grind) (by grind)
/-- (J) on `F` to 1/5, from the prior. -/
noncomputable def afterF : Measure (Bool × Bool) :=
  twoItems.jeffrey iF trivial tI_F0 tI_F1 (1/5) (by grind) (by grind)

theorem aE_F0 : afterE.P iF ≠ 0 := by
  simp [afterE, Measure.jeffrey, Measure.cond, twoItems, iE, iF, ind_true, ind_false]; grind
theorem aE_F1 : afterE.P (fun p => ¬ iF p) ≠ 0 := by
  simp [afterE, Measure.jeffrey, Measure.cond, twoItems, iE, iF, ind_true, ind_false]; grind
theorem aF_E0 : afterF.P iE ≠ 0 := by
  simp [afterF, Measure.jeffrey, Measure.cond, twoItems, iE, iF, ind_true, ind_false]; grind
theorem aF_E1 : afterF.P (fun p => ¬ iE p) ≠ 0 := by
  simp [afterF, Measure.jeffrey, Measure.cond, twoItems, iE, iF, ind_true, ind_false]; grind

/-- **Two items in opposite orders, section 5.3**, source lines 689-691: "Now take two points
    at which you find yourself certain of the same evidence ... with the same two things learned
    at both ... in one order at the one and in the other order at the other. ... (J) can give the
    two points two values."
    Statement: on a prior with two events `E`, `F` that bear on each other (`twoItems`), (J) on
    `E` to 9/10 and then on `F` to 1/5 gives `E` the value `0.2·(72/74) + 0.8·(18/26)`, about
    0.748; (J) on `F` to 1/5 and then on `E` to 9/10 gives `E` the value 9/10; the two differ.
    Choices: each of the two items is a (J) step, a new probability for one event (`E` to 9/10,
    `F` to 1/5); the prior and the two new values are one choice that exhibits the difference;
    the paper gives no numbers here. -/
theorem jeffrey_two_orders :
    (afterE.jeffrey iF trivial aE_F0 aE_F1 (1/5) (by grind) (by grind)).P iE
      = (1/5) * ((72/100) / (74/100)) + (4/5) * ((18/100) / (26/100)) ∧
    (afterF.jeffrey iE trivial aF_E0 aF_E1 (9/10) (by grind) (by grind)).P iE = 9/10 ∧
    (afterE.jeffrey iF trivial aE_F0 aE_F1 (1/5) (by grind) (by grind)).P iE
      ≠ (afterF.jeffrey iE trivial aF_E0 aF_E1 (9/10) (by grind) (by grind)).P iE := by
  have k := afterF.jeffrey_E (E := iE) trivial aF_E0 aF_E1 (9/10) (by grind) (by grind)
  have v : (afterE.jeffrey iF trivial aE_F0 aE_F1 (1/5) (by grind) (by grind)).P iE
      = (1/5) * ((72/100) / (74/100)) + (4/5) * ((18/100) / (26/100)) := by
    simp [afterE, Measure.jeffrey, Measure.cond, twoItems, iE, iF, ind_true, ind_false]; grind
  refine ⟨v, k, ?_⟩
  rw [v, k]; grind

/-- The noisy signal and the device: `E` the event, `D` the device reading (that `E` took
    place with probability 0.9), `Y` another event. Points: `E ∧ D ∧ Y`, `E ∧ ¬D`, `¬E ∧ D`,
    `¬E ∧ ¬D`, at 9/20, 1/20, 1/20, 9/20. -/
inductive NPt | eDY | eN | nD | nN
  deriving DecidableEq

noncomputable def noisy : Measure NPt where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 9/20 * ind (E .eDY) + 1/20 * ind (E .eN) + 1/20 * ind (E .nD) + 9/20 * ind (E .nN)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (9/20) (by grind) (A .eDY); have h2 := wind_nonneg (1/20) (by grind) (A .eN)
    have h3 := wind_nonneg (1/20) (by grind) (A .nD); have h4 := wind_nonneg (9/20) (by grind) (A .nN)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .eDY); have h2 := ind_or (h .eN)
    have h3 := ind_or (h .nD); have h4 := ind_or (h .nN)
    simp only [h1, h2, h3, h4]; grind

def nE : NPt → Prop | .eDY => True | .eN => True | _ => False
def nD : NPt → Prop | .eDY => True | .nD => True | _ => False
def nY : NPt → Prop | .eDY => True | _ => False

theorem noisy_E0 : noisy.P nE ≠ 0 := by simp [noisy, nE, ind_true, ind_false]; grind
theorem noisy_E1 : noisy.P (fun x => ¬ nE x) ≠ 0 := by simp [noisy, nE, ind_true, ind_false]; grind

/-- **The noisy signal and the reliable device, section 5.3**, source line 695: "A noisy signal
    that leaves you with 0.9 for `E` ... and a completely reliable measuring device that says that
    `E` took place with probability 0.9 have the same impact on `E`. In other words, given (B),
    learning either gives `E` the same value. (J) not only has us treat the two differently. It
    can give them different values for other events."
    Statement: (i) in any measure, two events `S` (the signal received) and `D` (the device's
    reading) with `P(E | S) = P(E | D) = 9/10`: any later measure with `S` certain, or with `D`
    certain, and the ratio kept, gives `E` the value 9/10. (ii) On the model `noisy`:
    `P(E | D) = 9/10`; (J) on `E` to 9/10 gives `E` 9/10; but `P(Y | D) = 9/10` while (J) gives
    `Y` the value `81/100`.
    Choices: under (J) the noisy signal is a (J) step on `E` to 0.9 and the device's reading is
    an event learned with certainty; "other events" is one event `Y` that, within `E`, goes with
    the device's reading. The model is one choice; the paper gives no model here. -/
theorem noisy_and_device :
    (∀ {Ω : Type} (m lat : Measure Ω) (E S : Ω → Prop), lat.ev E → lat.ev S →
      m.cond E S = 9/10 → lat.P S = 1 → lat.cond E S = m.cond E S → lat.P E = 9/10) ∧
    noisy.cond nE nD = 9/10 ∧
    (noisy.jeffrey nE trivial noisy_E0 noisy_E1 (9/10) (by grind) (by grind)).P nE = 9/10 ∧
    noisy.cond nY nD = 9/10 ∧
    (noisy.jeffrey nE trivial noisy_E0 noisy_E1 (9/10) (by grind) (by grind)).P nY = 81/100 := by
  refine ⟨fun m lat E S hE hS r cert same => lat.certain_gives_ratio hE hS cert (same.trans r),
    ?_, ?_, ?_, ?_⟩ <;>
  simp [noisy, Measure.jeffrey, Measure.cond, nE, nD, nY, ind_true, ind_false] <;> grind

/-- **Amina's case at `u`, and at `u = 1`, section 5.3**, source line 703: "`π_A(H) = u · 1/3 +
    (1-u) π_A(H | ¬R)` ... When Amin walks in, `u = 1`, the rule is conditioning on `R` from
    Sunday, and they are two values for `H` itself."
    Statement: (i) in any measure with `π_A(R) = u`, `0 < u < 1`, and `π_A(H | R) = 1/3`:
    `π_A(H) = u · 1/3 + (1-u) π_A(H | ¬R)`. (ii) At `u = 1`: a Sunday measure `Pr_A` with
    `Pr_A(H | R) = Pr_A(H | ¬R) = 1/2` and (J) on `R` to 1 gives `Q(H) = 1/2`; a waking measure
    with `R` certain and `π_A(H | R) = 1/3` gives `π_A(H) = 1/3`; the two values differ.
    Existing: `jeffrey_from_sunday` and `not_both` (YourProof.lean) give `Q(H) = 1/2` at every
    `u` and the two values of `H` given `R`. -/
theorem amina_total {Ω : Type} (πA : Measure Ω) (H R : Ω → Prop) (hH : πA.ev H) (hR : πA.ev R)
    (u : Rat) (hu : πA.P R = u) (hu0 : 0 < u) (hu1 : u < 1) (r : πA.cond H R = 1/3) :
    πA.P H = u * (1/3) + (1-u) * πA.cond H (fun ω => ¬ R ω) := by
  have c := πA.compl hR
  have t := πA.total_probability hH hR (by grind) (by grind)
  rw [t, r, hu]
  have e : πA.P (fun ω => ¬ R ω) = 1 - u := by grind
  rw [e]

theorem amina_u_one {Ω Ω' : Type} (PrA : Measure Ω) (H R : Ω → Prop) (hR : PrA.ev R)
    (h0 : PrA.P R ≠ 0) (h1 : PrA.P (fun ω => ¬ R ω) ≠ 0)
    (iR : PrA.cond H R = 1/2) (_inR : PrA.cond H (fun ω => ¬ R ω) = 1/2)
    (πA : Measure Ω') (H' R' : Ω' → Prop) (hH' : πA.ev H') (hR' : πA.ev R')
    (cert : πA.P R' = 1) (r : πA.cond H' R' = 1/3) :
    (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H = 1/2 ∧ πA.P H' = 1/3 ∧
    (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H ≠ πA.P H' := by
  have q : (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H = 1/2 := by
    show (1 : Rat) * PrA.cond H R + (1 - 1) * PrA.cond H (fun ω => ¬ R ω) = 1/2
    rw [iR]; grind
  have p := πA.certain_gives_ratio hH' hR' cert r
  refine ⟨q, p, ?_⟩
  rw [q, p]; grind

end Jeffrey


/-! ## Section 6: the justification of (12), and section 6.1, Schell(ing)'s gas stations -/

section Lemma

/-- **The justification of (12), section 6**, source line 756: "The four cells of (10) sum to 1,
    `(1+c)A + (2-c)B = 1`, so `A = B` is `A = B = 1/3`. At `A = B`, `q = π(a) = (1+c)A =
    (1+c)/3`; at the fair urn, `q = 1/2`."
    Statement: with `A = q/(1+c)`, `B = (1-q)/(2-c)` as in (10), `0 < c < 1`: `A = B` gives
    `A = B = 1/3` and `q = (1+c)/3`; at `c = 1/2`, `(1+c)/3 = 1/2`.
    Existing: `display12` (Displays.lean) has the equivalence of (12); `modelC_cells` has
    `q = (1+c)/3` inside the model. -/
theorem just12 (q c : Rat) (hc0 : 0 < c) (hc1 : c < 1) (hAB : q/(1+c) = (1-q)/(2-c)) :
    q/(1+c) = 1/3 ∧ (1-q)/(2-c) = 1/3 ∧ q = (1+c)/3 ∧ (c = 1/2 → (1+c)/3 = 1/2) := by
  have hA : q = q/(1+c) * (1+c) := by grind
  have hB : 1 - q = (1-q)/(2-c) * (2-c) := by grind
  rw [← hAB] at hB
  have k : q/(1+c) = 1/3 := by grind
  refine ⟨k, by rw [← hAB]; exact k, by grind, fun h => by subst h; grind⟩

end Lemma

section Gas

theorem gas_up (w : Rat) (h : 1/2 < w) : 1/3 < w/(1+w) := by
  have : w/(1+w) = 1/3 + (2*w - 1)/(3*(1+w)) := by grind
  rw [this]
  have : 0 < (2*w - 1)/(3*(1+w)) := pos_div _ _ (by grind) (by grind)
  grind

theorem gas_down (w : Rat) (h : 1/2 < w) (hw : w ≤ 1) : (1-w)/(2-w) < 1/3 := by
  have : (1-w)/(2-w) = 1/3 - (2*w - 1)/(3*(2-w)) := by grind
  rw [this]
  have : 0 < (2*w - 1)/(3*(2-w)) := pos_div _ _ (by grind) (by grind)
  grind

/-- A point of the gas stations: (heads, the where urn names the `Monday` station, the whether
    urn gives `meet`, the tails urn names the `Monday` station). `Monday` is the station that keeps
    the where urn (source line 784). -/
abbrev GasPt := Bool × Bool × Bool × Bool

/-- The manifesto's measure with the where urn at `w`, the whether urn at `s`, the tails urn at
    `t` (probabilities of a `Monday` ball, a `meet` ball, a `Monday` ball), the coin fair; the
    coin and the three draws independent ("do not affect one another"). The manifesto has
    `w = s = t = 1/2`. -/
noncomputable def gas (w s t : Rat) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Measure GasPt :=
  prod4 (1/2) w s t (by grind) (by grind) hw0 hw1 hs0 hs1 ht0 ht1

def sH : GasPt → Prop := fun p => p.1 = true
/-- You meet at the `Monday` station: tails with the tails urn naming it, or heads with `meet`
    and the where urn naming it. -/
def sMon : GasPt → Prop := fun p =>
  (p.1 = false ∧ p.2.2.2 = true) ∨ (p.1 = true ∧ p.2.2.1 = true ∧ p.2.1 = true)
def sTue : GasPt → Prop := fun p =>
  (p.1 = false ∧ p.2.2.2 = false) ∨ (p.1 = true ∧ p.2.2.1 = true ∧ p.2.1 = false)
def sMeet : GasPt → Prop := fun p => sMon p ∨ sTue p

/-- How many of the two drivers pull in at the `Tuesday` station: both, when the signs send
    both there (tails with the tails urn naming `Tuesday`; heads with `meet` and the where urn
    naming `Tuesday`); one, on heads with `not` (the signs send drivers to different stations);
    none otherwise. -/
def tueCustomers (p : GasPt) : Rat :=
  match p with
  | (false, _, _, false) => 2
  | (false, _, _, true) => 0
  | (true, false, true, _) => 2
  | (true, true, true, _) => 0
  | (true, _, false, _) => 1

/-- The weight of a point (the product of the four draws' probabilities). -/
def gasW (w s t : Rat) (p : GasPt) : Rat := wt (1/2) p.1 * wt w p.2.1 * wt s p.2.2.1 * wt t p.2.2.2

/-- An expectation over the sixteen points. -/
def gasExp (w s t : Rat) (f : GasPt → Rat) : Rat :=
    gasW w s t (true, true, true, true) * f (true, true, true, true)
  + gasW w s t (true, true, true, false) * f (true, true, true, false)
  + gasW w s t (true, true, false, true) * f (true, true, false, true)
  + gasW w s t (true, true, false, false) * f (true, true, false, false)
  + gasW w s t (true, false, true, true) * f (true, false, true, true)
  + gasW w s t (true, false, true, false) * f (true, false, true, false)
  + gasW w s t (true, false, false, true) * f (true, false, false, true)
  + gasW w s t (true, false, false, false) * f (true, false, false, false)
  + gasW w s t (false, true, true, true) * f (false, true, true, true)
  + gasW w s t (false, true, true, false) * f (false, true, true, false)
  + gasW w s t (false, true, false, true) * f (false, true, false, true)
  + gasW w s t (false, true, false, false) * f (false, true, false, false)
  + gasW w s t (false, false, true, true) * f (false, false, true, true)
  + gasW w s t (false, false, true, false) * f (false, false, true, false)
  + gasW w s t (false, false, false, true) * f (false, false, false, true)
  + gasW w s t (false, false, false, false) * f (false, false, false, false)

theorem hb0 : (0:Rat) ≤ 1/2 := by grind
theorem hb1 : (1/2:Rat) ≤ 1 := by grind
theorem one0 : (0:Rat) ≤ 1 := by grind
theorem one1 : (1:Rat) ≤ 1 := by grind
theorem zero0 : (0:Rat) ≤ 0 := by grind
theorem zero1 : (0:Rat) ≤ 1 := by grind

/-- **The where urn moved, section 6.1**, source line 790: "One of the gas station owners ... keeps
    adding Monday balls to his urn and taking out Tuesday balls. More of the heads meetings are
    then at his station, and the tails meetings are divided between the stations as before. So
    at his station heads now has more than a third, and at the other station less. ... This owner
    controls the share of the meetings that are at his station."
    Statement, with the where urn at `w` (whether and tails urns even): heads has `w/(1+w)` at a
    meeting at the `Monday` station and `(1-w)/(2-w)` at the `Tuesday` station; for `w > 1/2`
    the first is above 1/3 and the second below; the tails meetings at the `Monday` station are
    `1/4` of the runs at every `w`; the share of the meetings at the `Monday` station is
    `(1+w)/3`.
    Existing: `gas_where_urn` (Displays.lean): heads 1/3 at a meeting at every `w`. -/
theorem gas_owner (w : Rat) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (gas w (1/2) (1/2) hw0 hw1 hb0 hb1 hb0 hb1).cond sH sMon = w/(1+w) ∧
    (gas w (1/2) (1/2) hw0 hw1 hb0 hb1 hb0 hb1).cond sH sTue = (1-w)/(2-w) ∧
    (1/2 < w → 1/3 < w/(1+w) ∧ (1-w)/(2-w) < 1/3) ∧
    (gas w (1/2) (1/2) hw0 hw1 hb0 hb1 hb0 hb1).P (fun p => ¬ sH p ∧ sMon p) = 1/4 ∧
    (gas w (1/2) (1/2) hw0 hw1 hb0 hb1 hb0 hb1).cond sMon sMeet = (1+w)/3 := by
  refine ⟨?_, ?_, fun h => ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [gas, prod4, Measure.cond, sH, sMon, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, Measure.cond, sH, sTue, wt, ind_true, ind_false]; grind
  · exact gas_up w h
  · exact gas_down w h hw1
  · simp [gas, prod4, sH, sMon, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, Measure.cond, sMon, sTue, sMeet, wt, ind_true, ind_false]; grind

/-- **The complete altruist, section 6.1**, source line 790: "A complete altruist puts in
    Tuesday balls only, and it is the Tuesday case every time."
    Statement, the where urn at `w = 0`: heads has 1/2 at a meeting at the `Tuesday` station
    and 0 at the `Monday` station; two thirds of the meetings are at the `Tuesday` station.
    Choice: "the Tuesday case" is the egoist's case (`gas_egoist`, Displays.lean) with the
    stations exchanged. -/
theorem gas_altruist :
    (gas 0 (1/2) (1/2) zero0 zero1 hb0 hb1 hb0 hb1).cond sH sTue = 1/2 ∧
    (gas 0 (1/2) (1/2) zero0 zero1 hb0 hb1 hb0 hb1).cond sH sMon = 0 ∧
    (gas 0 (1/2) (1/2) zero0 zero1 hb0 hb1 hb0 hb1).cond sTue sMeet = 2/3 := by
  simp [gas, prod4, Measure.cond, sH, sMon, sTue, sMeet, wt, ind_true, ind_false]; grind

/-- **Both urns his, section 6.1**, source line 790: "Were the tails urn his as well, with Monday
    balls only in both, every meeting would be at his station, and heads would still have a
    third there. The only thing the Tuesday station would then get is the one customer who
    arrives on heads with no meeting: an eighth of all the customers. You can be certain that it
    is Monday, and heads still has 1/3."
    Statement, the where urn and the tails urn at 1 (whether urn even): no meeting is at the
    `Tuesday` station, `π(Monday | meeting) = 1`; heads has 1/3 at a meeting at the `Monday`
    station; at every point of positive weight, the `Tuesday` station has a customer only on
    heads with `not`, and then one; the expected number of customers at the `Tuesday` station is
    1/4 of a customer per run, of 2 per run in all, an eighth.
    Choices: the customers are the two drivers of a run, each pulling in where the sign on his
    side sends him; "all the customers" is the expected number of drivers at both stations per
    run (2); "an eighth of all the customers" is the ratio of the two expectations. -/
theorem gas_both_urns :
    (gas 1 (1/2) 1 one0 one1 hb0 hb1 one0 one1).P sTue = 0 ∧
    (gas 1 (1/2) 1 one0 one1 hb0 hb1 one0 one1).cond sMon sMeet = 1 ∧
    (gas 1 (1/2) 1 one0 one1 hb0 hb1 one0 one1).cond sH sMon = 1/3 ∧
    (∀ p : GasPt, gasW 1 (1/2) 1 p ≠ 0 → tueCustomers p ≠ 0 →
      p.1 = true ∧ p.2.2.1 = false ∧ tueCustomers p = 1) ∧
    gasExp 1 (1/2) 1 tueCustomers = 1/4 ∧
    gasExp 1 (1/2) 1 (fun _ => 2) = 2 ∧
    gasExp 1 (1/2) 1 tueCustomers / gasExp 1 (1/2) 1 (fun _ => 2) = 1/8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gas, prod4, sTue, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, Measure.cond, sMon, sTue, sMeet, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, Measure.cond, sH, sMon, wt, ind_true, ind_false]; grind
  · intro p; obtain ⟨a, b, c, d⟩ := p
    cases a <;> cases b <;> cases c <;> cases d <;> simp [gasW, wt, tueCustomers] <;> grind
  · simp [gasExp, gasW, wt, tueCustomers]; grind
  · simp [gasExp, gasW, wt]; grind
  · simp [gasExp, gasW, wt, tueCustomers]; grind

/-- **The whether urn moved, section 6.1**, source line 792: "Say such a ball is drawn with chance
    `s` on heads. On heads you then meet at a station half as often as such a ball is drawn. On
    tails you still meet there half the time. ... In the limit, you always meet. The meeting then
    tells you nothing, and heads has the coin's 1/2. ... With those two urns even, the station has
    no influence on the coin, and the coin has none on the station."
    Statement, with the whether urn at `s` (where and tails urns even): `π(Monday | H) = s/2`,
    `π(Monday | ¬H) = 1/2`; at `s = 1` a meeting is certain and `π(H | meeting) = π(H) = 1/2`;
    at every `0 < s ≤ 1`, given a meeting, the station and the coin are independent:
    `π(H | Monday) = π(H | Tuesday) = π(H | meeting)` and
    `π(Monday | meeting ∧ H) = π(Monday | meeting ∧ ¬H) = 1/2`.
    Existing: `gas_whether_urn` (Displays.lean): heads `s/(1+s)` at either station, 1/2 at
    `s = 1`. -/
theorem gas_whether (s : Rat) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sMon sH = s/2 ∧
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sMon (fun p => ¬ sH p) = 1/2 ∧
    (gas (1/2) 1 (1/2) hb0 hb1 one0 one1 hb0 hb1).P sMeet = 1 ∧
    (gas (1/2) 1 (1/2) hb0 hb1 one0 one1 hb0 hb1).cond sH sMeet = 1/2 ∧
    (gas (1/2) 1 (1/2) hb0 hb1 one0 one1 hb0 hb1).P sH = 1/2 ∧
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sH sMon
      = (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sH sMeet ∧
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sH sTue
      = (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sH sMeet ∧
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sMon (fun p => sMeet p ∧ sH p) = 1/2 ∧
    (gas (1/2) s (1/2) hb0 hb1 (by grind) hs1 hb0 hb1).cond sMon
      (fun p => sMeet p ∧ ¬ sH p) = 1/2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [gas, prod4, Measure.cond, sH, sMon, sTue, sMeet, wt, ind_true, ind_false] <;> grind

/-- **The gas station on Sunday, section 7.1**, source line 833: "A second before you pull in is
    like Sunday: heads has 1/2, and a meeting has 3/4, as `[M]` and `[T]` each have on Amin's
    Sunday. As soon as you pull in and see Boltzmann ... your probability for heads is now 1/3."
    Statement, at the manifesto's urns: `π(H) = 1/2`, `π(meeting) = 3/4`, `π(H | meeting) = 1/3`;
    and on the recording's model `Pr([M]) = Pr([T]) = 3/4` (`two_guesses`).
    Choice: "a meeting has 3/4" is the probability of a meeting at either station. -/
theorem gas_sunday :
    (gas (1/2) (1/2) (1/2) hb0 hb1 hb0 hb1 hb0 hb1).P sH = 1/2 ∧
    (gas (1/2) (1/2) (1/2) hb0 hb1 hb0 hb1 hb0 hb1).P sMeet = 3/4 ∧
    (gas (1/2) (1/2) (1/2) hb0 hb1 hb0 hb1 hb0 hb1).cond sH sMeet = 1/3 ∧
    PrModel.P Mout = 3/4 ∧ PrModel.P Tout = 3/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [gas, prod4, sH, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, sMeet, sMon, sTue, wt, ind_true, ind_false]; grind
  · simp [gas, prod4, Measure.cond, sH, sMeet, sMon, sTue, wt, ind_true, ind_false]; grind
  · simp [PrModel, Mout, Hout, Cout, ind_true, ind_false]; grind
  · simp [PrModel, Tout, Hout, Cout, ind_true, ind_false]; grind

end Gas

/-! ## Section 7: Sleeping Beauty, the halfers, the outsiders, the bets, the thirders -/

section SB

/-- The recording's measure at urn `c` (`0 ≤ c ≤ 1`, the probability of a `Monday` ball): a fair
    coin (first coordinate, heads) and the ball (second coordinate, `Monday`), independent. -/
noncomputable def recUrn (c : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : Measure (Bool × Bool) :=
  prod2 (1/2) c (by grind) (by grind) hc0 hc1

def rH : Bool × Bool → Prop := fun p => p.1 = true
/-- `[M]`: a waking on Monday, heads with a `Monday` ball or tails. -/
def rM : Bool × Bool → Prop := fun p => (p.1 = true ∧ p.2 = true) ∨ p.1 = false
/-- `[T]`: a waking on Tuesday, heads with a `Tuesday` ball or tails. -/
def rT : Bool × Bool → Prop := fun p => (p.1 = true ∧ p.2 = false) ∨ p.1 = false

/-- **Sleeping Beauty on Sunday, section 7.1**, source line 820: "So `Pr([M]) = 1` and
    `Pr([T]) = 1/2` in Sleeping Beauty on Sunday. In AMIN'S RECORDING, `Pr([M]) = Pr([T]) = 3/4`.
    Sure Thing, then, has nothing to apply to, and your measure, `Pr`, has heads at 1/2."
    Statement, on the recording's measure at urn `c`: `Pr([M]) = (1+c)/2`, `Pr([T]) = (2-c)/2`,
    `Pr(H) = 1/2`; at `c = 1` (Monday balls only, Sleeping Beauty) `Pr([M]) = 1` and
    `Pr([T]) = 1/2`; at `c = 1/2`, both 3/4; `Pr([M] ∧ [T]) = 1/2` (the two overlap on tails). -/
theorem sb_sunday (c : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (recUrn c hc0 hc1).P rM = (1+c)/2 ∧ (recUrn c hc0 hc1).P rT = (2-c)/2 ∧
    (recUrn c hc0 hc1).P rH = 1/2 ∧
    (recUrn c hc0 hc1).P (fun p => rM p ∧ rT p) = 1/2 ∧
    (c = 1 → (1+c)/2 = 1 ∧ (2-c)/2 = 1/2) ∧ (c = 1/2 → (1+c)/2 = 3/4 ∧ (2-c)/2 = 3/4) := by
  refine ⟨?_, ?_, ?_, ?_, fun h => by subst h; grind, fun h => by subst h; grind⟩ <;>
  simp [recUrn, prod2, rM, rT, rH, wt, ind_true, ind_false] <;> grind

/-- `λ` of (15) on the six points of Appendix B: a quarter at each heads waking, an eighth at each
    tails waking. -/
noncomputable def lamPt : Measure Point where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 1/4 * ind (E .R1M) + 1/4 * ind (E .R2T) + 1/8 * ind (E .R3M)
        + 1/8 * ind (E .R3T) + 1/8 * ind (E .R4M) + 1/8 * ind (E .R4T)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (1/4) (by grind) (A .R1M); have h2 := wind_nonneg (1/4) (by grind) (A .R2T)
    have h3 := wind_nonneg (1/8) (by grind) (A .R3M); have h4 := wind_nonneg (1/8) (by grind) (A .R3T)
    have h5 := wind_nonneg (1/8) (by grind) (A .R4M); have h6 := wind_nonneg (1/8) (by grind) (A .R4T)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .R1M); have h2 := ind_or (h .R2T); have h3 := ind_or (h .R3M)
    have h4 := ind_or (h .R3T); have h5 := ind_or (h .R4M); have h6 := ind_or (h .R4T)
    simp only [h1, h2, h3, h4, h5, h6]; grind

/-- **Where `λ` fails, section 7.2**, source line 859: "For `a`, the construction requires you to
    take `Pr` ... and rule out `¬[M]` by removing the one combination with no Monday waking. The
    remaining combinations have equal shares, a third each. In `λ`, the heads combination has a
    half and the two tails combinations have a quarter each."
    Statement: on the recording's model, `Pr(H∧C | [M]) = Pr(¬H∧C | [M]) = Pr(¬H∧¬C | [M]) = 1/3`
    and `Pr(H∧¬C | [M]) = 0`; on `λ` (15) on the six points, `λ(H∧C | a) = 1/2`,
    `λ(¬H∧C | a) = λ(¬H∧¬C | a) = 1/4`. -/
theorem lambda_cells :
    PrModel.cond (fun n => Hout n ∧ Cout n) Mout = 1/3 ∧
    PrModel.cond (fun n => ¬ Hout n ∧ Cout n) Mout = 1/3 ∧
    PrModel.cond (fun n => ¬ Hout n ∧ ¬ Cout n) Mout = 1/3 ∧
    PrModel.cond (fun n => Hout n ∧ ¬ Cout n) Mout = 0 ∧
    lamPt.cond (fun x => Hpt x ∧ Cpt x) apt = 1/2 ∧
    lamPt.cond (fun x => ¬ Hpt x ∧ Cpt x) apt = 1/4 ∧
    lamPt.cond (fun x => ¬ Hpt x ∧ ¬ Cpt x) apt = 1/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [PrModel, lamPt, Measure.cond, Mout, Hout, Cout, Hpt, Cpt, apt, ind_true, ind_false] <;>
  grind

theorem arith_kappa (x y : Rat) (hx : 1/4 / x = 1/3) (hy : 1/4 / y = 1/3) :
    x = 3/4 ∧ y = 3/4 ∧ x + y = 3/2 := by
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; grind
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; grind
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- **The measure `κ`, section 7.2**, source line 867: "If `κ` also gave heads 1/3 in each cell,
    then `κ(a)` and `κ(b)` would both have to equal 3/4. ... Two probabilities of 3/4 instead sum
    to 3/2, which is not a value of a measure."
    Statement: in any measure with `κ(H ∧ a) = κ(H ∧ b) = 1/4` (17) and `κ(H | a) = κ(H | b) = 1/3`:
    `κ(a) = κ(b) = 3/4` and `κ(a) + κ(b) = 3/2`.
    Existing: `display17_no_third` (Displays.lean) derives `False` from the same hypotheses with
    `a`, `b` a partition. -/
theorem kappa_three_quarters {Ω : Type} (κ : Measure Ω) (H a b : Ω → Prop)
    (k1 : κ.P (fun ω => H ω ∧ a ω) = 1/4) (k2 : κ.P (fun ω => H ω ∧ b ω) = 1/4)
    (t1 : κ.cond H a = 1/3) (t2 : κ.cond H b = 1/3) :
    κ.P a = 3/4 ∧ κ.P b = 3/4 ∧ κ.P a + κ.P b = 3/2 := by
  unfold Measure.cond at t1 t2
  rw [k1] at t1; rw [k2] at t2
  exact arith_kappa _ _ t1 t2

theorem arith_dh (pH x y pa : Rat) (s : pH = x + y) (hx : x / pa = 1/2) (hpa : pa ≠ 0)
    (hy : y = 0) : pH = pa / 2 ∧ (pH = 1/2 ↔ pa = 1) := by
  have : x = pa / 2 := by grind
  constructor <;> grind

/-- **Double halfing, section 7.2**, source line 875: "By the tag-swapping lemma, the probability
    of heads in AMIN'S MONDAY given Monday's announcement is 1/2. Given Tuesday's announcement,
    heads is excluded. The waking probability of heads is therefore half the probability that the
    announcement is Monday's. For the double-halfer account to give 1/2 at the waking, Monday's
    announcement must have probability 1."
    Statement: in any measure with `π(a) ≠ 0`, `π(H | a) = 1/2` and `π(H ∧ ¬a) = 0`:
    `π(H) = π(a)/2`, and `π(H) = 1/2` iff `π(a) = 1`.
    Choice: Tuesday's announcement is the cell `¬a` (the two cells exclusive and exhaustive), and
    "heads is excluded" given it is `π(H ∧ ¬a) = 0`. -/
theorem double_halfer {Ω : Type} (π : Measure Ω) (H a : Ω → Prop) (hH : π.ev H) (ha : π.ev a)
    (pa : π.P a ≠ 0) (h1 : π.cond H a = 1/2) (h0 : π.P (fun ω => H ω ∧ ¬ a ω) = 0) :
    π.P H = π.P a / 2 ∧ (π.P H = 1/2 ↔ π.P a = 1) := by
  have s := π.split hH ha
  unfold Measure.cond at h1
  exact arith_dh _ _ _ _ s h1 pa h0

/-- The three wakings of Sleeping Beauty (AMIN'S MONDAY): heads-Monday, tails-Monday,
    tails-Tuesday, at a third each, the values of the lemma's cells (13) at `c = 1`
    (`a ∧ C` at 2/3, half of it heads; `b ∧ C` at 1/3). -/
inductive SBPt | HM | TM | TT
  deriving DecidableEq

noncomputable def sb3 : Measure SBPt where
  ev := fun _ => True
  ev_true := trivial
  ev_not := fun _ => trivial
  ev_and := fun _ _ => trivial
  P := fun E => 1/3 * ind (E .HM) + 1/3 * ind (E .TM) + 1/3 * ind (E .TT)
  nonneg := by
    intro A _
    have h1 := wind_nonneg (1/3) (by grind) (A .HM); have h2 := wind_nonneg (1/3) (by grind) (A .TM)
    have h3 := wind_nonneg (1/3) (by grind) (A .TT)
    grind
  total := by simp only [ind_true]; grind
  add := by
    intro A B _ _ h
    have h1 := ind_or (h .HM); have h2 := ind_or (h .TM); have h3 := ind_or (h .TT)
    simp only [h1, h2, h3]; grind

def sbH : SBPt → Prop | .HM => True | _ => False
def sbA : SBPt → Prop | .TT => False | _ => True

/-- The double halfer's numbers on the three wakings (source line 875): `π(a) = 2/3`,
    `π(H | a) = 1/2`, `π(H ∧ ¬a) = 0`, `π(H) = 1/3 = π(a)/2`.
    Note (added after the audit of 22 Nov): the 2/3 is an input of this model (a third on each
    waking); it is derived in Displays.lean (`display13`, `π(a | C) = 2/3`), not here. -/
theorem double_halfer_model :
    sb3.P sbA = 2/3 ∧ sb3.cond sbH sbA = 1/2 ∧ sb3.P (fun x => sbH x ∧ ¬ sbA x) = 0 ∧
    sb3.P sbH = 1/3 ∧ sb3.P sbH = sb3.P sbA / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [sb3, Measure.cond, sbH, sbA, ind_true, ind_false] <;> grind

/-- **Outsiders, one on heads, none on tails, section 7.3**, source line 894: "With one added
    member in each heads outcome and none in the tails outcomes, each outcome has two members,
    and the rule gives 1/3."
    Statement: each outcome's quarter divided equally among its two members gives each heads
    waking and each tails waking `(1/4)/2`; dropping the added members and renormalizing over
    the six wakings (two heads, four tails), heads has `2·(1/8)/(2·(1/8) + 4·(1/8)) = 1/3`. -/
theorem outsiders_heads_only :
    (2 * ((1:Rat)/4/2)) / (2 * ((1:Rat)/4/2) + 4 * ((1:Rat)/4/2)) = 1/3 := by grind

/-- **A Sunday waking in the class, section 7.3**, source line 900: "With a Sunday waking added to
    the class in every outcome, it gives heads 3/5 at the Sunday waking".
    Statement: each heads outcome has two members (Sunday and one waking), each tails outcome
    three (Sunday and two wakings); each outcome's quarter divided equally; given the Sunday
    waking, heads has `2·(1/4)/2 / (2·(1/4)/2 + 2·(1/4)/3) = 3/5`. -/
theorem sunday_in_class :
    (2 * ((1:Rat)/4/2)) / (2 * ((1:Rat)/4/2) + 2 * ((1:Rat)/4/3)) = 3/5 := by grind

/-- Every rational is below some natural number (copied from Displays.lean). -/
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

theorem natcast_le (a b : Nat) (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by exact_mod_cast h
theorem natcast_nonneg (N : Nat) : (0:Rat) ≤ (N:Rat) := by exact_mod_cast Nat.zero_le N

theorem div_lt_of_lt_mul (x y e : Rat) (hy : 0 < y) (h : x < e * y) : x / y < e := by
  have hi : 0 < y⁻¹ := Rat.inv_pos.mpr hy
  have k := Rat.mul_lt_mul_of_pos_right h hi
  rw [Rat.div_def]
  have e1 : e * y * y⁻¹ = e := by grind
  rw [e1] at k; exact k

theorem eps_mul (eps k n : Rat) (he : 0 < eps) (h : k / eps ≤ n) : k ≤ eps * n := by
  have k1 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt he)
  have e1 : eps * (k / eps) = k := by grind
  rw [e1] at k1; exact k1

/-- **The Doomsday factor with outsiders, section 7.3**, source line 911: "With `N` members added
    under both hypotheses, the factor in (20) is `(N_L+N)/(N_S+N)`, and its limit is 1."
    Statement: for populations `0 < N_S < N_L`, the factor is above 1 at every `N`, and for every
    positive rational `ε` it is within `ε` of 1 from some `N₀` on.
    Choice: "its limit is 1" is stated in the `ε`-`N₀` form, with `ε` rational. -/
theorem doomsday_factor_limit (NS NL : Rat) (hS : 0 < NS) (hSL : NS < NL) :
    (∀ N : Nat, 1 < (NL + N)/(NS + N)) ∧
    ∀ eps : Rat, 0 < eps → ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → (NL + N)/(NS + N) - 1 < eps := by
  refine ⟨fun N => ?_, fun eps he => ?_⟩
  · have hn := natcast_nonneg N
    have e : (NL + N)/(NS + N) = 1 + (NL - NS)/(NS + N) := by grind
    have := pos_div (NL - NS) (NS + N) (by grind) (by grind)
    grind
  · obtain ⟨N0, hN0⟩ := rat_arch ((NL - NS)/eps)
    refine ⟨N0, fun N hN => ?_⟩
    have hn := natcast_nonneg N
    have k : (NL - NS)/eps ≤ (N:Rat) := Rat.le_trans hN0 (natcast_le _ _ hN)
    have t := eps_mul eps (NL - NS) _ he k
    have e : (NL + N)/(NS + N) - 1 = (NL - NS)/(NS + N) := by grind
    rw [e]
    have m : eps * (N:Rat) < eps * (NS + N) := Rat.mul_lt_mul_of_pos_left (by grind) he
    exact div_lt_of_lt_mul _ _ _ (by grind) (by grind)

/-- **The book of Schwarz's paper, section 7.4**, source line 919: "On Sunday you take a first
    bet, `+8` on heads and `-7` on tails, worth `+1/2` at Sunday's 1/2. ... On heads it costs you
    9. On tails it pays 6, but only if you say `deal' at both wakings ... the paper gives `deal' at
    a waking the value `1/3(-9) + 2/3(6) = +1`. The two bets together lose 1 on heads and 1 on
    tails. Suppose instead that you receive 3 at each tails waking at which you say `deal' ...
    You then get 6 if you say `deal' at each tails waking ... `1/3(-9) + 1/3(3) + 1/3(3) = -1`."
    Statement: with the recording's `Pr(H) = 1/2` (Appendix B model), the Sunday bet is worth
    `Pr(H)·8 + Pr(¬H)·(-7) = 1/2`; on the three wakings at a third each (`sb3`), `deal' taken at
    both tails wakings is worth `π(H)(-9) + π(¬H)(6) = 1`; the two bets together give `8 - 9 = -1`
    on heads and `-7 + 6 = -1` on tails; the improved bet pays `3 + 3 = 6` on tails with `deal' at
    both tails wakings and is worth `π(HM)(-9) + π(TM)(3) + π(TT)(3) = -1` at a waking.
    Choice: "every waking its own probability" is `sb3`, a third at each of the three wakings. -/
theorem schwarz_book :
    PrModel.P Hout * 8 + PrModel.P (fun n => ¬ Hout n) * (-7) = 1/2 ∧
    sb3.P sbH * (-9) + sb3.P (fun x => ¬ sbH x) * 6 = 1 ∧
    (8:Rat) + (-9) = -1 ∧ (-7:Rat) + 6 = -1 ∧ (3:Rat) + 3 = 6 ∧
    sb3.P (fun x => x = .HM) * (-9) + sb3.P (fun x => x = .TM) * 3
      + sb3.P (fun x => x = .TT) * 3 = -1 := by
  refine ⟨?_, ?_, by grind, by grind, by grind, ?_⟩
  · simp [PrModel, Hout, ind_true, ind_false]; grind
  · simp [sb3, sbH, ind_true, ind_false]; grind
  · simp [sb3, ind_true, ind_false]; grind

/-- The temporal-prior rule of section 7.5 as a model: (the clock-time is Monday's, heads, a
    `Monday` ball), the prior `ρ` for Monday, the fair coin and the ball at `c`, independent
    ("the coin, the ball and the prior are independent of one another", source line 939). -/
noncomputable def temporal (ρ c : Rat) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Measure (Bool × Bool × Bool) :=
  prod3 ρ (1/2) c hρ0 hρ1 (by grind) (by grind) hc0 hc1

def tD : Bool × Bool × Bool → Prop := fun p => p.1 = true
def tH : Bool × Bool × Bool → Prop := fun p => p.2.1 = true
/-- `W`, the clock-time is a waking time: tails, or heads with the clock-time the day on the
    ball. -/
def tW : Bool × Bool × Bool → Prop := fun p =>
  p.2.1 = false ∨ (p.2.1 = true ∧ ((p.1 = true ∧ p.2.2 = true) ∨ (p.1 = false ∧ p.2.2 = false)))

/-- **`μ_1(H | W)`, section 7.5**, source line 925: "The value `ρ = 1` gives `μ_1(H | W) = 1/2`,
    which is not your proved waking value of 1/3 in the Monday-only case." With (21), source
    lines 929-935: "In AMIN'S MONDAY ... `W` is certain on Monday and is `¬H` on Tuesday".
    Statement, on the model with Monday balls only (`c = 1`): `W` is "Monday or tails";
    `μ_ρ(H | W) = ρ/(1+ρ)`; at `ρ = 1` this is 1/2, which is not 1/3. -/
theorem mu_one (ρ : Rat) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ p : Bool × Bool × Bool, p.2.2 = true → (tW p ↔ (tD p ∨ ¬ tH p))) ∧
    (temporal ρ 1 hρ0 hρ1 one0 one1).cond tH tW = ρ/(1+ρ) ∧
    (temporal 1 1 one0 one1 one0 one1).cond tH tW = 1/2 ∧ (1:Rat)/2 ≠ 1/3 := by
  refine ⟨fun p hp => ?_, ?_, ?_, by grind⟩
  · obtain ⟨a, b, c⟩ := p; simp only at hp; subst hp
    cases a <;> cases b <;> simp [tW, tD, tH]
  · simp [temporal, prod3, Measure.cond, tH, tW, wt, ind_true, ind_false]; grind
  · simp [temporal, prod3, Measure.cond, tH, tW, wt, ind_true, ind_false]; grind

/-- **The Monday clock-time given `W`, section 7.5**, source line 941: "At the fair urn the prior
    does not affect `H`, since every `ρ` gives 1/3. But the rule gives the Monday clock-time
    `q = ρ` given being awake ... At `ρ = 1/2` ... The rule then gives the Monday clock-time
    `(1+c)/3` given `W`, the `q` of (12)."
    Statement, on the model: at `c = 1/2`, `μ(H | W) = 1/3` and `μ(D | W) = ρ` at every `ρ`;
    at `ρ = 1/2`, `μ(D | W) = (1+c)/3` and `μ(H | W) = 1/3` at every urn `c`.
    Existing: `display21_uneven_measure` (Displays.lean): `μ(H | W) = s/(1+s)` at every `ρ`, `c`. -/
theorem temporal_monday (ρ c : Rat) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (temporal ρ (1/2) hρ0 hρ1 hb0 hb1).cond tH tW = 1/3 ∧
    (temporal ρ (1/2) hρ0 hρ1 hb0 hb1).cond tD tW = ρ ∧
    (temporal (1/2) c hb0 hb1 hc0 hc1).cond tD tW = (1+c)/3 ∧
    (temporal (1/2) c hb0 hb1 hc0 hc1).cond tH tW = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [temporal, prod3, Measure.cond, tD, tH, tW, wt, ind_true, ind_false] <;> grind

end SB

/-! ## Section 8: ignorance is ignorance -/

section UrPrior

/-- Two separate runs of one mechanism with bias `b` toward one face (first coordinate: the first
    run shows that face; second: the second run does). -/
noncomputable def twoRuns (b : Rat) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Measure (Bool × Bool) :=
  prod2 b b hb0 hb1 hb0 hb1

/-- **Step 1, section 8.1**, source line 971: "The two orders in which the runs can differ have
    probabilities `b(1-b)` and `(1-b)b`. The runs are separate and of one mechanism, so these
    probabilities are equal. ... One such pair is the coin, with one order as heads and the other
    as tails, so `h = 1/2`."
    Statement, at every bias `0 < b < 1`: the two orders have `b(1-b)` and `(1-b)b`, equal; given
    that the runs differ, each order has 1/2.
    Choice: a pair that "came out with its runs differing" is the pair conditioned on the runs
    differing. -/
theorem von_neumann (b : Rat) (hb0 : 0 < b) (hb1 : b < 1) :
    (twoRuns b (by grind) (by grind)).P (fun p => p.1 = true ∧ p.2 = false) = b * (1-b) ∧
    (twoRuns b (by grind) (by grind)).P (fun p => p.1 = false ∧ p.2 = true) = (1-b) * b ∧
    b * (1-b) = (1-b) * b ∧
    (twoRuns b (by grind) (by grind)).cond (fun p => p.1 = true ∧ p.2 = false)
      (fun p => p.1 ≠ p.2) = 1/2 := by
  have k : 0 < b * (1-b) := Rat.mul_pos hb0 (by grind)
  refine ⟨?_, ?_, by grind, ?_⟩ <;> simp [twoRuns, prod2, Measure.cond, wt, ind_true, ind_false]
    <;> grind

/-- Which pair is the coin: (the first pair's order is heads-like, the second pair's order is
    heads-like, the first pair is the coin), each order at 1/2 (step 1), the pairs independent
    (step 2), the assignment at `α`. -/
noncomputable def assignment (α : Rat) (h0 : 0 ≤ α) (h1 : α ≤ 1) : Measure (Bool × Bool × Bool) :=
  prod3 (1/2) (1/2) α hb0 hb1 hb0 hb1 h0 h1

def asA : Bool × Bool × Bool → Prop := fun p => p.2.2 = true
/-- Heads: the coin pair's order, whichever pair is the coin. -/
def asH : Bool × Bool × Bool → Prop := fun p => if p.2.2 = true then p.1 = true else p.2.1 = true
/-- A `Monday` ball: the urn pair's order. -/
def asC : Bool × Bool × Bool → Prop := fun p => if p.2.2 = true then p.2.1 = true else p.1 = true
def asM : Bool × Bool × Bool → Prop := fun p => (asH p ∧ asC p) ∨ ¬ asH p

/-- **Which pair is the coin, section 8.1**, source line 979: "That you are awakened on Monday has
    probability 3/4 under either assignment, since it takes place on three of the four outcomes,
    a quarter each. ... So your waking says nothing about which pair is the coin".
    Statement, at every `0 < α < 1` for the first pair's being the coin: `Pr([M] | first is
    coin) = Pr([M] | second is coin) = 3/4`, and `Pr(first is coin | [M]) = α`. -/
theorem which_pair (α : Rat) (h0 : 0 < α) (h1 : α < 1) :
    (assignment α (by grind) (by grind)).cond asM asA = 3/4 ∧
    (assignment α (by grind) (by grind)).cond asM (fun p => ¬ asA p) = 3/4 ∧
    (assignment α (by grind) (by grind)).cond asA asM = α := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [assignment, prod3, Measure.cond, asA, asM, asH, asC, wt, ind_true, ind_false] <;> grind

/-- **A rule's cell probabilities at an uneven urn, section 8.1**, source line 997: "If the rule
    gives your two cells other probabilities than the tag-swapping lemma's, its probability for a
    Monday ball is `(1+q)/3`. ... The lemma has 1/2. With an uneven urn the rule gives heads a
    value different from the lemma's: the lemma's weighted sum of the two cell values, with the
    rule's cell probabilities as weights."
    Statement: `(1+q)/3 = 1/2` iff `q = 1/2`; for `0 < c < 1`, `c ≠ 1/2`, the weighted sum
    `q·c/(1+c) + (1-q)(1-c)/(2-c)` (display (9)) is 1/3 iff `q = (1+c)/3`, the lemma's weight.
    Choices: "the lemma's" cell probability at urn `c` is `q = (1+c)/3` (`just12`); "the value
    different from the lemma's" is read as different from 1/3. -/
theorem rule_weights (q c : Rat) (hc0 : 0 < c) (hc1 : c < 1) (hc : c ≠ 1/2) :
    ((1+q)/3 = 1/2 ↔ q = 1/2) ∧
    (q * (c/(1+c)) + (1-q) * ((1-c)/(2-c)) = 1/3 ↔ q = (1+c)/3) := by
  refine ⟨by grind, ?_⟩
  have e : q * (c/(1+c)) + (1-q) * ((1-c)/(2-c)) - 1/3
      = (q - (1+c)/3) * (c/(1+c) - (1-c)/(2-c)) := by grind
  have d : c/(1+c) - (1-c)/(2-c) ≠ 0 := by
    have : c/(1+c) - (1-c)/(2-c) = (2*c - 1)/((1+c)*(2-c)) := by grind
    rw [this]; intro h
    have k : (2*c - 1) = (2*c-1)/((1+c)*(2-c)) * ((1+c)*(2-c)) := by grind
    rw [h] at k; grind
  constructor
  · intro h
    have z : (q - (1+c)/3) * (c/(1+c) - (1-c)/(2-c)) = 0 := by grind
    rcases Rat.mul_eq_zero.mp z with z | z
    · grind
    · exact absurd z d
  · intro h; rw [h]; grind

/-- AMIN'S WEDNESDAY: (heads, a `Monday` ball, Monday is the day picked), the coin fair, the ball
    at `c`, the pick at 1/2, independent ("picked without regard to the coin", "independent of
    `H` and `C`"). -/
noncomputable def wednesday (c : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : Measure (Bool × Bool × Bool) :=
  prod3 (1/2) c (1/2) hb0 hb1 hc0 hc1 hb0 hb1

def wH : Bool × Bool × Bool → Prop := fun p => p.1 = true
def wMwake : Bool × Bool × Bool → Prop := fun p => (p.1 = true ∧ p.2.1 = true) ∨ p.1 = false
def wTwake : Bool × Bool × Bool → Prop := fun p => (p.1 = true ∧ p.2.1 = false) ∨ p.1 = false
/-- `E_M = K_M ∧ [M]`: Monday picked and a Monday waking. -/
def wEM : Bool × Bool × Bool → Prop := fun p => p.2.2 = true ∧ wMwake p
/-- `E_T = K_T ∧ [T]`. -/
def wET : Bool × Bool × Bool → Prop := fun p => p.2.2 = false ∧ wTwake p
def wE : Bool × Bool × Bool → Prop := fun p => wEM p ∨ wET p

/-- **The Wednesday display, section 8.2**, source lines 1010-1018:
    `Pr(H | E_M) = Pr(H | [M]) = c/(1+c)`, `Pr(H | E_T) = Pr(H | [T]) = (1-c)/(2-c)`,
    `Pr(E_M | E) = (1+c)/3`, `Pr(E_T | E) = (2-c)/3`, `Pr(H | E) = 1/3`, with the justification:
    `Pr(E_M) = 1/2 Pr([M]) = (1+c)/4` and `Pr(E_T) = (2-c)/4`, which sum to `Pr(E) = 3/4`.
    Statement: all of these on the model, at every urn `0 < c < 1`. -/
theorem wednesday_display (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    (wednesday c (by grind) (by grind)).cond wH wEM = c/(1+c) ∧
    (wednesday c (by grind) (by grind)).cond wH wMwake = c/(1+c) ∧
    (wednesday c (by grind) (by grind)).cond wH wET = (1-c)/(2-c) ∧
    (wednesday c (by grind) (by grind)).cond wH wTwake = (1-c)/(2-c) ∧
    (wednesday c (by grind) (by grind)).cond wEM wE = (1+c)/3 ∧
    (wednesday c (by grind) (by grind)).cond wET wE = (2-c)/3 ∧
    (wednesday c (by grind) (by grind)).cond wH wE = 1/3 ∧
    (wednesday c (by grind) (by grind)).P wEM = (1+c)/4 ∧
    (wednesday c (by grind) (by grind)).P wEM = 1/2 * (wednesday c (by grind) (by grind)).P wMwake ∧
    (wednesday c (by grind) (by grind)).P wET = (2-c)/4 ∧
    (wednesday c (by grind) (by grind)).P wE = 3/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [wednesday, prod3, Measure.cond, wH, wEM, wET, wE, wMwake, wTwake, wt, ind_true,
    ind_false] <;> grind

/-- **Self-sampling on Wednesday, section 8.2**, source line 1023: "A self-sampling rule over your
    experimental wakings and Wednesday counts two in a heads run with a memory and three in a
    tails run. At the fair urn ... it gives heads `(1/4·1/2)/(1/4·1/2 + 1/2·1/3) = 3/7`."
    Statement: on the Wednesday model at `c = 1/2`, `Pr(H ∧ E) = 1/4` and `Pr(¬H ∧ E) = 1/2`; the
    rule gives the Wednesday member of a heads run with a memory 1/2 of its run and of a tails
    run 1/3; heads then has `(Pr(H∧E)·1/2)/(Pr(H∧E)·1/2 + Pr(¬H∧E)·1/3) = 3/7`, not 1/3.
    Choice: the runs with no memory are excluded (no Wednesday member with your evidence). -/
theorem wednesday_self_sampling :
    (wednesday (1/2) hb0 hb1).P (fun p => wH p ∧ wE p) = 1/4 ∧
    (wednesday (1/2) hb0 hb1).P (fun p => ¬ wH p ∧ wE p) = 1/2 ∧
    ((wednesday (1/2) hb0 hb1).P (fun p => wH p ∧ wE p) * (1/2)) /
      ((wednesday (1/2) hb0 hb1).P (fun p => wH p ∧ wE p) * (1/2)
        + (wednesday (1/2) hb0 hb1).P (fun p => ¬ wH p ∧ wE p) * (1/3)) = 3/7 ∧
    (3:Rat)/7 ≠ 1/3 := by
  have e1 : (wednesday (1/2) hb0 hb1).P (fun p => wH p ∧ wE p) = 1/4 := by
    simp [wednesday, prod3, wH, wE, wEM, wET, wMwake, wTwake, wt, ind_true, ind_false]; grind
  have e2 : (wednesday (1/2) hb0 hb1).P (fun p => ¬ wH p ∧ wE p) = 1/2 := by
    simp [wednesday, prod3, wH, wE, wEM, wET, wMwake, wTwake, wt, ind_true, ind_false]; grind
  refine ⟨e1, e2, ?_, by grind⟩
  rw [e1, e2]; grind

/-- **Announcements in every history, sections 8.3**, source line 1033: "With the announcements as
    events in every history, `Pr(H | [M]) = Pr(H | [T]) = Pr(H) = 1/2` is one proved value";
    source line 1041: "`[E]` takes place under `T` and under its rivals, so `Pr(T | [E]) = Pr(T)`."
    Statement: in any measure, an event `A` with `P(A) = 1` gives `P(X | A) = P(X)` for every
    `X`; with `P([M]) = P([T]) = 1` and `P(H) = 1/2`, `P(H | [M]) = P(H | [T]) = 1/2`.
    Choice: "an event in every history" (and "takes place under `T` and under its rivals") is an
    event of value 1. -/
theorem every_history {Ω : Type} (m : Measure Ω) (A X : Ω → Prop) (hA : m.ev A) (hX : m.ev X)
    (cert : m.P A = 1) : m.cond X A = m.P X := by
  have s := m.split hX hA
  have n : m.P (fun ω => X ω ∧ ¬ A ω) ≤ m.P (fun ω => ¬ A ω) :=
    m.mono (m.ev_and hX (m.ev_not hA)) (m.ev_not hA) (fun ω h => h.2)
  have p := m.nonneg (m.ev_and hX (m.ev_not hA))
  have c := m.compl hA
  unfold Measure.cond; rw [cert]; grind

theorem every_history_half {Ω : Type} (m : Measure Ω) (H M T : Ω → Prop) (hH : m.ev H)
    (hM : m.ev M) (hT : m.ev T) (cM : m.P M = 1) (cT : m.P T = 1) (coin : m.P H = 1/2) :
    m.cond H M = 1/2 ∧ m.cond H T = 1/2 :=
  ⟨(every_history m M H hM hH cM).trans coin, (every_history m T H hT hH cT).trans coin⟩

/-- **The puzzle's four premises, section 8.3**, source line 1035: "The Monday heads center equals
    the Monday tails center. The Monday tails center equals the Tuesday tails center. Each world
    has its whole probability on its two centers. The Monday heads center is above the Tuesday
    heads center. Whence heads is below tails."
    Statement: center values with `MH = MT`, `MT = TT`, `TH < MH`, heads the sum `MH + TH`, tails
    `MT + TT`: heads is below tails.
    Choice: "each world has its whole probability on its two centers" is that heads is the sum of
    its two centers and tails of its two. -/
theorem four_premises (MH MT TH TT : Rat) (p1 : MH = MT) (p2 : MT = TT) (p4 : TH < MH) :
    MH + TH < MT + TT := by grind

/-- **The green room, section 8.3**, source line 1039: "The paper's two claims on the ur-prior give
    the two undeceived tails centers equal probabilities and the deceived heads center a lower
    one. With these claims, the four probabilities cannot be chosen. Monday-heads equals
    Monday-tails equals Tuesday-tails equals Tuesday-heads, which contradicts the discount."
    Statement: positive center values with `MH/(MH+MT) = 1/2` (`Pr(H | [M]) = 1/2`),
    `TH/(TH+TT) = 1/2` (`Pr(H | [T]) = 1/2`) and `MT = TT`: all four are equal, so `TH < TT` is
    false.
    Choices: the conditionals on the announcements are ratios of center values; "the deceived
    heads center a lower one" is `TH < TT`. -/
theorem green_room (MH MT TH TT : Rat) (h1 : 0 < MH + MT) (h2 : 0 < TH + TT)
    (dM : MH/(MH+MT) = 1/2) (dT : TH/(TH+TT) = 1/2) (eq : MT = TT) :
    MH = MT ∧ MT = TT ∧ TT = TH ∧ ¬ TH < TT := by
  have a : MH = MH/(MH+MT) * (MH + MT) := by grind
  have b : TH = TH/(TH+TT) * (TH + TT) := by grind
  rw [dM] at a; rw [dT] at b
  refine ⟨by grind, eq, by grind, by grind⟩

/-- **Self-indication with bias, section 8.3**, source line 1039: "The paper's self-indication
    with bias gives the Tuesday subject `d/(1+d)` on heads. ... An onlooker beside her with her
    evidence has 1/2."
    Statement: a fair coin with the deceived heads center discounted by `d` and the tails center
    at 1 gives heads `(1/2·d)/(1/2·d + 1/2·1) = d/(1+d)`; it is 1/2 iff `d = 1`.
    Choice: the rule weights the heads center by `d` and the tails center by 1. -/
theorem biased_tuesday (d : Rat) (hd : 0 ≤ d) :
    (1/2 * d)/(1/2 * d + 1/2 * 1) = d/(1+d) ∧ (d/(1+d) = 1/2 ↔ d = 1) := by
  constructor <;> grind

theorem arith_multiverse (n : Rat) (hn : 0 < n) :
    (1/2) / ((1/2) + 1/(2*n)) = n/(n+1) := by grind

/-- **No Multiverse Bias, section 8.4**, source line 1049: "Consider, at the paper's priors, the
    world `W_B` with one observer of each of `n` types against `n` worlds with one observer each.
    ... The cell of being certain that `[k]` gives `Pr(W_B | [k]) = n/(n+1)`."
    Statement: in any measure with `W_B` and `W_k` exclusive, `P(W_B) = 1/2`, `P(W_k) = 1/(2n)`,
    and `[k] = W_B ∨ W_k`: `P(W_B | [k]) = n/(n+1)`.
    Choice: the paper's priors are not in the snapshot; `W_B` at 1/2 and each of the `n` small
    worlds at `1/(2n)` (the big world against the multiverse at even odds) is the choice that is
    stated; it gives the paper's `n/(n+1)`. The step by Sure Thing over the `n` cells is
    `sure_thing_n` (Displays.lean). Changed after the audit of 22 Nov: `1 ≤ n` in place of
    `0 < n` (for `0 < n < 1` the hypotheses cannot hold together). -/
theorem multiverse {Ω : Type} (m : Measure Ω) (WB Wk : Ω → Prop) (hB : m.ev WB) (hk : m.ev Wk)
    (excl : ∀ ω, ¬ (WB ω ∧ Wk ω)) (n : Rat) (hn : 1 ≤ n)
    (pB : m.P WB = 1/2) (pk : m.P Wk = 1/(2*n)) :
    m.cond WB (fun ω => WB ω ∨ Wk ω) = n/(n+1) := by
  unfold Measure.cond
  have e : m.P (fun ω => WB ω ∧ (WB ω ∨ Wk ω)) = m.P WB := m.Pcongr (fun ω => by grind)
  rw [e, m.add hB hk excl, pB, pk]
  exact arith_multiverse n (by grind)

/-- **Your measure against `ν`, section 8.5**, source line 1065: "In your measure a waking under
    a Monday ball is 99 times as probable as one under the Tuesday ball, 33/100 against 1/300".
    Statement: `(33/100)/(1/300) = 99`.
    Existing: the two values are in `display22_yours` (Displays.lean). -/
theorem ninety_nine : ((33:Rat)/100) / (1/300) = 99 := by grind

/-- **The maintenance man, section 8.5**, source line 1079: "`BIV ⊨ ¬D`, so
    `Pr(BIV | D) = Pr(D | BIV) Pr(BIV)/Pr(D) = 0`."
    Statement: in any measure, if every point of `BIV` is a point of `¬D`, `P(D) ≠ 0` and
    `P(BIV) ≠ 0`: `P(D | BIV) = 0`, `P(BIV | D) = P(D | BIV) P(BIV)/P(D)`, and both are 0.
    Choice: `⊨` is inclusion of the sets. -/
theorem biv {Ω : Type} (m : Measure Ω) (BIV D : Ω → Prop) (hB : m.ev BIV) (hD : m.ev D)
    (ent : ∀ ω, BIV ω → ¬ D ω) (pD : m.P D ≠ 0) (pB : m.P BIV ≠ 0) :
    m.cond D BIV = 0 ∧ m.cond BIV D = m.cond D BIV * m.P BIV / m.P D ∧ m.cond BIV D = 0 := by
  have z1 : m.P (fun ω => D ω ∧ BIV ω) = 0 := by
    rw [m.Pcongr (B := fun _ => False) (fun ω => ⟨fun h => ent ω h.2 h.1, fun h => h.elim⟩)]
    exact m.P_false
  have z2 : m.P (fun ω => BIV ω ∧ D ω) = 0 := by
    rw [m.Pcongr (B := fun _ => False) (fun ω => ⟨fun h => ent ω h.1 h.2, fun h => h.elim⟩)]
    exact m.P_false
  unfold Measure.cond
  rw [z1, z2]
  refine ⟨by grind, by grind, by grind⟩

end UrPrior

/-! ## Section 9: the absent-minded driver -/

section Driver

theorem sq_nn (x : Rat) : 0 ≤ x * x := by
  cases Classical.em (0 ≤ x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have := Rat.mul_nonneg (show (0:Rat) ≤ -x by grind) (show (0:Rat) ≤ -x by grind)
    grind

/-- Tag-swapped driving: (the ball marks `Monday`, so Monday's intersection is your first; the
    coin at your first intersection lands heads; the coin at your second lands heads), the ball
    at `c`, each coin heads with `1 - p` (tails with `p`), all independent. Heads closes the gate. -/
noncomputable def driving (c p : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (Bool × Bool × Bool) :=
  prod3 c (1-p) (1-p) hc0 hc1 (by grind) (by grind) (by grind) (by grind)

/-- You reach a closed gate at Monday's: Monday's is first and its coin lands heads, or Tuesday's
    is first, its coin lands tails, and Monday's coin lands heads. -/
def dMon : Bool × Bool × Bool → Prop := fun x =>
  (x.1 = true ∧ x.2.1 = true) ∨ (x.1 = false ∧ x.2.1 = false ∧ x.2.2 = true)
def dTue : Bool × Bool × Bool → Prop := fun x =>
  (x.1 = false ∧ x.2.1 = true) ∨ (x.1 = true ∧ x.2.1 = false ∧ x.2.2 = true)
/-- You reach a closed gate. -/
def dGate : Bool × Bool × Bool → Prop := fun x => dMon x ∨ dTue x
/-- The prize: the closed gate is at your second intersection. -/
def dPrize : Bool × Bool × Bool → Prop := fun x => x.2.1 = false ∧ x.2.2 = true

/-- **Tag-swapped driving, section 9**, source line 1096: "Say it reads `Monday'. There are two
    ways to have reached a closed gate at Monday's. Either Monday's was your first intersection,
    and its coin landed heads. The first way has a quarter. Or it was your second ... The second
    way has an eighth. You get the prize only in the second way. So with the sign reading
    `Monday' the prize has 1/3. With the sign reading `Tuesday' the same holds. (If both coins
    land tails you drive past both and reach no closed gate.)"
    Source line 1098: "So before you see the sign the prize has 1/3, by Sure Thing."
    Source line 1100: "the prize has 1/3 given either ball."
    Statement, on the model with a fair urn and fair coins: the first way has 1/4, the second
    1/8; the prize has 1/3 given a closed gate at Monday's, at Tuesday's, and at either; no
    closed gate has 1/4; given a closed gate, the prize has 1/3 given either ball. -/
theorem tag_swapped_driving :
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).P (fun x => x.1 = true ∧ x.2.1 = true) = 1/4 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).P
      (fun x => x.1 = false ∧ x.2.1 = false ∧ x.2.2 = true) = 1/8 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).cond dPrize dMon = 1/3 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).cond dPrize dTue = 1/3 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).cond dPrize dGate = 1/3 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).P (fun x => ¬ dGate x) = 1/4 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).cond dPrize (fun x => dGate x ∧ x.1 = true) = 1/3 ∧
    (driving (1/2) (1/2) hb0 hb1 hb0 hb1).cond dPrize (fun x => dGate x ∧ x.1 = false) = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [driving, prod3, Measure.cond, dMon, dTue, dGate, dPrize, wt, ind_true, ind_false] <;> grind

/-- **Monday balls only, and the driver's coin back, section 9**, source line 1102: "With Monday
    balls only, Monday's intersection always comes first ... You reach a closed gate at Monday's
    with a half and at Tuesday's with a quarter. So the closed gate is Monday's with 2/3, and the
    prize has 1/3." Source line 1104: "Say it lands tails with probability `p` instead of a half.
    You then reach a closed gate at Monday's with `1-p` and at Tuesday's with `p(1-p)`. So the
    closed gate is Monday's with `1/(1+p)`."
    Statement, on the model at `c = 1`, every `0 ≤ p < 1`: the two values and `1/(1+p)`; at
    `p = 1/2`: 1/2, 1/4, 2/3, and the prize 1/3 given a closed gate. -/
theorem monday_balls_driving (p : Rat) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (driving 1 p one0 one1 hp0 (by grind)).P dMon = 1 - p ∧
    (driving 1 p one0 one1 hp0 (by grind)).P dTue = p * (1-p) ∧
    (driving 1 p one0 one1 hp0 (by grind)).cond dMon dGate = 1/(1+p) ∧
    (driving 1 (1/2) one0 one1 hb0 hb1).P dMon = 1/2 ∧
    (driving 1 (1/2) one0 one1 hb0 hb1).P dTue = 1/4 ∧
    (driving 1 (1/2) one0 one1 hb0 hb1).cond dMon dGate = 2/3 ∧
    (driving 1 (1/2) one0 one1 hb0 hb1).cond dPrize dGate = 1/3 := by
  have k : (0:Rat) < 1 - p := by grind
  have k2 : 0 ≤ p * (1 - p) := Rat.mul_nonneg hp0 (by grind)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [driving, prod3, Measure.cond, dMon, dTue, dGate, dPrize, wt, ind_true, ind_false] <;> grind

/-- **The act at the intersection, section 9.1**, source line 1122: "if this is the first
    intersection, driving on pays 1 with probability `r`. After driving on from the first, you are
    paid 4 with probability `1-r` ... With `1/(1+r)` for the first and the rest for the second,
    driving on minus turning is `-2(3r-2)/(r+1)`. It is zero at `r = 2/3`. A coin chosen in advance
    is worth `4p(1-p) + p^2 = 4p - 3p^2`, and the best one is also at 2/3."
    Statement, the expectations written out: with `α = 1/(1+r)` for the first intersection,
    driving on is worth `α((1-r)·4 + r·1) + (1-α)·1`, turning `α·0 + (1-α)·4`; their difference
    is `-2(3r-2)/(r+1)` and is 0 iff `r = 2/3`; the coin chosen in advance is worth
    `(1-p)·0 + p(1-p)·4 + p^2·1 = 4p - 3p^2`, at most `4/3`, with equality iff `p = 2/3`. -/
theorem driver_payoffs (r p : Rat) (hr0 : 0 ≤ r) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1/(1+r)) * ((1-r)*4 + r*1) + (1 - 1/(1+r)) * 1 - ((1/(1+r)) * 0 + (1 - 1/(1+r)) * 4)
      = -2*(3*r-2)/(r+1) ∧
    (-2*(3*r-2)/(r+1) = 0 ↔ r = 2/3) ∧
    (1-p)*0 + p*(1-p)*4 + p^2*1 = 4*p - 3*p^2 ∧
    4*p - 3*p^2 ≤ 4/3 ∧ (4*p - 3*p^2 = 4/3 ↔ p = 2/3) := by
  have sq := sq_nn (p - 2/3)
  have hr : (0:Rat) < 1 + r := by grind
  refine ⟨by grind, ?_, by grind, by grind, ?_⟩
  · constructor
    · intro h
      have k : -2*(3*r-2) = -2*(3*r-2)/(r+1) * (r+1) := by grind
      rw [h] at k; grind
    · intro h; subst h; grind
  · constructor
    · intro h
      have z : (p - 2/3) * (p - 2/3) = 0 := by grind
      rcases Rat.mul_eq_zero.mp z with z | z <;> grind
    · intro h; subst h; grind

/-- **Any payoffs, section 9.1**, source line 1126: "Let turning pay `x` at the first intersection
    and `y` at the second, and let driving past both pay `z`. A coin chosen in advance is then
    worth `(1-p)x + p(1-p)y + p^2 z`. At the intersection, with `1/(1+r)` for the probability that
    it is the first, driving on minus turning is `[(y-x) - 2r(y-z)]/(1+r)`. This difference is the
    derivative of the coin's worth, taken at `r` and divided by `1+r`. So the two are zero at the
    same coin, whatever the payoffs. With 1 in place of 0 for turning at the first intersection,
    the best coin is the fair one, in place of 2/3."
    Statement: the expectations written out give the difference `[(y-x) - 2r(y-z)]/(1+r)`; with
    `D(r) = (y-x) - 2r(y-z)`, `worth(p) - worth(r) = (p-r)(D(r) - (p-r)(y-z))`, so `D(r)` is the
    derivative of the worth at `r`; the difference is 0 iff `D(r) = 0`; at `x = 1`, `y = 4`,
    `z = 1`: `D(r) = 0` iff `r = 1/2`, and the worth `1 + 3p - 3p^2` is at most `7/4` with
    equality iff `p = 1/2`.
    Choice: "the derivative" is stated through the exact difference quotient (no limits). -/
theorem driver_any_payoffs (x y z r p : Rat) (hr0 : 0 ≤ r) :
    (1/(1+r)) * ((1-r)*y + r*z) + (1 - 1/(1+r)) * z - ((1/(1+r)) * x + (1 - 1/(1+r)) * y)
      = ((y-x) - 2*r*(y-z))/(1+r) ∧
    ((1-p)*x + p*(1-p)*y + p^2*z) - ((1-r)*x + r*(1-r)*y + r^2*z)
      = (p - r) * (((y-x) - 2*r*(y-z)) - (p - r)*(y-z)) ∧
    (((y-x) - 2*r*(y-z))/(1+r) = 0 ↔ (y-x) - 2*r*(y-z) = 0) ∧
    (((4:Rat)-1) - 2*r*(4-1) = 0 ↔ r = 1/2) ∧
    ((1-p)*1 + p*(1-p)*4 + p^2*1 = 1 + 3*p - 3*p^2) ∧
    1 + 3*p - 3*p^2 ≤ 7/4 ∧ (1 + 3*p - 3*p^2 = 7/4 ↔ p = 1/2) := by
  have sq := sq_nn (p - 1/2)
  have hr : (0:Rat) < 1 + r := by grind
  refine ⟨by grind, by grind, ?_, by grind, by grind, by grind, ?_⟩
  · constructor
    · intro h
      have k : (y-x) - 2*r*(y-z) = ((y-x) - 2*r*(y-z))/(1+r) * (1+r) := by grind
      rw [h] at k; grind
    · intro h; rw [h]; grind
  · constructor
    · intro h
      have zz : (p - 1/2) * (p - 1/2) = 0 := by grind
      rcases Rat.mul_eq_zero.mp zz with zz | zz <;> grind
    · intro h; subst h; grind

/-- **Z-consistency in its symmetric form, section 9.2**, source line 1134: "In its symmetric form
    it keeps the run probabilities and divides a two-visit run equally between its intersections.
    That gives the first intersection `(2-p)/2`, where your measure has `1/(1+p)`."
    Statement: the run that turns at the first intersection (`1-p`) has one visit, the run that
    drives on (`p`) two; dividing the second equally gives the first intersection
    `(1-p)·1 + p·(1/2) = (2-p)/2`, which differs from `1/(1+p)` at every `0 < p < 1`. -/
theorem z_consistency (p : Rat) (hp0 : 0 < p) (hp1 : p < 1) :
    (1-p)*1 + p*(1/2) = (2-p)/2 ∧ (2-p)/2 ≠ 1/(1+p) := by
  refine ⟨by grind, fun h => ?_⟩
  have k : (2-p) * (1+p) = 2 := by
    have : (1:Rat) = 1/(1+p) * (1+p) := by grind
    grind
  have : p * (1 - p) = 0 := by grind
  rcases Rat.mul_eq_zero.mp this with z | z <;> grind

/-- The clock-times of the driver paper as a model: (the clock-time is the first, the coin at the
    first intersection drives on, the coin at the second drives on), the first clock-time at `w`,
    each coin drives on with `p`. -/
noncomputable def clock (w p : Rat) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (Bool × Bool × Bool) :=
  prod3 w p p hw0 hw1 hp0 hp1 hp0 hp1

def kFirst : Bool × Bool × Bool → Prop := fun x => x.1 = true
/-- At an intersection: at the first clock-time always; at the second iff you drove on at the
    first. -/
def kAt : Bool × Bool × Bool → Prop := fun x => x.1 = true ∨ (x.1 = false ∧ x.2.1 = true)
def kTurnFirst : Bool × Bool × Bool → Prop := fun x => x.1 = true ∧ x.2.1 = false

/-- **The urn on the clock-times, section 9.2**, source line 1136: "let the probability on the
    clock-times be set by an urn at `w` in place of 1/2, say at a third. The rule gives the first
    intersection `w/(w+(1-w)p)` in place of `1/(1+p)`. With the fair coin, the first intersection
    has `2w/(1+w)` in place of 2/3. The probability of turning at the first intersection is
    `w/(1+w)`, a quarter with the urn at a third, where the tag-swapping lemma has 1/3. ... The
    proved value comes out at `w = 1/2` only."
    Statement, on the model at `0 < w < 1`, `0 < p ≤ 1`: `π(first | at an intersection) =
    w/(w+(1-w)p)`, equal to `1/(1+p)` iff `w = 1/2`; at `p = 1/2`: `2w/(1+w)` and turning at the
    first `w/(1+w)`; at `w = 1/3`, a quarter; at `w = 1/2`, 2/3 and 1/3.
    Choice: "being at an intersection" at a clock-time is the event `kAt`; "the probability of
    turning at the first intersection" is `π(first ∧ turn | at an intersection)`. -/
theorem clock_urn (w p : Rat) (hw0 : 0 < w) (hw1 : w < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (clock w p (by grind) (by grind) (by grind) hp1).cond kFirst kAt = w/(w + (1-w)*p) ∧
    (w/(w + (1-w)*p) = 1/(1+p) ↔ w = 1/2) ∧
    (clock w (1/2) (by grind) (by grind) hb0 hb1).cond kFirst kAt = 2*w/(1+w) ∧
    (clock w (1/2) (by grind) (by grind) hb0 hb1).cond kTurnFirst kAt = w/(1+w) ∧
    (clock (1/3) (1/2) (by grind) (by grind) hb0 hb1).cond kTurnFirst kAt = 1/4 ∧
    (clock (1/2) (1/2) hb0 hb1 hb0 hb1).cond kFirst kAt = 2/3 ∧
    (clock (1/2) (1/2) hb0 hb1 hb0 hb1).cond kTurnFirst kAt = 1/3 := by
  have k : 0 < (1-w)*p := Rat.mul_pos (by grind) hp0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [clock, prod3, Measure.cond, kFirst, kAt, wt, ind_true, ind_false]; grind
  · constructor
    · intro h
      have a : w * (1+p) = w + (1-w)*p := by
        have e1 : w = w/(w + (1-w)*p) * (w + (1-w)*p) := by grind
        have e2 : (1:Rat) = 1/(1+p) * (1+p) := by grind
        rw [h] at e1; grind
      have b : p * (2*w - 1) = 0 := by grind
      rcases Rat.mul_eq_zero.mp b with z | z <;> grind
    · intro h; subst h; grind
  all_goals simp [clock, prod3, Measure.cond, kFirst, kAt, kTurnFirst, wt, ind_true, ind_false]
  all_goals grind

/-- **The planner's two events, section 9.2**, source line 1138: "The first and the second
    intersection are cells of your measure at an intersection, where the first has `1/(1+p)`.
    That is one only for the coin that always turns. ... You always go through the first
    intersection. Whether you get to the second depends on what you do at the first. So the ratio
    is 1 to `p` ... Those are the planner's probabilities ... of two events that overlap. They add
    up to more than one."
    Statement: `1/(1+p) = 1` iff `p = 0` (for `p ≥ 0`); on the two coins (drive on with `p`),
    going through the first has 1, going through the second `p`, their sum `1 + p` is above 1 at
    every `p > 0`, and the two overlap with `p`. -/
theorem planner_events (p : Rat) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ p' : Rat, 0 ≤ p' → (1/(1+p') = 1 ↔ p' = 0)) ∧
    (prod2 p p (by grind) hp1 (by grind) hp1).P (fun _ => True) = 1 ∧
    (prod2 p p (by grind) hp1 (by grind) hp1).P (fun x => x.1 = true) = p ∧
    1 < (prod2 p p (by grind) hp1 (by grind) hp1).P (fun _ => True)
      + (prod2 p p (by grind) hp1 (by grind) hp1).P (fun x => x.1 = true) ∧
    (prod2 p p (by grind) hp1 (by grind) hp1).P (fun x => True ∧ x.1 = true) = p := by
  refine ⟨fun p' hp' => ⟨fun h => ?_, fun h => by subst h; grind⟩, ?_, ?_, ?_, ?_⟩
  · have : (1:Rat) = 1/(1+p') * (1+p') := by grind
    grind
  all_goals simp [prod2, wt, ind_true, ind_false]
  all_goals grind

end Driver

/-! ## Section 10.1: the train -/

section Train

/-- The train: (England is in the final, France is in the final, if both won the third ticket's
    celebration is England's), the first two at 1/2 each and independent ("I took each bet as fair
    at even odds ... the bets independent"), the third at `r` (1/2 when taken at even odds). -/
noncomputable def train (r : Rat) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Measure (Bool × Bool × Bool) :=
  prod3 (1/2) (1/2) r hb0 hb1 hb0 hb1 hr0 hr1

def trE : Bool × Bool × Bool → Prop := fun x => x.1 = true
def trF : Bool × Bool × Bool → Prop := fun x => x.2.1 = true
def trEF : Bool × Bool × Bool → Prop := fun x => x.1 = true ∧ x.2.1 = true
/-- `O_E`: I came from England's celebration. -/
def trOE : Bool × Bool × Bool → Prop := fun x =>
  (x.1 = true ∧ x.2.1 = false) ∨ (x.1 = true ∧ x.2.1 = true ∧ x.2.2 = true)
def trOF : Bool × Bool × Bool → Prop := fun x =>
  (x.1 = false ∧ x.2.1 = true) ∨ (x.1 = true ∧ x.2.1 = true ∧ x.2.2 = false)

/-- **The train, section 10.1**, source line 1184: "`Pr(E) = Pr(F) = 1/2`, the bets independent,
    `Pr(E ∧ F) = 1/4`; and the third ticket gives `Pr(O_E) = 1/4 + 1/8 = 3/8`." Source lines
    1188-1192: `π(E ∧ F | a) = Pr(E ∧ F | O_E) = (1/8)/(3/8) = 1/3`, `π(E ∧ F | b) =
    Pr(E ∧ F | O_F) = 1/3`; "The conditional on the celebration I remember gives
    `Pr(E ∧ F | E ∨ F) = 1/3` as well. ... Both differ from the 1/4 I gave both bets".
    Statement, on the model at `r = 1/2`: these values; `Pr(E ∧ ¬F) = 1/4` and
    `Pr(E ∧ F ∧ Z) = 1/8`. -/
theorem train_values :
    (train (1/2) hb0 hb1).P trE = 1/2 ∧ (train (1/2) hb0 hb1).P trF = 1/2 ∧
    (train (1/2) hb0 hb1).P trEF = 1/4 ∧
    (train (1/2) hb0 hb1).P (fun x => x.1 = true ∧ x.2.1 = false) = 1/4 ∧
    (train (1/2) hb0 hb1).P (fun x => x.1 = true ∧ x.2.1 = true ∧ x.2.2 = true) = 1/8 ∧
    (train (1/2) hb0 hb1).P trOE = 3/8 ∧
    (train (1/2) hb0 hb1).cond trEF trOE = 1/3 ∧ (train (1/2) hb0 hb1).cond trEF trOF = 1/3 ∧
    (train (1/2) hb0 hb1).cond trEF (fun x => trE x ∨ trF x) = 1/3 ∧ (1:Rat)/3 ≠ 1/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by grind⟩ <;>
  simp [train, prod3, Measure.cond, trE, trF, trEF, trOE, trOF, wt, ind_true, ind_false] <;> grind

/-- **The train's cells, section 10.1**, source line 1192: "Both cells give a third, so by Sure
    Thing (section 1.3) `π(E ∧ F) = 1/3` for every `0 < w < 1`."
    Statement: any measure `π` with two cells `a`, `b` that partition it, `π(a) = w` with
    `0 < w < 1`, and the construction's identities `π(E∧F | a) = Pr(E∧F | O_E)`,
    `π(E∧F | b) = Pr(E∧F | O_F)` on the train model, gives `π(E ∧ F) = 1/3`.
    Choice: the two cells are exclusive and exhaustive as sets (as in Appendix B), which gives
    (4), `π(a ∧ b) = 0`, `π(a ∨ b) = 1`. -/
theorem train_cells {Ω : Type} (π : Measure Ω) (EF a b : Ω → Prop) (hEF : π.ev EF) (ha : π.ev a)
    (hb : π.ev b) (w : Rat) (hw : π.P a = w) (hw0 : 0 < w) (hw1 : w < 1)
    (excl : ∀ ω, ¬ (a ω ∧ b ω)) (exh : ∀ ω, a ω ∨ b ω)
    (ca : π.cond EF a = (train (1/2) hb0 hb1).cond trEF trOE)
    (cb : π.cond EF b = (train (1/2) hb0 hb1).cond trEF trOF) : π.P EF = 1/3 := by
  obtain ⟨_, _, _, _, _, _, v1, v2, _⟩ := train_values
  have h_and : π.P (fun ω => a ω ∧ b ω) = 0 := by
    rw [π.Pcongr (B := fun _ => False) (fun ω => ⟨fun h => excl ω h, fun h => h.elim⟩)]
    exact π.P_false
  have h_or : π.P (fun ω => a ω ∨ b ω) = 1 := by
    rw [π.Pcongr (B := fun _ => True) (fun ω => ⟨fun _ => trivial, fun _ => exh ω⟩)]
    exact π.total
  have s := π.add ha hb excl
  have pb : π.P b ≠ 0 := by grind
  exact π.sure_thing_cells hEF ha hb (by grind) pb (ca.trans v1) (cb.trans v2) h_and h_or

/-- **The third ticket at another price, section 10.1**, source line 1192: "Had I taken the third
    ticket as fair at another price, `r` in place of 1/2, by the same count the two cells would
    give `r/(1+r)` and `(1-r)/(2-r)`. The value would still be a third. Given a celebration, the
    tickets give the two origins the probabilities `(1+r)/3` and `(2-r)/3`."
    Statement, on the model at every `0 ≤ r ≤ 1`: `Pr(E∧F | O_E) = r/(1+r)`,
    `Pr(E∧F | O_F) = (1-r)/(2-r)`, `Pr(E∧F | E ∨ F) = 1/3`, `Pr(O_E | E∨F) = (1+r)/3`,
    `Pr(O_F | E∨F) = (2-r)/3`, and the cell values weighted by these give 1/3.
    Choice: "the value would still be a third" is read as `Pr(E ∧ F | E ∨ F)`, equal to the
    weighted sum with the origins' probabilities given a celebration; with other weights `w` the
    sum is not 1/3 when `r ≠ 1/2` (the paper's "for every `0 < w < 1`" is said at `r = 1/2`). -/
theorem train_any_price (r : Rat) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (train r hr0 hr1).cond trEF trOE = r/(1+r) ∧
    (train r hr0 hr1).cond trEF trOF = (1-r)/(2-r) ∧
    (train r hr0 hr1).cond trEF (fun x => trE x ∨ trF x) = 1/3 ∧
    (train r hr0 hr1).cond trOE (fun x => trE x ∨ trF x) = (1+r)/3 ∧
    (train r hr0 hr1).cond trOF (fun x => trE x ∨ trF x) = (2-r)/3 ∧
    (1+r)/3 * (r/(1+r)) + (2-r)/3 * ((1-r)/(2-r)) = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by grind⟩ <;>
  simp [train, prod3, Measure.cond, trE, trF, trEF, trOE, trOF, wt, ind_true, ind_false] <;> grind

end Train

/-! ## Section 7.1: before and at the waking -/

section Waking

/-- **Before entering Gilad's room, section 7.1**, source line 829: "before entering the room, or
    on Sunday, with no partition, your probability for heads is 1/2, and when you are asked to
    enter your unknown side, it goes to 1/3."
    Statement, on Gilad's model (even urn, even side): `π(H) = 1/2` and `π(H | in the room) = 1/3`.
    Choice: "before entering" is the model's unconditional value; "when you enter" is the value
    given that you are in the room. -/
theorem gilad_before :
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).P gH = 1/2 ∧
    (gilad (1/2) (1/2) half_bounds.1 half_bounds.2 half_bounds.1 half_bounds.2).cond gH gIn
      = 1/3 := by
  refine ⟨?_, ?_⟩ <;> simp [gilad, prod3, Measure.cond, gH, gIn, wt, ind_true, ind_false] <;> grind

/-- **Nothing excluded at the waking, section 7.1**, source line 831: "At the waking, tails goes
    from 1/2 to 2/3 with nothing excluded."
    Statement: `Pr(¬H) = 1/2` on the recording's model; on your model of Appendix B at every
    `0 < q < 1`, `π(¬H) = 2/3`, and each of the four outcomes keeps a positive value (the points
    over it have positive value).
    Choice: "nothing excluded" is that no outcome has value 0 in `π`. -/
theorem tails_two_thirds (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) :
    PrModel.P (fun n => ¬ Hout n) = 1/2 ∧
    (piModel q hq0 hq1).P (fun x => ¬ Hpt x) = 2/3 ∧
    ∀ n : Outcome, 0 < (piModel q hq0 hq1).P (fun x => pmap x = n) := by
  refine ⟨?_, ?_, fun n => ?_⟩
  · simp [PrModel, Hout, ind_true, ind_false]; grind
  · simp [piModel, Hpt, ind_true, ind_false]; grind
  · cases n <;> simp [piModel, pmap, ind_true, ind_false] <;> grind

end Waking

/-! ## Added after the audit of 22 Nov

Each theorem answers an item of `AUDIT_of_Cases_22nov.txt` (sections B and D). -/

section AuditAdded

/-- **Item 1 (audit B1). Two values for `H` itself, section 5.3**, source line 703: "When Amin
    walks in, `u = 1`, the rule is conditioning on `R` from Sunday, and they are two values for
    `H` itself."
    Statement: one type `Ω`, one event `H`, one event `R`. `Pr_A` is the Sunday measure with
    `Pr_A(H | R) = 1/2`; `Q` is (J) on `R` at `u = 1`; `π_A` is a measure on the same type with `R`
    certain and `π_A(H | R) = 1/3`. Then `Q(H) = 1/2`, `π_A(H) = 1/3`, and `Q(H) ≠ π_A(H)`.
    Choice: "your measure at the waking" is `π_A`, the rule's measure is `Q`; both measure the
    same event `H` of the same type. -/
theorem amina_one_space {Ω : Type} (PrA πA : Measure Ω) (H R : Ω → Prop) (hR : PrA.ev R)
    (h0 : PrA.P R ≠ 0) (h1 : PrA.P (fun ω => ¬ R ω) ≠ 0) (iR : PrA.cond H R = 1/2)
    (hH' : πA.ev H) (hR' : πA.ev R) (cert : πA.P R = 1) (r : πA.cond H R = 1/3) :
    (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H = 1/2 ∧ πA.P H = 1/3 ∧
    (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H ≠ πA.P H := by
  have q : (PrA.jeffrey R hR h0 h1 1 (by grind) (by grind)).P H = 1/2 := by
    show (1 : Rat) * PrA.cond H R + (1 - 1) * PrA.cond H (fun ω => ¬ R ω) = 1/2
    rw [iR]; grind
  have p := πA.certain_gives_ratio hH' hR' cert r
  refine ⟨q, p, ?_⟩
  rw [q, p]; grind

/-- The hypotheses of `amina_one_space` can be met on one type: on `Bool × Bool` (heads, `R`),
    the Sunday measure with coin and `R` independent at 1/2 each, and a waking measure with heads
    at 1/3 and `R` certain. -/
theorem amina_one_space_model :
    (prod2 (1/2) (1/2) hb0 hb1 hb0 hb1).P (fun p => p.2 = true) ≠ 0 ∧
    (prod2 (1/2) (1/2) hb0 hb1 hb0 hb1).P (fun p => ¬ p.2 = true) ≠ 0 ∧
    (prod2 (1/2) (1/2) hb0 hb1 hb0 hb1).cond (fun p => p.1 = true) (fun p => p.2 = true) = 1/2 ∧
    (prod2 (1/3) 1 (by grind) (by grind) one0 one1).P (fun p => p.2 = true) = 1 ∧
    (prod2 (1/3) 1 (by grind) (by grind) one0 one1).cond (fun p => p.1 = true)
      (fun p => p.2 = true) = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [prod2, Measure.cond, wt, ind_true, ind_false] <;> grind

theorem arith_ratio_div (a b e : Rat) (he : e ≠ 0) (hb : b ≠ 0) : (a / e) / (b / e) = a / b := by
  grind

/-- **Item 2 (i) (audit B2). Jill's measure derived, section 3**, source line 325: "Jill's
    measure has `[M]` certain and the recording's values. By conditioning, a calculation from the
    axioms (section 5), `π_Jill = Pr(· | [M])`".
    Statement: any measure `J` on the four outcomes with `J([M]) = 1` that keeps the recording's
    ratio of `X` given `[M]` has `J(X) = Pr(X | [M])`; and `jill` is such a measure for every `X`
    (`jill([M]) = 1` and `jill(X | [M]) = Pr(X | [M])`).
    Choice: "the recording's values" in Jill's measure is the recording's ratio given `[M]`. -/
theorem jill_derived :
    (∀ (J : Measure Outcome) (X : Outcome → Prop), J.ev X → J.ev Mout → J.P Mout = 1 →
      J.cond X Mout = PrModel.cond X Mout → J.P X = PrModel.cond X Mout) ∧
    jill.P Mout = 1 ∧ ∀ X : Outcome → Prop, jill.cond X Mout = PrModel.cond X Mout := by
  have pM : PrModel.P Mout = 3/4 := by
    simp [PrModel, Mout, Hout, Cout, ind_true, ind_false]; grind
  refine ⟨fun J X hX hM cert same => J.certain_gives_ratio hX hM cert same, ?_, fun X => ?_⟩
  · simp [jill, PrModel, Measure.cond, Mout, Hout, Cout, ind_true, ind_false]; grind
  · show PrModel.cond (fun n => X n ∧ Mout n) Mout / PrModel.cond Mout Mout = PrModel.cond X Mout
    unfold Measure.cond
    rw [PrModel.Pcongr (A := fun n => (X n ∧ Mout n) ∧ Mout n) (B := fun n => X n ∧ Mout n)
      (fun n => by grind),
      PrModel.Pcongr (A := fun n => Mout n ∧ Mout n) (B := Mout) (fun n => by grind)]
    exact arith_ratio_div _ _ _ (by rw [pM]; grind) (by rw [pM]; grind)

/-- **Item 2 (ii) (audit B2). Your measure in `a` is Jill's, for every event, section 3**,
    source line 325: "`π(X | a) = π_Jill(X) = Pr(X | [M])`. In `b`, your value is `Pr(X | [T])`."
    Statement: for every event `X` of the experiment (any `X : Outcome → Prop`, pulled back to the
    six points by `p`), on `piModel q` at every `0 < q < 1`: `π(X∘p | a) = jill(X) = Pr(X | [M])`
    and `π(X∘p | b) = Pr(X | [T])`. -/
theorem jill_every_event (q : Rat) (hq0 : 0 < q) (hq1 : q < 1) (X : Outcome → Prop) :
    (piModel q hq0 hq1).cond (fun x => X (pmap x)) apt = jill.P X ∧
    jill.P X = PrModel.cond X Mout ∧
    (piModel q hq0 hq1).cond (fun x => X (pmap x)) bpt = PrModel.cond X Tout := by
  refine ⟨?_, rfl, ?_⟩
  · show (piModel q hq0 hq1).cond (fun x => X (pmap x)) apt = PrModel.cond X Mout
    simp [piModel, PrModel, Measure.cond, pmap, apt, Mout, Hout, Cout, ind_true, ind_false]
    grind
  · simp [piModel, PrModel, Measure.cond, pmap, bpt, Tout, Hout, Cout, ind_true, ind_false]
    grind

theorem arith_ticket (h nh x : Rat) (c : h + nh = 1) (five : h = 1/3) :
    h * (1 - x) + nh * (-x) = 1/3 - x := by grind

/-- **Item 3 (audit B5). Hating money swaps which is which, section 4**, source line 421: "At any
    other price one side has a positive expected value and the other a negative one, and hating
    money only swaps which is which."
    Statement: in any measure with `π(H) = 1/3` (5), the ticket paying 1 on `H` bought at price
    `x` is worth `π(H)(1-x) + π(¬H)(-x) = 1/3 - x` to the buyer; the seller's worth is its
    negation; at every `x ≠ 1/3` one is positive and the other negative; and with every worth
    negated (hating money) the buyer's and the seller's signs are exchanged: the buyer is positive
    for the money-lover iff the money-hating buyer is negative, and the same for the seller.
    Choice: hating money is the negation of every worth. -/
theorem hating_money {Ω : Type} (π : Measure Ω) (H : Ω → Prop) (hH : π.ev H)
    (five : π.P H = 1/3) (x : Rat) (hx : x ≠ 1/3) :
    π.P H * (1 - x) + π.P (fun ω => ¬ H ω) * (-x) = 1/3 - x ∧
    ((1/3 - x > 0 ∧ -(1/3 - x) < 0) ∨ (1/3 - x < 0 ∧ -(1/3 - x) > 0)) ∧
    (1/3 - x > 0 ↔ -(1/3 - x) < 0) ∧ (-(1/3 - x) > 0 ↔ -(-(1/3 - x)) < 0) ∧
    ((1/3 - x > 0 ∧ -(1/3 - x) < 0) ↔ (-(1/3 - x) < 0 ∧ -(-(1/3 - x)) > 0)) := by
  refine ⟨arith_ticket _ _ x (π.compl hH) five, ?_, by grind, by grind, by grind⟩
  cases Classical.em (x < 1/3) with
  | inl h => exact Or.inl ⟨by grind, by grind⟩
  | inr h => exact Or.inr ⟨by grind, by grind⟩

theorem arith_any_prior (b k n : Rat) (hk : 0 < k) (hb : b = n * k) (hn : 1 ≤ n) :
    b / (b + k) = n / (n + 1) := by
  subst hb
  have : n * k + k = (n + 1) * k := by grind
  rw [this]
  have hk0 : k ≠ 0 := by grind
  have hn0 : n + 1 ≠ 0 := by grind
  grind

/-- **Item 4 (audit B7). The reference-class case for any priors, section 8.4**, source line
    1049: "Consider, at the paper's priors, the world `W_B` with one observer of each of `n` types
    against `n` worlds with one observer each. ... The cell of being certain that `[k]` gives
    `Pr(W_B | [k]) = n/(n+1)`."
    Statement: in any measure with `W_B`, `W_k` exclusive, `P(W_k) > 0`, `P(W_B) = n P(W_k)`,
    `1 ≤ n`: `P(W_B | W_B ∨ W_k) = n/(n+1)`.
    Choice: "the paper's priors" are any priors with `W_B` at `n` times each small world. -/
theorem multiverse_any_priors {Ω : Type} (m : Measure Ω) (WB Wk : Ω → Prop) (hB : m.ev WB)
    (hk : m.ev Wk) (excl : ∀ ω, ¬ (WB ω ∧ Wk ω)) (n : Rat) (hn : 1 ≤ n)
    (pk : 0 < m.P Wk) (pB : m.P WB = n * m.P Wk) :
    m.cond WB (fun ω => WB ω ∨ Wk ω) = n/(n+1) := by
  unfold Measure.cond
  have e : m.P (fun ω => WB ω ∧ (WB ω ∨ Wk ω)) = m.P WB := m.Pcongr (fun ω => by grind)
  rw [e, m.add hB hk excl]
  exact arith_any_prior _ _ n pk pB hn

/-- How many of the two drivers pull in at the `Monday` station (the counterpart of
    `tueCustomers`). -/
def monCustomers (p : GasPt) : Rat :=
  match p with
  | (false, _, _, true) => 2
  | (false, _, _, false) => 0
  | (true, true, true, _) => 2
  | (true, false, true, _) => 0
  | (true, _, false, _) => 1

/-- **Item 5 (audit B10). The customers, section 6.1**, source line 790: "The only thing the
    Tuesday station would then get is the one customer who arrives on heads with no meeting: an
    eighth of all the customers."
    Statement: at every point the `Monday` and `Tuesday` counts sum to 2 (the two drivers); with
    the where and tails urns at 1 and the whether urn even, the expected customers are 7/4 at the
    `Monday` station and 1/4 at the `Tuesday` station per run, and the `Tuesday` station's
    expected customers over the sum of the two stations' expected customers is 1/8.
    Choice: as in `gas_both_urns`, "an eighth of all the customers" is a ratio of expected
    counts. -/
theorem gas_customers :
    (∀ p : GasPt, monCustomers p + tueCustomers p = 2) ∧
    gasExp 1 (1/2) 1 monCustomers = 7/4 ∧ gasExp 1 (1/2) 1 tueCustomers = 1/4 ∧
    gasExp 1 (1/2) 1 tueCustomers
      / (gasExp 1 (1/2) 1 monCustomers + gasExp 1 (1/2) 1 tueCustomers) = 1/8 := by
  refine ⟨fun p => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, d⟩ := p
    cases a <;> cases b <;> cases c <;> cases d <;> simp [monCustomers, tueCustomers] <;> grind
  · simp [gasExp, gasW, wt, monCustomers]; grind
  · simp [gasExp, gasW, wt, tueCustomers]; grind
  · simp [gasExp, gasW, wt, monCustomers, tueCustomers]; grind

def asT : Bool × Bool × Bool → Prop := fun p => (asH p ∧ ¬ asC p) ∨ ¬ asH p

/-- **Item 6 (audit B12, D1). The same for Tuesday, section 8.1**, source line 979: "That you are
    awakened on Monday has probability 3/4 under either assignment ... The same holds for
    Tuesday."
    Statement, on `assignment α` at every `0 < α < 1`: `Pr([T] | first is coin) =
    Pr([T] | second is coin) = 3/4`, and `Pr(first is coin | [T]) = α`. -/
theorem which_pair_tuesday (α : Rat) (h0 : 0 < α) (h1 : α < 1) :
    (assignment α (by grind) (by grind)).cond asT asA = 3/4 ∧
    (assignment α (by grind) (by grind)).cond asT (fun p => ¬ asA p) = 3/4 ∧
    (assignment α (by grind) (by grind)).cond asA asT = α := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [assignment, prod3, Measure.cond, asA, asT, asH, asC, wt, ind_true, ind_false] <;> grind

/-- Your measure on the six points at urn `c` (as `piModelC` in Displays.lean): `(R1,M)`,
    `(R3,M)`, `(R3,T)` at `c/3`; `(R4,M)`, `(R2,T)`, `(R4,T)` at `(1-c)/3`. -/
noncomputable def piUrn (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) : Measure Point where
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

/-- **Item 7 (audit D2). Equal tails wakings in the lemma's cells, section 8.5**, source line
    1071: "In the lemma's cells, (13), the two wakings of each tails outcome have equal
    probability."
    Statement: (i) on `piUrn c` at every `0 < c < 1`, the Monday point and the Tuesday point of
    each tails outcome have equal value (`(R3,M)` and `(R3,T)` at `c/3`; `(R4,M)` and `(R4,T)` at
    `(1-c)/3`); `π(a) = (1+c)/3`; heads 1/3. (ii) From the lines of (10) with `q = (1+c)/3`,
    `A = q/(1+c)`, `B = (1-q)/(2-c)`: the tails lines `a∧¬H∧C = cA` and `b∧¬H∧C = cB` are equal, and
    `a∧¬H∧¬C = (1-c)A` and `b∧¬H∧¬C = (1-c)B` are equal.
    Choice: the tails lines of (10) are read from its justification (heads is half of `a∧C` and
    of `b∧¬C`, none of `a∧¬C` or `b∧C`). The model's weights are put in, as in Displays.lean's
    `piModelC`, where (8)-(13) are checked against them. -/
theorem lemma_equal_tails (c : Rat) (hc0 : 0 < c) (hc1 : c < 1) :
    (piUrn c hc0 hc1).P (fun x => x = .R3M) = (piUrn c hc0 hc1).P (fun x => x = .R3T) ∧
    (piUrn c hc0 hc1).P (fun x => x = .R4M) = (piUrn c hc0 hc1).P (fun x => x = .R4T) ∧
    (piUrn c hc0 hc1).P apt = (1+c)/3 ∧ (piUrn c hc0 hc1).P Hpt = 1/3 ∧
    c * (((1+c)/3)/(1+c)) = c * ((1 - (1+c)/3)/(2-c)) ∧
    (1-c) * (((1+c)/3)/(1+c)) = (1-c) * ((1 - (1+c)/3)/(2-c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [piUrn, apt, Hpt, ind_true, ind_false]; grind)
  all_goals grind

/-- **Item 8 (audit D3). The big world keeps its prior, section 8.4**, source line 1049: "No
    Doomsday is the case of the Doomsday division. `[F]` takes place in both worlds, and the big
    world keeps its prior."
    Statement: in any measure, with `P([F]) = 1`, `P(W | [F]) = P(W)` (an instance of
    `every_history`).
    Choice: "takes place in both worlds" is `P([F]) = 1`. -/
theorem big_world_prior {Ω : Type} (m : Measure Ω) (W F : Ω → Prop) (hW : m.ev W) (hF : m.ev F)
    (cert : m.P F = 1) : m.cond W F = m.P W :=
  every_history m F W hF hW cert

/-- **Item 9 (audit D4). The train's cells are the lemma's ratios, section 10.1**, source line
    1192: "In the tag-swapping lemma, heads given either waking day has that day's ball
    probability divided by one plus that probability. The train's two cell values equal those
    ratios, with `r` for the urn's `c`."
    Statement, for every `0 ≤ r ≤ 1`: on the train model `Pr(E ∧ F | O_E)` equals, on the
    recording at urn `r` (`recUrn r`), `Pr(H | [M]) = r/(1+r)`; and `Pr(E ∧ F | O_F)` equals
    `Pr(H | [T]) = (1-r)/(1+(1-r))`. -/
theorem train_is_lemma (r : Rat) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (train r hr0 hr1).cond trEF trOE = (recUrn r hr0 hr1).cond rH rM ∧
    (recUrn r hr0 hr1).cond rH rM = r/(1+r) ∧
    (train r hr0 hr1).cond trEF trOF = (recUrn r hr0 hr1).cond rH rT ∧
    (recUrn r hr0 hr1).cond rH rT = (1-r)/(1+(1-r)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [train, recUrn, prod3, prod2, Measure.cond, trEF, trOE, trOF, rH, rM, rT, wt, ind_true,
    ind_false] <;> grind

end AuditAdded

end Cases

-- What the theorems rest on (Lean prints every axiom used):
#print axioms Cases.B2_sets
#print axioms Cases.sec1_on_model
#print axioms Cases.gilad_room
#print axioms Cases.gilad_any_urn
#print axioms Cases.gilad_box
#print axioms Cases.gilad_monday_only
#print axioms Cases.two_guesses
#print axioms Cases.guesses_footnote
#print axioms Cases.jack_and_jill
#print axioms Cases.jill_remembers
#print axioms Cases.other_price
#print axioms Cases.edt_per_run
#print axioms Cases.peanut_butter
#print axioms Cases.skewed_die
#print axioms Cases.fair_die
#print axioms Cases.partition_footnote
#print axioms Cases.amina_point_nine
#print axioms Cases.amina_bayes
#print axioms Cases.coin_055
#print axioms Cases.jeffrey_at_zero
#print axioms Cases.conditioning_commutes
#print axioms Cases.jeffrey_two_orders
#print axioms Cases.noisy_and_device
#print axioms Cases.amina_total
#print axioms Cases.amina_u_one
#print axioms Cases.just12
#print axioms Cases.gas_owner
#print axioms Cases.gas_altruist
#print axioms Cases.gas_both_urns
#print axioms Cases.gas_whether
#print axioms Cases.gas_sunday
#print axioms Cases.sb_sunday
#print axioms Cases.lambda_cells
#print axioms Cases.kappa_three_quarters
#print axioms Cases.double_halfer
#print axioms Cases.double_halfer_model
#print axioms Cases.outsiders_heads_only
#print axioms Cases.sunday_in_class
#print axioms Cases.doomsday_factor_limit
#print axioms Cases.schwarz_book
#print axioms Cases.mu_one
#print axioms Cases.temporal_monday
#print axioms Cases.von_neumann
#print axioms Cases.which_pair
#print axioms Cases.rule_weights
#print axioms Cases.wednesday_display
#print axioms Cases.wednesday_self_sampling
#print axioms Cases.every_history
#print axioms Cases.every_history_half
#print axioms Cases.four_premises
#print axioms Cases.green_room
#print axioms Cases.biased_tuesday
#print axioms Cases.multiverse
#print axioms Cases.ninety_nine
#print axioms Cases.biv
#print axioms Cases.tag_swapped_driving
#print axioms Cases.monday_balls_driving
#print axioms Cases.driver_payoffs
#print axioms Cases.driver_any_payoffs
#print axioms Cases.z_consistency
#print axioms Cases.clock_urn
#print axioms Cases.planner_events
#print axioms Cases.train_values
#print axioms Cases.train_cells
#print axioms Cases.train_any_price
#print axioms Cases.gilad_before
#print axioms Cases.tails_two_thirds
#print axioms Cases.amina_one_space
#print axioms Cases.amina_one_space_model
#print axioms Cases.jill_derived
#print axioms Cases.jill_every_event
#print axioms Cases.hating_money
#print axioms Cases.multiverse_any_priors
#print axioms Cases.gas_customers
#print axioms Cases.which_pair_tuesday
#print axioms Cases.lemma_equal_tails
#print axioms Cases.big_world_prior
#print axioms Cases.train_is_lemma
