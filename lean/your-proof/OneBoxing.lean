/-
  Section 4.1 of the paper "Your proof": one-boxing without evidential decision theory.

  What is checked here is the skeleton of that section: the arithmetic, and the structure of the
  rules it describes. Each theorem carries, in its comment, the sentence of the paper it states.

  What is NOT stated here, because it is not a calculation and Lean has no statement for it:
    - that anyone who gives a reason to one-box is thereby following a rule that takes the
      arrangement into account (the section's argument from the boxes "arranged for someone who
      failed to show up");
    - that the arranger can act on any rule whatever, a coin included ("So he knows the coin").
      The case is described that way; the theorems below take the description as given.

  Checked with Lean 4.36.0, using nothing beyond Lean's own library:  lean OneBoxing.lean
  A run with no error means every theorem below is accepted. The lines printed at the end name
  the axioms the results rest on.
-/

namespace OneBoxing

/-- The two acts: take the opaque box alone, or take both boxes. -/
inductive Act | one | two
  deriving DecidableEq

/-- The other act. -/
def other : Act → Act
  | .one => .two
  | .two => .one

/-- What an act gets: the opaque box holds a million or nothing, the transparent box a thousand. -/
def payoff (full : Bool) : Act → Nat
  | .one => if full then 1000000 else 0
  | .two => (if full then 1000000 else 0) + 1000

/-- "choosing two boxes is a thousand more whatever the opaque box holds". -/
theorem two_is_a_thousand_more (full : Bool) : payoff full .two = payoff full .one + 1000 := by
  cases full <;> rfl

/-! ### The arranger: "the opaque box holds the million iff you act against what your rule
    recommends" -/

/-- The opaque box is full exactly when the act goes against the recommendation. -/
def arranged (recommended act : Act) : Bool := decide (act ≠ recommended)

/-- What an act gets, with the recommendation in hand. -/
def gets (recommended act : Act) : Nat := payoff (arranged recommended act) act

/-- "Decide to take one, and there is a million and a thousand in taking two." -/
theorem decide_one : gets .one .two = 1001000 ∧ gets .one .one = 0 := by decide

/-- "Decide to take two, and there is a million in taking one." -/
theorem decide_two : gets .two .one = 1000000 ∧ gets .two .two = 1000 := by decide

/-- "Act against your identity and you are rich!": whatever is recommended, acting against the
    recommendation gets more than acting on it. -/
theorem acting_against_gets_more : ∀ r : Act, gets r r < gets r (other r) := by
  intro r; cases r <;> decide

/-- A rule that takes the arrangement into account: with a recommendation in hand it goes to the
    act that then gets more. -/
def reconsider (recommended : Act) : Act :=
  if gets recommended .one > gets recommended .two then .one else .two

/-- "each recommends the other": one goes to two, and two goes to one. -/
theorem each_recommends_the_other : reconsider .one = .two ∧ reconsider .two = .one := by decide

/-- "whatever the rule outputs is the thing the arranger has arranged against": reconsidered, a
    recommendation always becomes the other act. -/
theorem reconsider_is_the_other : ∀ r : Act, reconsider r = other r := by
  intro r; cases r <;> decide

/-- "has no recommendation it can keep": no recommendation survives being reconsidered. -/
theorem no_recommendation_it_can_keep : ∀ r : Act, reconsider r ≠ r := by
  intro r; cases r <;> decide

/-! ### The two-boxer's rule: "two boxes, however the boxes were arranged" -/

/-- The two-boxer's rule compares the two acts with the opaque box as it is, whatever was
    recommended. It is written with the recommendation as an input so that it can be asked again
    "with the recommendation in hand"; the recommendation is not used. -/
def twoBoxer (_recommended : Act) (full : Bool) : Act :=
  if payoff full .one > payoff full .two then .one else .two

/-- "The two-boxer does, since choosing two boxes is a thousand more whatever the opaque box
    holds": whatever was recommended and whatever the box holds, the rule gives two boxes. -/
theorem two_boxes_however_arranged : ∀ (r : Act) (full : Bool), twoBoxer r full = .two := by
  intro r full; cases r <;> cases full <;> decide

/-- "A rule that keeps its recommendation recommends itself: asked again with the recommendation
    in hand, it gives it again." -/
theorem two_boxing_recommends_itself : ∀ full : Bool, twoBoxer .two full = .two :=
  fun full => two_boxes_however_arranged .two full

/-- "The only rule with a recommendation it can keep is ... two boxes, however the boxes were
    arranged": of the two rules, the two-boxer's keeps a recommendation and the rule that takes
    the arrangement into account keeps none. -/
theorem only_two_boxing_is_kept :
    (∃ r : Act, ∀ full : Bool, twoBoxer r full = r) ∧ ¬ (∃ r : Act, reconsider r = r) := by
  refine ⟨⟨.two, two_boxing_recommends_itself⟩, ?_⟩
  intro ⟨r, h⟩
  exact no_recommendation_it_can_keep r h

/-! ### The forms the section compares these with -/

/-- "this sentence is false": no sentence is true exactly when it is not. The rule above has
    the same form, with `reconsider` (the other act) in the place of "not". -/
theorem liar (a : Prop) : ¬ (a ↔ ¬ a) :=
  fun h => have na : ¬ a := fun ha => h.mp ha ha; na (h.mpr na)

/-- "`the sentence below is false' and, under it, `the sentence above is true'": the two cannot
    both be as they say. This is what "each rule recommending the other" would be. -/
theorem liar_pair (a b : Prop) : ¬ ((a ↔ ¬ b) ∧ (b ↔ a)) :=
  fun ⟨h1, h2⟩ => liar a ⟨fun ha hb => h1.mp ha (h2.mpr hb), fun na => h1.mpr (fun hb => na (h2.mp hb))⟩

/-! ### Gideon's paradox: "the prize is never given" -/

/-- If the prize is won exactly by an irrational choice, and a choice that wins the million is
    thereby not irrational ("will win the million and will hence be rational"), then the prize
    is not won ("you can't win") and the choice is not irrational ("you failed to be
    irrational"). -/
theorem gideon (wins irrational : Prop) (rule : wins ↔ irrational) (hence : wins → ¬ irrational) :
    ¬ wins ∧ ¬ irrational :=
  ⟨fun w => hence w (rule.mp w), fun i => hence (rule.mpr i) i⟩

/-! ### The mixture of the two rules: "you take one box as long as w times the prize is above
    the thousand. Now halve the weight ..." -/

/-- After `k` halvings of a weight that starts at 1, you still take one box iff the prize is
    above a thousand times 2 to the k (that is, `prize / 2^k > 1000`). -/
def stillOneBox (prize k : Nat) : Prop := prize > 1000 * 2 ^ k

instance (prize k : Nat) : Decidable (stillOneBox prize k) := by unfold stillOneBox; infer_instance

/-- "one at two thousand, two at four thousand, ten at a million": the halving at which the act
    settles, and that it has not settled one halving earlier. -/
theorem iterations :
    (stillOneBox 2000 0 ∧ ¬ stillOneBox 2000 1) ∧
    (stillOneBox 4000 1 ∧ ¬ stillOneBox 4000 2) ∧
    (stillOneBox 1000000 9 ∧ ¬ stillOneBox 1000000 10) := by decide

/-- The paper starts with all the weight on the one-boxing rule, `w = 1` (the theorem
    `iterations` above). The same three counts hold for any weight `w` to start from that is
    above 0.512 and at most 1: one halving at two thousand, two at four thousand, ten at a
    million. The halved weights are written out: w/2, w/4, w/512, w/1024. -/
theorem iterations_any_weight (w : Rat) (h1 : 64/125 < w) (h2 : w ≤ 1) :
    (w * 2000 > 1000 ∧ ¬ (w / 2 * 2000 > 1000)) ∧
    (w / 2 * 4000 > 1000 ∧ ¬ (w / 4 * 4000 > 1000)) ∧
    (w / 512 * 1000000 > 1000 ∧ ¬ (w / 1024 * 1000000 > 1000)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

/-- "The number of iterations ... grows with the prize": a prize that is still above the line
    after `k + 1` halvings is above it after `k`. -/
theorem later_needs_more (prize k : Nat) : stillOneBox prize (k + 1) → stillOneBox prize k := by
  unfold stillOneBox
  intro h
  have : 1000 * 2 ^ k ≤ 1000 * 2 ^ (k + 1) := by
    rw [Nat.pow_succ]; omega
  omega

/-- "With no bound on the prize it never settles": for every number of halvings there is a prize
    at which you would still take one box. -/
theorem never_settles : ∀ k : Nat, ∃ prize : Nat, stillOneBox prize k :=
  fun k => ⟨1000 * 2 ^ k + 1, Nat.lt_succ_self _⟩

/-! ### "A coin tossed in your head": the predictor puts nothing in the opaque box -/

/-- "With the box empty, you get nothing from one box and the thousand from two." -/
theorem empty_box : payoff false .one = 0 ∧ payoff false .two = 1000 := by decide

/-- "So every chance of landing on one box is a loss": with the box empty, a chance `t` of one
    box gets `(1 - t)` of the thousand, which is less than the thousand whenever `t` is
    positive. -/
theorem every_chance_is_a_loss (t : Rat) (_ht0 : 0 < t) (_ht1 : t ≤ 1) :
    t * 0 + (1 - t) * 1000 < 1000 := by grind

/-- "and the weight given to one-boxing is zero": the chance of one box that gets the whole
    thousand is 0, and no other. -/
theorem the_weight_is_zero (t : Rat) : t * 0 + (1 - t) * 1000 = 1000 ↔ t = 0 := by
  constructor <;> intro h <;> grind

end OneBoxing

#print axioms OneBoxing.two_is_a_thousand_more
#print axioms OneBoxing.acting_against_gets_more
#print axioms OneBoxing.reconsider_is_the_other
#print axioms OneBoxing.no_recommendation_it_can_keep
#print axioms OneBoxing.two_boxes_however_arranged
#print axioms OneBoxing.only_two_boxing_is_kept
#print axioms OneBoxing.liar
#print axioms OneBoxing.liar_pair
#print axioms OneBoxing.gideon
#print axioms OneBoxing.iterations
#print axioms OneBoxing.iterations_any_weight
#print axioms OneBoxing.later_needs_more
#print axioms OneBoxing.never_settles
#print axioms OneBoxing.every_chance_is_a_loss
#print axioms OneBoxing.the_weight_is_zero
