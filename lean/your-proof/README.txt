Lean 4 check of the proofs in "Your proof"
==========================================

Files (each stands alone)
  YourProof.lean             the main proof, Sure Thing, section 5.1, section 5.3, the models
  Displays.lean              the paper's other numbered displays, and numbers given in the text
  OneBoxing.lean             the skeleton of section 4.1
  Cases.lean                 the cases of the paper as finite models, with their values
  YourProof_any_field.lean   YourProof.lean with values in any ordered field
  Displays_any_field.lean    Displays.lean with values in any ordered field

What is checked
  - The Sure Thing theorem, for any finitely additive probability measure on any algebra of
    events.
  - The main proof of the paper, steps (1) to (5): from the recording's values (the coin at 1/2,
    the ball at 1/2, the two independent) and the construction (two cells that partition your
    measure, each with the recording's ratio for heads given the day's waking), heads has 1/3.
  - The model in sets of Appendix B: two measures that meet every condition of the proof, so
    the theorem is not empty. A four-point case does the same for section 5.3.
  - Section 5.1: the subdivision lemma; (S1), Sure Thing inside E; (S3), which is (B): in any
    later measure in which E is certain and the cells of E have the ratio for X that they are
    defined with, the unconditional probability of X is the conditional one; (S4).
  - Section 5.3: Jeffrey's rule (J) is defined as a measure. It gives E the value u and keeps
    the ratio inside E. Then the conflict: with her reliability at 9/10 and x at p, the measure
    in which her saying it is certain has x at 9p/(8p + 1); (J) with u = 9/10 has x at 9/10;
    the two differ unless p = 1/2; and whatever value (J) is given for x, it gives her saying
    it less than 1. Run from Sunday on R, (J) gives heads 1/2 given R at every u, and no
    measure has that together with 1/3 in each cell of R.

What the files assume, said plainly
  - Measures are finitely additive, on an algebra of events. In YourProof.lean, Displays.lean
    and Cases.lean they take rational values. The two files with any_field in the name state the same theorems
    with values in any ordered field, the real numbers included. There the finite models stay
    over the rationals, and four statements are left out: three about limits (an ordered field
    need not be Archimedean) and one footnote's arithmetic with fixed numbers.
  - In (S3), 'with the same definitions' is written as: the later measure gives X, in each cell
    of E, the ratio the first measure gives it. From that and E certain the value follows.
    YourProof.lean also states it with the definitions as one object (bayes_of_definitions).
    That the definitions are the same at the later point is argued in the paper, section 5.1;
    Lean checks what follows from it.
  - No measure meets the conditions of the main proof and gives heads a value other than 1/3
    (no_other_value).

How to run it
  1. Install Lean 4 (https://lean-lang.org). The files were checked with version 4.36.0.
  2. Run each file by itself:
       lean YourProof.lean
       lean Displays.lean
       lean OneBoxing.lean
       lean Cases.lean
       lean YourProof_any_field.lean
       lean Displays_any_field.lean
  Each run should end without any error or warning. It prints, for the results named at the end
  of the file, the axioms they rest on: propext, Classical.choice, Quot.sound, or fewer of
  these, or none. These are the axioms of Lean's standard logic. No library beyond Lean's own is used. The lines each
  run should print are in the files expected_output_*.txt.

How to read it
  Each theorem carries a comment naming the display or the sentence of the paper that it
  states. Lean certifies that each statement follows from the hypotheses written in front of
  it. Whether a statement says what the paper's sentence says is for the reader to check, by
  reading the two side by side.

The letters
  As in the paper: the Greek letter pi is your measure, and Pr is the recording's.

The numbered displays (Displays.lean)
  The paper's other numbered displays, each with the justification the paper gives after it:
  (6) and (7) of section 4; the tag-swapping lemma, (8) to (13), and (14); the measures set
  against the proved one, (15) to (22); the full measure, (23) and (24); (25); Sure Thing for a
  finite partition of n cells; (S5); Appendix A, (A1) to (A4); Appendix C, (C1) to (C3). Each
  theorem's comment gives the display's number, the display as it stands in the source, and any
  choice made in stating it.

The tag-swap equation by a second partition (in Displays.lean, not a display of the paper)
  In the lemma, (13) is derived from the equation pi(H | C) = pi(H | not-C). The file also derives
  that equation: with a second pair of cells, being certain that today is the day the ball marks
  and being certain that it is the other day, the ball has the urn's proportion c in each cell;
  Sure Thing gives pi(C) = c; with the lines of (10) that is A = B = 1/3. From it: (14) at every
  urn, pi(H | C) = 1/3, and, with C certain, pi(H) = 1/3; and the second line of (22).

The uneven urn has a model (in Displays.lean)
  For every proportion c strictly between 0 and 1, the recording's measure on the four outcomes
  and your measure on the six points (c/3, c/3, (1-c)/3 on the Monday points; (1-c)/3, c/3,
  (1-c)/3 on the Tuesday points) meet all the conditions of the lemma and of the second
  partition together, and the general theorems are applied to them. At c = 99/100 the values of
  (22) are read off the model.

Numbers given in the text (in Displays.lean)
  - After (19): the difference from 1/3 is exactly 2/(3(3N + 4)), and it is below any positive
    number from some N on.
  - After (21): the calculation with an uneven urn, stated with a measure.
  - Section 5.1, the footnote with the die: 1/6 + 1/6 = 1/3 and 1/6 + 1/4 = 5/12.
  - Section 5.3, the footnote: 0.9 if you are sure of what she said, 0.74 if you are 0.8 sure,
    and, with the same doubt at every level, values that go down toward 1/2: above 1/2 at every
    level, and below 1/2 + e from some level on, for every positive e.
  - Section 6.1, the gas stations: the manifesto's measure as a finite model (the coin and the
    three urns, sixteen points). Heads has 1/3 at a meeting at either station. With any
    proportion in the where urn, heads has 1/3 given a meeting. With one station's balls only
    in the where urn, two thirds of the meetings are at that station, with heads at 1/2 there
    and 0 at the other. With a 'meet' ball drawn with chance s, heads has s/(1 + s) at a meeting,
    at either station, which is 1/2 at s = 1.

Section 4.1 (OneBoxing.lean)
  What is stated and accepted:
  - Two boxes is a thousand more whatever the opaque box holds.
  - The arranger: the opaque box holds the million iff you act against what your rule
    recommends. Then, whatever is recommended, acting against it gets more than acting on it.
    A rule that takes the arrangement into account goes from one box to two and from two to
    one: it has no recommendation it can keep.
  - The two-boxer's rule compares the acts with the box as it is. Whatever was recommended and
    whatever the box holds, it gives two boxes, so it keeps its recommendation.
  - Gideon's paradox: if the prize is won exactly by an irrational choice, and a choice that
    wins is thereby not irrational, the prize is not won.
  - The mixture of the two rules: with the weight on the one-boxing rule halved again and
    again, the act settles after one halving at two thousand, two at four thousand, ten at a
    million (for any weight to start from above 0.512 and at most 1), and for every number of
    halvings there is a prize at which it has not settled.
  - With the opaque box empty, every chance of taking one box is a loss, and the one chance
    that loses nothing is 0.
  What is not stated, because it is not a calculation: that anyone who gives a reason to
  one-box follows a rule that takes the arrangement into account, and that the arranger can act
  on any rule whatever, a coin included. These are argued in the paper, section 4.1.

The cases (Cases.lean)
  Where the paper describes a case with chances, the case is built as a finite model, a list of
  points with weights, and the paper's values are derived on it. Each theorem quotes the
  sentence it states and names every choice made in stating it.
  - Sections 1 and 2 on the model of Appendix B, and (B2) as sets.
  - Section 3: the two guesses; Jack and Jill, with your measure in each cell equal to the
    recording's conditional for every event of the experiment; Gilad's room and box, at the
    even urn and at any urn.
  - Section 4: the worth of the ticket to each side at any price, and EDT's price per run.
  - Section 5: the peanut butter (an event independent of the ratio splits E into two cells
    with the same ratio); the dice; Amina's recording at 0.9; (J) at u = 0; two items taken in
    opposite orders, where (J) can give two values and conditioning gives one; the noisy signal
    and the reliable device; the sum for heads in Amina's case, and its two values at u = 1.
  - Section 6.1: the gas stations with every urn as a parameter: the owner who moves the where
    urn, the altruist, both urns his and the eighth of all the customers, the whether urn, and
    the second before you pull in.
  - Section 7: Sleeping Beauty on Sunday at any urn; the measure (15) on the six points; the
    measure with the four quarters; double halfing; outsiders in the reference class; the
    Doomsday factor and its limit; the bets of section 7.4; the Monday clock-time prior.
  - Section 8: the pairs of runs at any bias; which pair is the coin; a rule's cell
    probabilities at an uneven urn; the Wednesday case at every urn, and the 3/7 that a
    self-sampling rule gives there; the arithmetic of the ur-prior rules; the reference-class
    case; the lemma's cells at every urn.
  - Section 9: tag-swapped driving (1/4, 1/8, the prize at 1/3 given either sign); Monday balls
    only and the driver's coin, 1/(1+p); the payoffs at the intersection and of a coin chosen in
    advance, for the paper's payoffs and for any payoffs; the division that gives the first
    intersection (2-p)/2; the urn on the clock-times; the planner's two events.
  - Section 10.1: the train at even odds and at any price of the third ticket, and its cell
    values as the lemma's ratios.
  Not stated: two footnotes that appeal to the law of large numbers, a sum over infinitely many
  cells (the measures here are finitely additive), and sentences that are arguments and not
  calculations.
