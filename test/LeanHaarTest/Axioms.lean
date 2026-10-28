import LeanHaar

/-!
# Axiom guards for the main theorems

These guards catch changes to the axioms used by the main results. CI additionally audits every
library and test declaration, so an unrelated declaration cannot bypass the safety check.
-/

/-- info: 'SchurWeyl.schur_weyl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.schur_weyl

/-- info: 'SchurWeyl.weingarten_moment_haar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.weingarten_moment_haar

/-- info: 'k1_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms k1_moment

/-- info: 'k2_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms k2_moment

/-- info: 'SchurWeyl.K4.k4_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.K4.k4_moment
