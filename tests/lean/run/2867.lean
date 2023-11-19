/-!
  # Simp support for numerals and `OfNat`

  TODO: desc -/


-- set_option trace.Meta.Tactic.simp.discr true
-- set_option trace.Meta.DiscrTree true

namespace Test

-- # Numerals of type `Nat`

namespace Nat

-- Test equalities where the numeral is the root expression and ones where it's nested.
def rhs : Nat := sorry
theorem zero_eq : 0 = rhs := sorry -- `0` expands to `OfNat.ofNat (nat_lit 0)`
theorem one_eq : 1 = rhs := sorry -- `1` expands to `OfNat.ofNat (nat_lit 1)`
theorem ofNat_eq (n : Nat) : OfNat.ofNat n = rhs := sorry

def f : Nat → Nat := sorry
theorem f_zero_eq : f 0 = rhs := sorry
theorem f_one_eq : f 1 = rhs := sorry
theorem f_ofNat_eq (n : Nat) : f (OfNat.ofNat n) = rhs := sorry

example : 0 = rhs := by simp only [zero_eq]
example : f 0 = rhs := by simp only [f_zero_eq]
example : 1 = rhs := by simp only [one_eq]
example : f 1 = rhs := by simp only [f_one_eq]
example : 0 = rhs := by simp only [ofNat_eq]
example : f 0 = rhs := by simp only [f_ofNat_eq]
example : 1 = rhs := by simp only [ofNat_eq]
example : f 1 = rhs := by simp only [f_ofNat_eq]
example (n : Nat) : OfNat.ofNat n = rhs := by simp only [ofNat_eq]
example (n : Nat) : f (OfNat.ofNat n) = rhs := by simp only [f_ofNat_eq]

-- Apply a general lemma about nat literals to a specific nat literal.
-- This is the primary use case for collapsing nested `OfNat.ofNat` in lemmas.
example : 1 = rhs := by simp only [ofNat_eq 1] -- `ofNat_eq 1 : OfNat.ofNat (OfNat.ofNat (nat_lit 0)) = rhs`
example : f 1 = rhs := by simp only [f_ofNat_eq 1]

theorem ofNat_eq_iff (n : Nat) : OfNat.ofNat n = rhs ↔ f (OfNat.ofNat n) = rhs := sorry
theorem f_ofNat_eq_ofNat (n : Nat) : f (OfNat.ofNat n) = OfNat.ofNat n := sorry

-- Apply an equation with a nat literal variable on both sides to a specific nat literal.
-- This is the primary use case for collapsing nested `OfNat.ofNat` in the target.
example : 1 = rhs := by
  simp only [ofNat_eq_iff 1] -- `⊢ f (OfNat.ofNat (OfNat.ofNat (nat_lit 1))) = rhs`
  simp only [f_one_eq]
example : f 1 = rhs := by
  simp only [f_ofNat_eq_ofNat 1]
  simp only [one_eq]

-- In order to support the current desugaring of equation lemmas with pattern-matching on natural numbers,
-- we need unenclosed `nat_lit 0` to work in simp lemma statements.
theorem lit_zero_eq : nat_lit 0 = rhs := sorry
theorem f_lit_zero_eq : f (nat_lit 0) = rhs := sorry

example : 0 = rhs := by simp only [lit_zero_eq]
example : f 0 = rhs := by simp only [f_lit_zero_eq]

example : wellFounded 0 = 0 := by simp only [wellFounded]

theorem ofNat_succ_eq_iff (n : Nat) : OfNat.ofNat n.succ = rhs ↔ f (OfNat.ofNat n.succ) = rhs := sorry
theorem f_ofNat_succ (n : Nat) : f (OfNat.ofNat n.succ) = OfNat.ofNat n.succ := sorry

--
example : 1 = rhs := by
  simp only [ofNat_succ_eq_iff] -- `⊢ f (OfNat.ofNat (Nat.succ (OfNat.ofNat (nat_lit 0)))) = rhs`
  simp only [f_ofNat_eq]
example : f 1 = rhs := by
  simp only [f_ofNat_succ]
  simp only [ofNat_eq]

example : f (Nat.succ 0) = rhs := by simp only [f_ofNat_eq 1]
example : f (Nat.succ 0) = rhs := by simp only [f_ofNat_eq]

-- TODO: add tests for
-- - Nat.zero
-- - Nat.succ
-- - OfNat.ofNat into a custom semiring
-- - Nested all of the above
-- - Nat literals (with a note for the hack)
-- - OfNat.ofNat (OfNat.ofNat (nat_lit 0)) = (OfNat.ofNat (nat_lit 0))
--   - infinite loop?
--   - similar for (0.succ) = 1?
-- - Root vs non-root all of the above
-- - A lemma which forces a literal into Nat.succ via unification (simp only [n.succ < 2 ↔ n.succ = 1, 0.succ = 1])
-- - Additional dimension: Nat.zero in LHS vs in target
-- - Something which is reducibly defeq to Nat.zero
-- - Something which is semireducibly defeq to Nat.zero (should fail)
-- simp_arith
-- @OfNat.ofNat (ZMod <numeral>) <numeral> _
-- @OfNat.ofNat (ZMod (toNat (@OfNat.ofNat (ZMod <numeral>) <numeral> _) <numeral> _

-- `OfNat.ofNat n` applies to `0` in a nested context.
-- `OfNat.ofNat n` applies to `1` in a nested context.
-- `OfNat.ofNat n` applies to `Nat.zero` in a nested context.
-- `OfNat.ofNat n` applies to `Nat.succ Nat.zero` in a nested context.
-- `OfNat.ofNat (nat_lit 0)` applies to `Nat.zero` in a nested context
-- `Nat.zero` applies to `Nat.zero` in a nested context
-- `1` applies to `Nat.succ Nat.zero` in a nested context
-- `1` applies to `Nat.succ 0` in a nested context
-- `1` applies to `Nat.succ (nat_lit 0)` in a nested context
-- `1` applies to `Nat.succ (nat_lit 0)` in a nested context


-- ## Current behavior

theorem p_ofNat_ofNat (n : Nat) : P (OfNat.ofNat (OfNat.ofNat n)) := trivial
-- Currently, we collapse arbitrarily nested `OfNat` around a numeral into one.
example : P 0 := by simp only [p_ofNat_ofNat 0]
-- ...but we don't do any collapsing around a variable.
example : P 0 := by
  fail_if_success simp only [p_ofNat_ofNat]
  trivial

theorem p_nat_zero : P Nat.zero := trivial

example : P 0 := by simp only [p_nat_zero]
example : P Nat.zero := by simp only [p_zero]

theorem p_succ (n : Nat) : P (Nat.succ n) := trivial
-- Test `nat_lit` that appears outside of `OfNat`, even though that's generally not allowed.
theorem p_lit_zero : P (nat_lit 0) := trivial
theorem p_lit_one : P (nat_lit 1) := trivial

-- Currently, we allow simp lemmas about orphaned `nat_lit x` to apply to targets with
-- properly enclosed `OfNat.ofNat (nat_lit x)`. See test `bugNatLitDiscrTree.lean`.
example : P 0 := by simp only [p_lit_zero]

end Nat

-- # Numerals of type implementing `OfNat`

structure N where
  val : Nat

namespace N

instance instOfNat (n : Nat) : OfNat N n where
  ofNat := mk n



end N


theorem foo : P (Nat.succ 0) ↔ P 1 := sorry
theorem foo' : P (Nat.succ 0) ↔ P 1 := sorry

example : P (Nat.succ 0) := by
  simp (config := {memoize := false}) only [foo, foo']

theorem p_zero : P Nat.zero := test_sorry
theorem p_add_one (n : Nat) : P (HAdd.hAdd n 1) := test_sorry
-- theorem p_zero : P Nat.zero := test_sorry

example : P 0 := by simp only [p_zero]

-- DiscrTree key: [P, OfNat.ofNat, Nat, *, *]
theorem p_ofNat (n : Nat) : P (OfNat.ofNat n) := test_sorry

example : P 0 := by simp [p_ofNat] -- fails. should succeed
example (n : Nat) : P (OfNat.ofNat n) := by simp [p_ofNat] -- succeeds

-- DiscrTree key: [P, *]
theorem p_ofNat' (n : Nat) : P (no_index (OfNat.ofNat n)) := test_sorry
example : P 0 := by simp [p_ofNat'] -- succeeds

#check Nat.zero_eq

-- @[simp] theorem my_nat_add (n : Nat) : n + 0 = n := sorry
-- @[simp] theorem my_zero_add (n : Nat) : 0 + n = n := match n with
--   | 0 => sorry
--   | (n + 1) => sorry

set_option pp.all true in
#check my_nat_add

set_option pp.all true in
#check Nat.add_zero

#check Nat.zero_add

example : 0 = Nat.zero := by simp

example (n : Nat) : 0 + n = n := by simp

end Test
