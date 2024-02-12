/-!
  # Normalizing nat literals in `simp` and `dsimp`

  `dsimp only` will now (and `simp only` already does) normalize all occurences of raw nat literals
  (`nat_lit n`) into `@OfNat.ofNat Nat (nat_lit n) instOfNatNat`. This is generally the expected
  form for nat literals and is particularly important for `simp` to produce in contexts where
  `simp` is used to determine the statement of a theorem, because we don't want raw `nat_lit` in our
  theorem statements.

  There is some subtlety here, because there is one case where we do not want to convert
  `nat_lit n` into `@OfNat.ofNat Nat (nat_lit n) instOfNatNat`, namely, when it occurs as the
  second argument of an `OfNat.ofNat` invocation already. A naïve solution would have `simp` simply
  skip arguments of `OfNat.ofNat`, but a more principled solution would still simplify the first and
  third arguments (and even the second argument if it is a more complicated expression than `nat_lit n`)-/

-- Show `OfNat.ofNat` in infoview when present for clarity
set_option pp.coercions false

def P (_ : α) : Prop := True

/-- Raw nat literals have the same simp-normal form as `OfNat.ofNat` literals.

  Note: Testing `nat_lit 2 = 2` would be useless because `simp` tries `rfl`.
  Therefore, to avoid solving by defeq, all goals should be `Iff`s.
  Note: There is no test for `dsimp` because it does not close `Iff` goals. -/
example : P (nat_lit 2) ↔ P 2 := by
  simp only

/-- Raw nat literals should NOT be in simp-normal form.-/
example : P (nat_lit 2) := by
  simp (config := {failIfUnchanged := true}) only
  trivial
example : P (nat_lit 2) := by
  dsimp (config := {failIfUnchanged := true}) only
  trivial

/-- `OfNat.ofNat` literals should be in simp-normal form.-/
example : P 2 := by
  fail_if_success simp (config := {failIfUnchanged := true})
  trivial
example : P 2 := by
  fail_if_success dsimp (config := {failIfUnchanged := true})
  trivial

/-- Raw nat literals should also get simplified in positions where they have forward dependencies
    (and therefore only defeq simplifications are safe to perform). -/
example (α : Nat → Type) (f : (n : Nat) → α n) : P (f (nat_lit 2)) ↔ P (f 2) := by
  simp only

-- We're about to test that type and instance arguments get simplified
set_option pp.explicit true
set_option pp.coercions false

/-- Term equivalent of `sorry` which avoids warnings in the expected test output. -/
axiom testSorry {α : Sort _} : α

example (n : Nat) : P (default : Fin ((n * 0 + n + n) + 1)) := by
  simp only [←Nat.mul_succ]
  exact testSorry

example (n : Nat) : P (@default (Fin ((n * 0 + n + n) + 1))
    (@Fin.instInhabitedFinHAddNatInstHAddInstAddNatOfNat (n * 2))) := by
  simp only [←Nat.mul_succ]
  exact testSorry

example (n : Nat) : P (@default (Fin ((n * 2) + 1))
    (@Fin.instInhabitedFinHAddNatInstHAddInstAddNatOfNat (n * 0 + n + n))) := by
  simp only [←Nat.mul_succ]
  exact testSorry

example : P (@OfNat.ofNat (Fin (n + 0 + 1)) (nat_lit 2) (@Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat n (nat_lit 2))) := by
  simp only [Nat.add_zero]
  trace_state
  exact testSorry

example : P (@OfNat.ofNat (Fin (Nat.succ (n + 0))) (nat_lit 2) _) := by
  dsimp only
  trace_state
  exact testSorry

example : P (Fin (n + 0)) := by
  dsimp only

-- example (n : Nat) : n + 0 = sorry := by
--   simp

-- example (n : Nat) : (OfNat.ofNat (2 + 0)) = sorry := by
--   simp
/- Key ingredients:
  - Well-founded recursion (so equation lemmas are even generated)
  - Matching on a nat literal pattern (`0` below)
  - The conclusion type depends on the nat discriminant (so `dsimp` is used instead of `simp`)
  -/
@[simp] def wellFounded (n : Nat) : { r : Nat // r = n } :=
  match n with
  | 0 => ⟨0, rfl⟩
  | n + 1 =>
    let _ := wellFounded (id n)
    ⟨n + 1, rfl⟩

#check wellFounded._eq_1
