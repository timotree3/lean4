set_option trace.Elab.definition.wf.eqns true
set_option trace.Elab.definition.eqns true
set_option trace.Meta.Match.debug true
set_option trace.Elab.match true
set_option trace.Meta.Match.matchEqs true
set_option trace.Meta.Tactic.split true
set_option trace.Elab.definition true
set_option trace.Debug.Meta.Tactic.simp.congr true
set_option trace.Debug.Meta.Tactic.simp true
set_option trace.Meta.Tactic.simp.rewrite true

@[simp] def f' (n : Nat) : Option { r : Nat // r ≤ n } :=
  match n with
  | 0   => some ⟨0, Nat.le_refl _⟩
  | n+1 => match f' n with
    | some ⟨m, h₁⟩ =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      match f' m with
      | some ⟨r, h₂⟩ => some ⟨r, Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.le_succ _))⟩
      | none => none
    | none => none
-- set_option trace.Meta.Tactic.simp.discr true
-- set_option trace.Meta.DiscrTree true


@[simp] def nondep (n : Nat) : Option Nat :=
  match n with
  | 0   => some 0
  | n+1 => match nondep n with
    | some m =>
      have : m < n+1 := sorry
      match nondep m with
      | some r => some r
      | none => none
    | none => none

#check nondep._eq_1 -- nondep._eq_1 : nondep (OfNat.ofNat (nat_lit 0)) = ...`
#check f'._eq_1
#check f'._match_splitter

example : True := by
  simp

#check Lean.Meta.DSimp.Config

example : nat_lit 2 = OfNat.ofNat (nat_lit 2) := by
  dsimp (config := {
  zeta              := false
  beta              := false
  eta               := false
  iota              := false
  proj              := false
  decide            := false
  autoUnfold        := false}) only

example {β : Nat → Type u} (f : (n : Nat) → β n): f (nat_lit 2) = sorry := by
  dsimp (config := {
  zeta              := false
  beta              := false
  eta               := false
  iota              := false
  proj              := false
  decide            := false
  autoUnfold        := false}) only

-- #check fun n => match n with | 2 => 3| n + 2 => 2 | 0 => 1

@[simp] def wellFounded (n : Nat): { r : Nat // r = n } :=
  match n with
  | 0 => ⟨0, rfl⟩
  | n + 1 =>
    let _ := wellFounded (id n)
    ⟨n + 1, rfl⟩

#check wellFounded._eq_1
#reduce 0

@[simp] def dependent (n : Nat): { r : Nat // r = n } :=
  match n with
  | 0 => ⟨0, rfl⟩
  | m + 1 => ⟨m + 1, rfl⟩

#check dependent._eq_1

-- example (n : Nat) : wellFounded n = ⟨n, rfl⟩ := by
--   delta wellFounded
--   split

-- @[simp] def wellFounded' (n : Nat) : Nat :=
--   match n with
--   | 0 => 0
--   | n + 1 =>
--     match wellFounded' (0 + n) with
--     | 0 => n + 1
--     | _ + 1 => n + 1

-- #reduce wellFounded'


example : wellFounded' n = n := by
  simp only [wellFounded']


@[match_pattern] def K : Nat → Nat → Nat := fun n _ => n
#check fun n => match n with  | n + 1 => 2 | K 0 y => y


theorem f'_ne_none (n : Nat) : f' n ≠ none := by
  match n with
  | 0   => simp (config := { decide := false }) only [f']; simp
  | n+1 =>
    simp [f']
    have ih₁ := f'_ne_none n
    split
    next m h₁ he =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      have ih₂ := f'_ne_none m
      split
      next => simp
      next h => contradiction
    next => contradiction
