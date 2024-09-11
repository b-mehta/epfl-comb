import Mathlib

open Real

-- # Intro
-- Lean is a dependently-typed language

-- Every expression has a type, and `#check` can tell you the type

#check 2
#check 17 + 4
#check π
#check rexp 1

-- Types are expressions too!

#check ℕ
#check ℝ

-- We can also make our own expressions, and give them names
def myFavouriteNumber : ℕ := 7

def yourFavouriteNumber : ℕ := 2
-- sorry works as a placeholder

#check myFavouriteNumber

-- or not give them a name
example : ℕ := 2

-- # But this isn't maths!

-- The type `Prop` contains `Prop`ositions...

#check 2 + 2 = 4
#check rexp 1 < π

-- ...including false propositions...
#check 2 + 2 = 5
-- ...and open questions
#check Irrational (rexp 1 + π)
#check myFavouriteNumber = yourFavouriteNumber

def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p

-- Key! If `p : Prop`, an expression of type `p` is a proof of `p`.

example : 2 + 2 = 4 := rfl
example : 2 + 2 ≠ 5 := by simp
example : ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry
-- Erdős-Strauss conjecture

example (n : ℕ) (hn : 2 ≤ n) :
  ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry

-- # How can we make these expressions?

-- Simple proof terms
example : True := trivial
example : 2 = 2 := rfl
example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem my_proof : MyVeryEasyProposition := fun n => ⟨n, le_rfl⟩

#check MyVeryEasyProposition
#check my_proof
-- my proposition "has type Proposition", or "is a proposition"
-- my proof "has type my proposition", or "has type ∀ n : ℕ, ∃ p, n ≤ p",
--    or "is a proof of ∀ n : ℕ, ∃ p, n ≤ p"

-- But just proof terms get ugly...
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))



-- Very clever tactics
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring

example : 2 + 2 ≠ 5 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

open Nat

-- Simple tactics
example (a b : ℝ) : a + b = b + a := by exact add_comm a b
example : 3 = 3 := by rfl

#check add_mul (R := ℕ)

-- In practice we write tactic proofs, and write them with help of the infoview
example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [add_mul b 1 a, one_mul a, add_comm a (a * b), mul_comm a b]
  --> S01_Calculating.lean has many examples and some more information about using `rw`

open Nat

theorem Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  have hn : n ! ≠ 0 := by exact factorial_ne_zero n
  have f1 : n ! + 1 ≠ 1 := by simp [hn]
  have pp : Nat.Prime p := by exact minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h ↦ by
      have h₁ : p ∣ factorial n := by exact (Prime.dvd_factorial pp).mpr h
      have h₂ : p ∣ 1 := by
        refine (Nat.dvd_add_iff_right h₁).mpr ?_
        exact minFac_dvd (n ! + 1)
      rw [@dvd_one] at h₂
      simp_all only [ne_eq, add_left_eq_self, not_false_eq_true, ge_iff_le, minFac_eq_one_iff, p]
  exact ⟨p, np, pp⟩

theorem Ugly_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  have pp := minFac_prime (add_left_ne_self.2 (factorial_pos n).ne')
  ⟨_, le_of_not_le fun h ↦ pp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_factorial pp.pos h)).2
    (minFac_dvd _)), pp⟩

-- The proof doesn't matter
example : Euclid_Thm = Ugly_Euclid_Thm := rfl
-- *to Lean*

noncomputable def minFac' (n : ℕ) : ℕ :=
  sInf {p : ℕ | p ∣ n ∧ Nat.Prime p}

lemma minFac'_one : minFac' 1 = 0 := by
  rw [minFac']
  simp
  aesop

  --> S02_Inequalities.lean has more examples of tactic proofs

-- Some tactics can self-replace
theorem Easy_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by exact Euclid_Thm n

example (a b c : ℕ) : a * b * c = a * c * b := by
  ring

  -- rw [Nat.right_distrib]
  -- rw [Nat.one_mul]
  -- rw [Nat.add_comm]
  -- rw [Nat.mul_comm]


/- ###  λ notation:
In Lean, functions are defined using `fun` expressions:
`fun x ↦ f x` is a function that maps `x` to `f (x)`
-/

def α : ℕ → ℕ := fun n ↦ n ^ 2 + 3
def α' (n : ℕ) : ℕ := n^2 + 3 -- `f(n) = n^2 + 3`

-- We can also use the keyword `λ` instead of `fun`

def α'' : ℕ → ℕ := λ n ↦ n^2 + 3

example : α 3 = 12 := by
  -- rw [α]
  norm_num

-- # Some more difficult proofs
def myFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

#eval 3 / 0 * 0

#check myFactorial

-- Lean can compute too!
-- #eval myFactorial 10
-- sometimes useful for sanity-checking definitions

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [myFactorial_add_one]
    positivity

-- Follow-up about the definition of `minFac`!

-- # Personal note: this scales!

noncomputable def upper_density (A : Set ℕ) : ℝ := 0

theorem bloom (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ B : Finset ℕ, B.toSet ⊆ A ∧ ∑ i in B, (1 / i : ℚ) = 1 := by
  rw [upper_density] at hA
  aesop

def diagonal_ramsey (k : ℕ) : ℕ :=
  sorry

theorem campos_griffiths_morris_sahasrabudhe :
    ∃ c : ℝ, 0 < c ∧ ∀ k, diagonal_ramsey k ≤ (4 - c) ^ k := by
  aesop

-- Expressions and types, every expression has a type
-- A proof has type given by what it's proved!

-- Useful tactics:
  -- rw
  -- exact
  -- apply
  -- simp
  -- induction
  -- have

  -- ring, norm_num, positivity, linarith
  -- refine

  -- calc

example (n : Finset ℕ) : Set ℝ := (n : Set ℕ)

-- # Footnotes

-- ## Dependently typed
#check Fin 10
#check Fin

example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## terminal simps
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?

-- ## naming
-- https://leanprover-community.github.io/contribute/naming.html

-- ## hierarchy!
#check 3
#check ℕ
#check 4 = 4
#check Prop
#check Type
#check Type 1
#check Type 2

#check Type 0

-- myproof : myVeryEasyProposition : Prop : Type : Type 1 : Type 2 : Type 3 : ...
