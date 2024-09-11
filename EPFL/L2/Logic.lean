import Mathlib

-- This file is adapted from Lean for the Curious Mathematician 2023
-- Thanks to Jakob von Raumer

/-
# Logics

* Get used to being precise about logical connective, phrases like "to prove
  `A ∧ B` we have to prove `A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...           implication
∀   \all    for all                   universal quantification
∃   \ex     there exists              existential quantification
¬   \not    not                       negation
∧   \and    and                       conjunction
∨   \or     or                        disjunction
↔   \iff    ... if and only iff ...   biimplication
False       contradiction!            falsity
True        this is trivial           truth

... and how to use them:

            appearing as hypothesis `h`                appearing as goal
`A → B`     `have h' := h ha`, `apply h`               `intro ha`
`∀ x, P x`  `have h' := h x`, `apply h`,               `intro x`

`A ∧ B`     `obtain ⟨ha, hb⟩ := h`, `h.1`, `h.2`       `constructor`
`A ∨ B`     `obtain (h₁ | h₂) := h`                    `left` or `right`
`∃ x. P x`  `obtain ⟨x, hx⟩ := h`                      `constructor` or `use x`

`False`     `contradiction`                            --
`True`      --                                         `trivial`

`¬ A`       `contradiction`, `apply h`                 `intro ha`
`A ↔ B`     `obtain ⟨h₁, h₂⟩ := h`, `h.1`, `h.2`       `constructor`

* `by_contra` for proofs by contradiction
* Note that logical connectives can be hidden under other definitions:
  `a ∣ b` is existential, `s ⊆ t` is universal.
-/

/-!
## Implication and universal quantifiers
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

section

variable (a b c d : ℝ)
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check @my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end

def isUpperBoundedBy (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

-- Demonstrate use of `apply`, `have`, `specialize`, `dsimp`, `simp`, proof structuring
-- Also show `have`
theorem isUpperBoundedBy_add {f g a b} (hfa : isUpperBoundedBy f a) (hgb : isUpperBoundedBy g b) :
    isUpperBoundedBy (f + g) (a + b) := by
  simp only [isUpperBoundedBy] at hfa hgb ⊢
  intro x
  simp?
  have hfa' := hfa x
  specialize hgb x
  linarith


end

/-!
## The existential quantifier
-/

-- Demonstrate `use`, `refine` and `norm_num`, explain how to know that it is existential

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.4
  norm_num

example : 5 ∣ 20 := by
  use 4  -- Automatically closes trivial goals!

-- Demonstrate `rcases` and `obtain` on existential quantifiers

section

def upperBounded (f : ℝ → ℝ) := ∃ a, isUpperBoundedBy f a

example {f g} (ubf : upperBounded f) (ubg : upperBounded g) : upperBounded (f + g) := by
  simp only [upperBounded] at *
  obtain ⟨a, ha⟩ := ubf
  obtain ⟨b, hb⟩ := ubg
  use a + b
  exact isUpperBoundedBy_add ha hb

end

/-
The existential quantifier in Lean comes with an axiom called *global choice*.
It provides a witness for all proofs of existentially quantified statements and
guarantees that the witness is the same if we deconstruct the same statement twice.
-/
#check Exists.choose
#check Exists.choose_spec

theorem nat_exists : ∃ (x : ℕ), 4 < x := by sorry

noncomputable def chooseNat : ℕ := by
  exact Exists.choose nat_exists

/-!
## Negation

`¬ A` is an abbreviation for `A → False`.
-/

section

variable {f : ℝ → ℝ}

-- Demonstrate `rintro`

example (h : ∀ a, ∃ x, a < f x) : ¬ upperBounded f := by
  simp only [upperBounded]
  rintro ⟨a, ha⟩
  specialize h a
  obtain ⟨b, hb⟩ := h
  simp only [isUpperBoundedBy] at *
  specialize ha b
  rw [← not_lt] at ha
  contradiction


-- Repeat with demonstration of `simp`, `simp only`, `push_neg`

example (h : ∀ a, ∃ x, a < f x) : ¬ upperBounded f := by
  simp only [upperBounded, isUpperBoundedBy]
  push_neg
  assumption

end

/-!
## Conjuction
-/

section

variable {x y : ℝ}

-- Demonstrate `constructor`, `linarith`, `subst`, `contradiction`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  case left => assumption
  case right => linarith

-- Demonstrate `rcases`, `.1`,

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  --rcases h with ⟨h₁, h₂⟩
  simp only [Not]
  intro h₃
  apply h.2
  exact antisymm h.1 h₃

end

/-!
## Disjunction
-/

section

variable (x y z : ℝ)

-- Demonstrate `exact?`, `by_cases`, `left`, `right`, `rwa`

#check abs_of_nonneg
#check abs_of_neg

example : x < |y| → x < y ∨ x < -y := by
  intro h
  by_cases hy : y < 0
  · right
    rwa [abs_of_neg hy] at h
  · left
    rw [not_lt] at hy
    rwa [abs_of_nonneg hy] at h

end




















/-!
## More exercises
-/

section

variable (p q : Prop) -- Propositions
variable (r s : ℕ → Prop)  -- Predicates over the natural numbers

example : p ∧ q → q ∧ p := by
  sorry

example : p ∨ q → q ∨ p := by
  sorry

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) := by
  sorry

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z := by
  sorry

example : ¬¬(¬¬p → p) := by
  sorry

example : ∃ x, r x → ∀ y, r y := by
  by_cases ∀ y, r y
  case pos h =>
    simp [h]
  case neg h =>
    push_neg at h
    obtain ⟨i, hi⟩ := h
    use i
    simp [hi]

end
