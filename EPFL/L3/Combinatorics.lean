import Mathlib

-- # Combinatorics

-- Combinatorics is characterised by typically having
-- very few, very simple definitions...
-- But the proofs are difficult!

#check Set
#check Set ℕ
#check Finset
#check Finset ℕ

def ExampleFinset : Finset ℕ := {5, 1, 2, 0}

#eval ExampleFinset

def SecondFinset : Finset ℕ := {3, 1}

#eval ExampleFinset ∪ SecondFinset

example : SecondFinset = {1, 3} := by
  rw [SecondFinset, Finset.pair_comm]

example {x y : ℕ} : ({x, y} : Finset ℕ) = {y, x} := by
  rw [Finset.pair_comm]

#synth Union (Finset ℕ)           -- allows me to use ∪ on Finsets
#synth Inter (Finset ℕ)           -- allows me to use ∩ on Finsets
#synth Insert ℕ (Finset ℕ)        -- allows me to use insert
#synth EmptyCollection (Finset ℕ) -- allows me to use ∅
#synth HasSubset (Finset ℕ)       -- ⊆
#synth SDiff (Finset ℕ)           -- \
#synth Singleton ℕ (Finset ℕ)     -- {x}

#check Finset.biUnion             -- bounded indexed union
variable (s : Finset ℕ) (a : ℕ)
#check s.erase a              -- erase an element
#check Finset.image
#check Finset.filter
#check Finset.range
#check (· ⁻¹' ·)

#check Fintype

variable (α : Type) [Fintype α]
#check Fintype.card α
example (α : Type) [Fintype α] (x : α) : x ∈ Finset.univ := by simp

#check Finset.sum
#check Finset.prod

open BigOperators

#eval ∑ i in ExampleFinset, i ^ 2
#eval ExampleFinset

example : ∑ i in ExampleFinset, i ^ 2 = 30 := rfl

#check Finset.prod_insert
#check Finset.sum_insert

example {s : Finset ℝ} : 0 ≤ ∑ i in s, i ^ 2 := by
  apply?


-- ## Interactive!!

open Classical
open Finset

#check Finset.sum_const
#check Finset.sum_congr
#check Finset.sum_le_sum

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ (t.filter (r a ·)).card)
    (h_right : ∀ b ∈ t, (s.filter (r · b)).card = 1) :
    3 * s.card ≤ t.card :=
  sorry





theorem doubleCounting' {α β : Type*} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ (t.filter (r a ·)).card)
    (h_right : ∀ b ∈ t, (s.filter (r · b)).card = 1) :
    3 * s.card ≤ t.card := by
  suffices s.card * 3 ≤ t.card * 1 by linarith
  exact Finset.card_mul_le_card_mul r h_left (fun b hb => (h_right b hb).le)




lemma Nat.coprime_self_add_one (n : ℕ) :
    Nat.Coprime n (n + 1) := by simp

#check exists_lt_card_fiber_of_mul_lt_card_of_maps_to

example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y := by
  sorry

example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.Ioc 0 (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ x ∣ y := by
  sorry
