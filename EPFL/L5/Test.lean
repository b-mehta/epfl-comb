import Mathlib

open Pointwise

open Classical FiniteDimensional Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable def realRank (A : Finset V) : ℕ :=
    finrank ℝ (span ℝ A.toSet)

lemma realRank_insert_mem_span {A : Finset V} (a : V) (h : a ∈ span ℝ A.toSet) :
    realRank (insert a A) = realRank A := by
  simp only [realRank]
  have : span ℝ (insert a A).toSet = span ℝ A.toSet := by
    simp only [Finset.coe_insert]
    exact span_insert_eq_span h
  rw [finrank_eq_of_rank_eq]
  simp only [finrank_eq_rank]
  rw [this]

variable [FiniteDimensional ℝ V]

lemma realRank_insert_not_mem_span {A : Finset V} (a : V) (h : a ∉ span ℝ A.toSet) :
    realRank (insert a A) = realRank A + 1 := by
  sorry

@[simp] lemma realRank_empty : realRank (∅ : Finset V) = 0 := by
  sorry

#check Finset.card_le_card_mul_left
#check Finset.card_le_card_add_left

lemma Finset.card_le_card_add_self {α : Type*} [Add α] [IsLeftCancelAdd α] [DecidableEq α]
    {A : Finset α} : A.card ≤ (A + A).card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  case inl => simp
  case inr => exact Finset.card_le_card_add_left _ hA

#check convexHull

theorem myProof {n d : ℕ} {A : Finset (Fin n → ℝ)} (hA : realRank A = d) :
    (d + 1) * A.card - (d + 1).choose 2 ≤ (A + A).card := by
  induction d
  case zero =>
    simp only [zero_add, one_mul, Nat.choose_succ_self, tsub_zero]
    exact Finset.card_le_card_add_self
  case succ d ih =>

    obtain ⟨x, hx⟩ : ((convexHull ℝ A.toSet).extremePoints ℝ).Nonempty := by
      refine IsCompact.extremePoints_nonempty ?_ ?_
      · refine Set.Finite.isCompact_convexHull ?_
        exact Finset.finite_toSet A
      · simp only [convexHull_nonempty_iff, Finset.coe_nonempty]
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hA
    sorry
