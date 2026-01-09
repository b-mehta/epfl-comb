import Mathlib

variable {V : Type*} {B : V → V → ℂ}

open Classical SimpleGraph

def GreenGraph (B : V → V → ℂ) (hB : ∀ i j, B i j = - B j i) :
    SimpleGraph V where
  Adj i j := B i j ≠ 0 ∧ ∀ k, k ≠ i → k ≠ j → ∃ n : ℕ, (B j k + B k i) / B i j = n
  loopless i := by
    dsimp
    have := hB i i
    rw [CharZero.eq_neg_self_iff] at this
    simp [this]
  symm := by
    intro i j ⟨h₁, h₂⟩
    rw [hB]
    simp only [ne_eq, neg_eq_zero]
    refine ⟨h₁, ?_⟩
    intro k hkj hki
    obtain ⟨n, hn⟩ := h₂ k hki hkj
    use n
    rw [hB i k, hB k j, ← neg_add_rev, neg_div_neg_eq, hn]

lemma greenGraph_adj (hB : ∀ i j, B i j = - B j i) {i j : V} :
    (GreenGraph B hB).Adj i j ↔ B i j ≠ 0 ∧ ∀ k, k ≠ i → k ≠ j →
      ∃ n : ℕ, (B j k + B k i) / B i j = n := Iff.rfl

lemma ne_zero_of_greenGraph_adj (hB) {i j} (h : (GreenGraph B hB).Adj i j) :
  B i j ≠ 0 := h.1

lemma triple_sum_ne_zero (hB) {i j k : V} (hik : i ≠ k) (hjk : j ≠ k)
    (hij : (GreenGraph B hB).Adj i j) :
    B i j + B j k + B k i ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := hij.2 k hik.symm hjk.symm
  rw [div_eq_iff hij.1] at hq
  rw [add_assoc, hq] at h
  rw [← one_add_mul] at h
  simp only [mul_eq_zero] at h
  simp only [hij.1, or_false] at h
  norm_cast at h
  simp at h

lemma lem_3point1_part2 (hB) {i j k : V} (hik : i ≠ k)
    (hij : (GreenGraph B hB).Adj i j)
    (hjk : (GreenGraph B hB).Adj j k) :
    ∃ q : ℚ, q > 0 ∧ B j k * q = B i j := by
  obtain ⟨p, hp⟩ := hij.2 k hik.symm hjk.ne'
  obtain ⟨q, hq⟩ := hjk.2 i hij.ne hik
  use (1 + q) / (1 + p)
  constructor
  · positivity
  · push_cast
    rw [mul_div_assoc', div_eq_iff, ← hp, ← hq]
    · field_simp [hjk.1, hij.1]
      ring
    rw [add_comm, ← Nat.cast_add_one, Nat.cast_ne_zero]
    simp

lemma lem_3point1_part1 (hB) {j k₁ k₂ k₃ : V}
    (h₁₂ : k₁ ≠ k₂)
    (h₁₃ : k₁ ≠ k₃)
    (h₂₃ : k₂ ≠ k₃)
    (hk₁ : (GreenGraph B hB).Adj j k₁)
    (hk₂ : (GreenGraph B hB).Adj j k₂)
    (hk₃ : (GreenGraph B hB).Adj j k₃) :
    False := by
  obtain ⟨q₁₂, hq₁₂, hq₁₂k⟩ := lem_3point1_part2 hB h₁₂ hk₁.symm hk₂
  obtain ⟨q₂₃, hq₂₃, hq₂₃k⟩ := lem_3point1_part2 hB h₂₃ hk₂.symm hk₃
  obtain ⟨q₁₃, hq₁₃, hq₁₃k⟩ := lem_3point1_part2 hB h₁₃ hk₁.symm hk₃
  rw [hB, ← hq₂₃k, ← hq₁₃k, neg_mul, mul_assoc, neg_eq_iff_add_eq_zero, ← mul_add,
    mul_eq_zero, or_iff_right hk₃.1] at hq₁₂k
  norm_cast at hq₁₂k
  nlinarith

variable [Fintype V]

lemma bounded_degree (hB) {j : V} : (GreenGraph B hB).degree j ≤ 2 := by
  rw [← card_neighborFinset_eq_degree, ← not_lt, Finset.two_lt_card]
  simp only [mem_neighborFinset, ne_eq, not_exists, not_and, Decidable.not_not]
  intro k₁ hk₁ k₂ hk₂ k₃ hk₃ h₁₂ h₁₃
  by_contra!
  exact lem_3point1_part1 hB h₁₂ h₁₃ this hk₁ hk₂ hk₃
