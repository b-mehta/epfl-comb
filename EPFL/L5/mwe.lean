import Mathlib

variable {α : Type*} [DecidableEq α]

def containsSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ T ⊆ F, T.card = r ∧ ∃ K : Finset α, T.toSet.Pairwise fun X Y => X ∩ Y = K

-- TODO: make subset_image_iff about finsets
theorem containsSunflower_of_image_image {r : ℕ} {β : Type*} [DecidableEq β]
    {F : Finset (Finset α)} {f : α → β} (hf : Set.InjOn f (F.biUnion id)) :
    containsSunflower (F.image (Finset.image f)) r → containsSunflower F r := by
  rintro ⟨G, hG₁, hGr, hG₂⟩
  have : G.toSet ⊆ Finset.image f '' F := by
    rw [←Finset.coe_image, Finset.coe_subset]
    exact hG₁
  rw [Finset.subset_image_iff] at this
  obtain ⟨G', hG', rfl⟩ := this
  have : G'.biUnion id ⊆ F.biUnion id := by exact Finset.biUnion_subset_biUnion_of_subset_left hG' id

example : 1 = 2 := by rfl
