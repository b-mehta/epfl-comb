import Mathlib

variable {α β : Type*}

namespace Finset

lemma disjSum_inj {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    s₁.disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [Finset.ext_iff]

lemma Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β) :=
  fun _ _ _ _ => by simp [Finset.ext_iff]

def toLeft (s : Finset (α ⊕ β)) : Finset α :=
  s.disjiUnion (Sum.elim singleton (fun _ => ∅)) <|
    fun x hx y hy h => by aesop (add simp Function.onFun)

def toRight (s : Finset (α ⊕ β)) : Finset β :=
  s.disjiUnion (Sum.elim (fun _ => ∅) singleton) <|
    fun x hx y hy h => by aesop (add simp Function.onFun)

@[simp] lemma mem_toLeft {s : Finset (α ⊕ β)} {x : α} : x ∈ s.toLeft ↔ .inl x ∈ s := by
  simp [toLeft]

@[simp] lemma mem_toRight {s : Finset (α ⊕ β)} {x : β} : x ∈ s.toRight ↔ .inr x ∈ s := by
  simp [toRight]

@[gcongr]
lemma toLeft_subset_toLeft {s t : Finset (α ⊕ β)} : s ⊆ t → s.toLeft ⊆ t.toLeft :=
  fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]
lemma toRight_subset_toRight {s t : Finset (α ⊕ β)} : s ⊆ t → s.toRight ⊆ t.toRight :=
  fun h _ => by simpa only [mem_toRight] using @h _

lemma toLeft_monotone : Monotone (@toLeft α β) := fun _ _ => toLeft_subset_toLeft
lemma toRight_monotone : Monotone (@toRight α β) := fun _ _ => toRight_subset_toRight

lemma toLeft_disjSum_toRight {s : Finset (α ⊕ β)} : s.toLeft.disjSum s.toRight = s := by
  ext (x | x) <;> simp

lemma toLeft_inter [DecidableEq α] [DecidableEq β] {s t : Finset (α ⊕ β)} :
    (s ∩ t).toLeft = s.toLeft ∩ t.toLeft := by ext x; simp

lemma toRight_inter [DecidableEq α] [DecidableEq β] {s t : Finset (α ⊕ β)} :
    (s ∩ t).toRight = s.toRight ∩ t.toRight := by ext x; simp

lemma card_toLeft_add_card_toRight {s : Finset (α ⊕ β)} :
    s.toLeft.card + s.toRight.card = s.card := by
  rw [← card_disjSum, toLeft_disjSum_toRight]

lemma card_toLeft_le {s : Finset (α ⊕ β)} : s.toLeft.card ≤ s.card := by
  rw [← card_toLeft_add_card_toRight]
  exact Nat.le_add_right _ _

lemma card_toRight_le {s : Finset (α ⊕ β)} : s.toRight.card ≤ s.card := by
  rw [← card_toLeft_add_card_toRight]
  exact Nat.le_add_left _ _

@[simp] lemma disjSum_toLeft {s : Finset α} {t : Finset β} : (s.disjSum t).toLeft = s := by
  ext x; simp

@[simp] lemma disjSum_toRight {s : Finset α} {t : Finset β} : (s.disjSum t).toRight = t := by
  ext x; simp

lemma disjSum_eq_iff {s : Finset α} {t : Finset β} {u : Finset (α ⊕ β)} :
    s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight :=
  ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

end Finset

variable [DecidableEq α] {F : Finset (Finset α)} {K : Finset α}

open Finset
open scoped Nat


@[simp]
lemma mem_inf' {α β : Type*} [DecidableEq β]
    {f : α → Finset β} {S : Finset α} (hS : S.Nonempty) {x : β} :
    x ∈ S.inf' hS f ↔ ∀ s ∈ S, x ∈ f s := by
  induction hS using Nonempty.cons_induction <;> simp_all

-- in #16823
theorem Set.Nontrivial.image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (hs : s.Nontrivial)
    (hf : s.InjOn f) :
    (f '' s).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, Set.mem_image_of_mem _ hx, f y, Set.mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

-- in #16823
@[simp]
theorem image_nontrivial_iff_of_injOn {α β : Type*} {f : α → β} {s : Set α} (hf : s.InjOn f) :
    (f '' s).Nontrivial ↔ s.Nontrivial :=
  sorry

lemma image_subset_image_iff_of_injOn {α β : Type*} [DecidableEq β] {f : α → β} {s₁ s₂ s : Finset α}
    (ht : (s : Set α).InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    s₁.image f ⊆ s₂.image f ↔ s₁ ⊆ s₂ := by
  simpa [←Finset.coe_subset] using ht.image_subset_image_iff h₁ h₂

lemma image_eq_image_iff {α β : Type*} [DecidableEq β] {f : α → β} {s₁ s₂ s : Finset α}
    (ht : (s : Set α).InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    s₁.image f = s₂.image f ↔ s₁ = s₂ := by
  simpa [←Finset.coe_inj] using ht.image_eq_image_iff h₁ h₂

theorem injOn_image {β : Type*} [DecidableEq β] {S : Finset (Finset α)} {f : α → β}
    (hf : Set.InjOn f (S.biUnion id)) :
    (S : Set (Finset α)).InjOn (image f) := by
  intro x hx y hy h
  rwa [← image_eq_image_iff hf]
  case h₁ => exact subset_biUnion_of_mem id hx
  case h₂ => exact subset_biUnion_of_mem id hy

theorem nontrivial_of_image {f : β → α} {S : Finset β} (h : (S.image f).Nontrivial) :
    S.Nontrivial := by
  simp only [Finset.Nontrivial, coe_image] at h ⊢
  exact Set.nontrivial_of_image _ _ h

theorem Nontrivial.image_of_injOn {f : β → α} {S : Finset β} (h : Set.InjOn f S) (h : S.Nontrivial) :
    (S.image f).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, h.ne hx hy hxy⟩

lemma strictMono_range : StrictMono range := strictMono_nat_of_lt_succ (by simp [ssubset_def])

section hasKernel

def hasKernel (S : Finset (Finset α)) (K : Finset α) : Prop :=
  S.toSet.Pairwise fun X Y => X ∩ Y = K

@[simp] lemma hasKernel_not_nontrivial (hF : ¬F.Nontrivial) {K : Finset α} :
    hasKernel F K := by
  have : F.toSet.Subsingleton := by simpa only [Set.not_nontrivial_iff] using hF
  exact this.pairwise _

@[simp] lemma singleton_hasKernel {s : Finset α} {K : Finset α} : hasKernel {s} K :=
  hasKernel_not_nontrivial (by simp)

@[simp] lemma empty_hasKernel {K : Finset α} : hasKernel ∅ K :=
  hasKernel_not_nontrivial (by simp)

lemma hasKernel.subset (hF : F.Nontrivial) {K : Finset α}
    (h : hasKernel F K) {s : Finset α} (hs : s ∈ F) : K ⊆ s := by
  obtain ⟨t, ht, ht'⟩ := hF.exists_ne s
  rw [←h ht hs ht']
  exact inter_subset_right

lemma hasKernel.pairwiseDisjoint_sdiff {K : Finset α} (h : hasKernel F K) :
    F.toSet.PairwiseDisjoint (· \ K) := by
  intro X hX Y hY h'
  simp only [disjoint_left, mem_sdiff, not_and, Decidable.not_not, and_imp]
  intro i hiX _ hiY
  rw [←h hX hY h']
  simp [hiX, hiY]

lemma hasKernel.inf'_eq (hF : F.Nontrivial) {K : Finset α}
    (h : hasKernel F K) :
    F.inf' hF.nonempty id = K := by
  ext x
  simp only [id_eq, mem_inf']
  constructor
  case mp =>
    intro hx
    obtain ⟨s, hs, t, ht, hst⟩ := hF
    simp [←h hs ht hst, hx _ hs, hx _ ht]
  case mpr =>
    intro hx s hs
    exact h.subset hF hs hx

lemma hasKernel_iff (hF : F.Nontrivial) {K} :
    hasKernel F K ↔ (∀ s ∈ F, K ⊆ s) ∧ F.toSet.PairwiseDisjoint (· \ K) := by
  refine ⟨fun h => ⟨fun s hs => h.subset hF hs, h.pairwiseDisjoint_sdiff⟩, ?_⟩
  rintro ⟨h₁, h₂⟩ X hX Y hY h
  refine subset_antisymm ?_ (subset_inter (h₁ _ hX) (h₁ _ hY))
  simp only [subset_iff, mem_inter, and_imp]
  intro i hiX hiY
  by_contra! hiK
  have := Finset.disjoint_left.1 (h₂ hX hY h)
  simp only [mem_sdiff, not_and, Decidable.not_not, and_imp] at this
  exact hiK (this hiX hiK hiY)

@[simp] lemma hasKernel_empty : hasKernel F ∅ ↔ F.toSet.PairwiseDisjoint id := by
  by_cases F.Nontrivial
  case pos h =>
    rw [hasKernel_iff h]
    simp only [empty_subset, implies_true, sdiff_empty, true_and]
    rfl
  case neg h =>
    have : F.toSet.Subsingleton := by simpa only [Set.not_nontrivial_iff] using h
    simp [hasKernel_not_nontrivial h]
    exact this.pairwise _

lemma hasKernel_iff_inf' (hF : F.Nontrivial) {K} :
    hasKernel F K ↔ F.inf' hF.nonempty id = K ∧ F.toSet.PairwiseDisjoint (· \ K) := by
  constructor
  case mp =>
    intro hSK
    exact ⟨hSK.inf'_eq hF, hSK.pairwiseDisjoint_sdiff⟩
  case mpr =>
    rintro ⟨rfl, h₂⟩
    rw [hasKernel_iff hF]
    exact ⟨fun s hs => inf'_le id hs, h₂⟩

lemma hasKernel_inf'_iff (hF : F.Nonempty) :
    hasKernel F (F.inf' hF id) ↔ F.toSet.PairwiseDisjoint (· \ F.inf' hF id) := by
  obtain (⟨x, rfl⟩ | hS) := hF.exists_eq_singleton_or_nontrivial
  case inl => simp
  case inr => simp [hasKernel_iff_inf' hS]

lemma hasKernel_pair {X Y : Finset α} : hasKernel {X, Y} (X ∩ Y) := by
  rw [hasKernel, coe_insert, coe_singleton]
  refine (Set.pairwise_pair_of_symmetric fun A B ↦ ?_).2 fun _ ↦ rfl
  simp [inter_comm]

lemma hasKernel.image_insert {a} (hSK : hasKernel F K) (h : ∀ s ∈ F, a ∉ s) :
    hasKernel (F.image (insert a)) (insert a K) := by
  rw [hasKernel] at hSK
  simp only [hasKernel, Set.Pairwise, coe_image, Set.mem_image, mem_coe, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, mem_insert, inter_insert_of_mem, true_or]
  rintro X hX Y hY hXY
  rw [insert_erase_invOn.2.injOn.ne_iff (h X hX) (h Y hY)] at hXY
  rw [insert_inter_of_not_mem (h Y hY), hSK hX hY hXY]

end hasKernel

section isSunflower

def isSunflower (F : Finset (Finset α)) : Prop := ∃ K : Finset α, hasKernel F K

lemma isSunflower_not_nontrivial (hF : ¬F.Nontrivial) :
    isSunflower F := by
  simp [isSunflower, hasKernel_not_nontrivial hF]

@[simp] lemma isSunflower_empty : isSunflower (∅ : Finset (Finset α)) := by
  simp [isSunflower]

@[simp] lemma isSunflower_singleton {s : Finset α} : isSunflower {s} := by
  simp [isSunflower]

@[simp] lemma isSunflower_pair {s t : Finset α} : isSunflower {s, t} :=
  ⟨_, hasKernel_pair⟩

lemma isSunflower_iff_hasKernel_inf' (hF : F.Nonempty) :
    isSunflower F ↔ hasKernel F (F.inf' hF id) := by
  refine ⟨?_, fun hK => ⟨_, hK⟩⟩
  rintro ⟨K, hK⟩
  obtain (⟨x, rfl⟩ | hS) := hF.exists_eq_singleton_or_nontrivial
  next => simp
  next =>
    cases hK.inf'_eq hS
    exact hK

lemma isSunflower_iff_disjoint (hF : F.Nonempty) :
    isSunflower F ↔ F.toSet.PairwiseDisjoint (· \ F.inf' hF id) := by
  rw [isSunflower_iff_hasKernel_inf' hF, hasKernel_inf'_iff]

lemma isSunflower_of_pairwiseDisjoint {F : Finset (Finset α)} (hF : F.toSet.PairwiseDisjoint id) :
    isSunflower F :=
  ⟨∅, by simpa only [hasKernel, ←Finset.disjoint_iff_inter_eq_empty]⟩

lemma isSunflower.image_insert {a} (hF : isSunflower F) (hS' : ∀ s ∈ F, a ∉ s) :
    isSunflower (F.image (insert a)) := by
  obtain ⟨K, hK⟩ := hF
  exact ⟨_, hK.image_insert hS'⟩

lemma isSunflower.hasKernel_of_subset (hF : isSunflower F) {X Y : Finset α} (h : X ⊆ Y)
    (hX : X ∈ F) (hY : Y ∈ F) (hXY : X ≠ Y) : hasKernel F X := by
  obtain ⟨K, hK⟩ := hF
  rwa [←hK hX hY hXY, inter_eq_left.2 h] at hK

lemma IsChain.not_isSunflower (hF : 3 ≤ F.card)
    (hF' : IsChain (· ⊆ ·) (F : Set (Finset α))) :
    ¬ isSunflower F := by
  replace hF : 2 < F.card := by omega
  rw [two_lt_card_iff] at hF
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY, hXZ, hYZ⟩ := hF
  wlog hXY' : X ⊆ Y generalizing X Y with H
  case inr => exact H Y X hY hX hXY.symm hYZ hXZ ((hF' hX hY hXY).resolve_left hXY')
  intro hF
  have hX' := hF.hasKernel_of_subset hXY' hX hY hXY
  have : X ⊆ Z := by
    rw [←hX' hX hZ hXZ]
    exact inter_subset_right
  wlog hYZ' : Y ⊆ Z generalizing Y Z with H
  case inr => exact H Y hY Z hZ hXZ hXY hYZ.symm ‹_› hXY' ((hF' hY hZ hYZ).resolve_left hYZ')
  have hY' := hF.hasKernel_of_subset hYZ' hY hZ hYZ
  have : Y ⊆ X := by
    rw [←hY' hY hX hXY.symm]
    exact inter_subset_right
  exact hXY (subset_antisymm hXY' this)

instance {α β : Type*} [DecidableEq α] [PartialOrder β] [OrderBot β] {s : Finset α} {f : α → β}
    [DecidableRel (Disjoint (α := β))] :
    Decidable (s.toSet.PairwiseDisjoint f) :=
  inferInstanceAs (Decidable (s.toSet.Pairwise _))

lemma isSunflower_iff_nonempty_disjoint :
    isSunflower F ↔ ∀ (hF : F.Nonempty), F.toSet.PairwiseDisjoint (· \ F.inf' hF id) := by
  constructor
  case mp =>
    intro h hS
    exact (isSunflower_iff_disjoint _).1 h
  case mpr =>
    intro h
    rcases F.eq_empty_or_nonempty with rfl | hS
    case inl => simp
    case inr => exact (isSunflower_iff_disjoint hS).2 (h hS)

instance : DecidablePred (isSunflower (α := α)) :=
  fun _ => decidable_of_iff' _ isSunflower_iff_nonempty_disjoint

example : isSunflower {{1, 2, 3, 4}, {1, 2, 5}, {1, 2, 6, 7, 8}} := by decide
example : isSunflower {{1, 2}, {3, 4, 5}, {6}} := by decide
example : ¬ isSunflower {{1, 2}, {1, 2, 3}, {3}} := by decide

lemma isSunflower_image_image [DecidableEq β]  {f : α → β}
    (hF : isSunflower F) (hf : Set.InjOn f (F.biUnion id)) :
    isSunflower (image (image f) F) := by
  obtain ⟨K, hK⟩ := hF
  refine ⟨K.image f, ?_⟩
  rw [hasKernel, Finset.coe_image, (injOn_image hf).pairwise_image]
  refine hK.imp_on ?_
  rintro X hX Y hY _ rfl
  refine (image_inter_of_injOn _ _ (hf.mono ?_)).symm
  simp only [Finset.coe_subset, Set.union_subset_iff]
  exact ⟨Finset.subset_biUnion_of_mem id hX, Finset.subset_biUnion_of_mem id hY⟩

lemma image_biUnion_id_eq_image_image_biUnion_id {α : Type*}  [DecidableEq α] [DecidableEq β]
    {F : Finset (Finset α)} {f : α → β} :
    (F.biUnion id).image f = (F.image (image f)).biUnion id := by
  aesop

lemma biUnion_image_eq_image_image_biUnion_id {α : Type*} [DecidableEq β] {F : Finset (Finset α)}
    {f : α → β} :
    F.biUnion (image f) = (F.image (image f)).biUnion id := by aesop

lemma isSunflower_of_image_image [DecidableEq β] {f : α → β}
    (hF : isSunflower (F.image (image f))) (hf : Set.InjOn f (F.biUnion id)) :
    isSunflower F := by
  by_cases hFnt : F.Nontrivial
  case neg =>
    apply isSunflower_not_nontrivial hFnt
  have hF'nt : (F.image (image f)).Nontrivial := Nontrivial.image_of_injOn (injOn_image hf) hFnt
  classical
  obtain ⟨K, hK⟩ := hF
  let K' : Finset α := (F.biUnion id).filter (· ∈ f ⁻¹' K)
  have : K ⊆ (F.image (image f)).biUnion id := by
    obtain ⟨X, hX, Y, _, _⟩ := id hF'nt
    exact (hK.subset hF'nt hX).trans (subset_biUnion_of_mem id hX)
  have hfK' : K'.image f = K := by
    ext x
    simp only [Set.mem_preimage, mem_coe, mem_image, mem_filter, id_eq, K']
    constructor
    case mp =>
      rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    case mpr =>
      intro hx
      specialize this hx
      rw [←image_biUnion_id_eq_image_image_biUnion_id, mem_image] at this
      obtain ⟨a, ha, rfl⟩ := this
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  rw [←hfK', hasKernel, coe_image, (injOn_image hf).pairwise_image] at hK
  refine ⟨K', ?_⟩
  refine hK.imp_on ?_
  intro X hX Y hY _ (h : _ = _)
  rwa [←image_inter_of_injOn _ _ (hf.mono ?_), image_eq_image_iff hf _ (filter_subset _ _)] at h
  next =>
    refine inter_subset_left.trans ?_
    exact subset_biUnion_of_mem id hX
  next =>
    rw [Set.union_subset_iff]
    exact ⟨subset_biUnion_of_mem id hX, subset_biUnion_of_mem id hY⟩

lemma isSunflower_iff_image_image [DecidableEq β] {f : α → β}
    (hf : Set.InjOn f (F.biUnion id)) :
    isSunflower (image (image f) F) ↔ isSunflower F :=
  ⟨(isSunflower_of_image_image · hf), (isSunflower_image_image · hf)⟩

end isSunflower

def containsSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ T ⊆ F, T.card = r ∧ isSunflower T

@[simp] lemma containsSunflower_zero {F : Finset (Finset α)} : containsSunflower F 0 := ⟨∅, by simp⟩

@[simp] lemma containsSunflower_one {F : Finset (Finset α)} :
    containsSunflower F 1 ↔ F.Nonempty := by
  rw [containsSunflower]
  simp only [card_eq_one]
  constructor
  case mp =>
    simp only [forall_exists_index, and_imp]
    rintro _ hT s rfl
    simp only [singleton_subset_iff] at hT
    exact fun _ => ⟨_, hT⟩
  case mpr =>
    rintro ⟨s, hs⟩
    exact ⟨{s}, by simp [hs]⟩

@[simp] lemma containsSunflower_two {F : Finset (Finset α)} :
    containsSunflower F 2 ↔ F.Nontrivial := by
  rw [containsSunflower]
  simp only [card_eq_two, Finset.Nontrivial, Set.Nontrivial, mem_coe]
  constructor
  case mp =>
    rintro ⟨T, hXYF, ⟨X, Y, hXY, rfl⟩, hT⟩
    simp only [insert_subset_iff, singleton_subset_iff] at hXYF
    use X, hXYF.1, Y, hXYF.2
  case mpr =>
    rintro ⟨X, hX, Y, hY, hXY⟩
    exact ⟨{X, Y}, by simp [insert_subset_iff, hX, hY], ⟨_, _, hXY, rfl⟩, by simp⟩

@[simp]
lemma containsSunflower_empty (r : ℕ) : containsSunflower (∅ : Finset (Finset α)) r ↔ r = 0 := by
  simp [containsSunflower, Finset.subset_empty, eq_comm]

variable {n r : ℕ}

lemma memberSubfamily_sized {A : Finset (Finset α)} {n : ℕ} (hA : A.toSet.Sized (n + 1)) {a : α} :
    (memberSubfamily a A).toSet.Sized n := by
  intro X hX
  simp only [mem_coe, mem_memberSubfamily] at hX
  simpa [hX] using hA hX.1

theorem extracted_2 {α : Type*} [DecidableEq α] {F : Finset (Finset α)} (A : Finset α)
    (hA : ∀ f ∈ F, ¬ Disjoint f A) :
    F.card ≤ ∑ a ∈ A, (memberSubfamily a F).card := by
  have (a : α) : ((memberSubfamily a F).image (insert a)).card = (memberSubfamily a F).card := by
    rw [Finset.card_image_of_injOn]
    intro s hs t ht h
    simp only [mem_coe, mem_memberSubfamily] at hs ht
    exact (insert_erase_invOn (α := α)).2.injOn hs.2 ht.2 h
  simp only [←this, image_insert_memberSubfamily, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_le_sum fun s hs => ?_
  rw [sum_boole, Nat.cast_id, one_le_card]
  simpa [Finset.Nonempty, Finset.disjoint_right] using hA _ hs

theorem subset_memberSubfamily_iff {F G : Finset (Finset α)} {a : α} :
    G ⊆ memberSubfamily a F ↔ image (insert a) G ⊆ F ∧ ∀ s ∈ G, a ∉ s := by
  aesop (add simp Finset.subset_iff)

theorem subset_nonMemberSubfamily_iff {F G : Finset (Finset α)} {a : α} :
    G ⊆ nonMemberSubfamily a F ↔ G ⊆ F ∧ ∀ s ∈ G, a ∉ s := by
  aesop (add simp Finset.subset_iff)

theorem image_insert_subset_of_subset_memberSubfamily {F G : Finset (Finset α)} {a : α}
    (hG : G ⊆ memberSubfamily a F) : image (insert a) G ⊆ F :=
  (subset_memberSubfamily_iff.1 hG).1

theorem not_mem_of_mem_nonMemberSubfamily {F : Finset (Finset α)} {a : α} {s : Finset α}
    (hs : s ∈ nonMemberSubfamily a F) : a ∉ s := by aesop

theorem not_mem_of_mem_memberSubfamily {F : Finset (Finset α)} {a : α} {s : Finset α}
    (hs : s ∈ memberSubfamily a F) : a ∉ s := by aesop

lemma maximal_pairwiseDisjoint_iff {α β : Type*} [CompleteDistribLattice β]
    {S T : Set α} {f : α → β} (hf : ∀ t ∈ T, f t ≠ ⊥) :
    Maximal (fun U => U ⊆ S ∧ U.PairwiseDisjoint f) T ↔
      (T ⊆ S ∧ T.PairwiseDisjoint f) ∧ ∀ s ∈ S, ¬ Disjoint (f s) (⨆ t ∈ T, f t) := by
  rw [Set.maximal_iff_forall_insert ?g1]
  case g1 =>
    rintro s t ⟨htS, htf⟩ hst
    exact ⟨hst.trans htS, htf.subset hst⟩
  simp (config := { contextual := true }) only [Set.insert_subset_iff, Set.pairwiseDisjoint_insert,
    ne_eq, not_and, not_forall, Classical.not_imp, and_imp, disjoint_iSup₂_iff, and_congr_right_iff,
    true_implies]
  refine fun _ _ => ⟨?mp, ?mpr⟩
  case mp =>
    rintro h s hs
    by_contra!
    have hsT : s ∉ T := by
      intro hs'
      have := this _ hs'
      simp only [disjoint_self] at this
      exact hf _ hs' this
    obtain ⟨t, ht, -, ht''⟩ := h _ hsT hs
    exact ht'' (this t ht)
  case mpr =>
    rintro h₁ x hxT hxS
    obtain ⟨y, hy, h⟩ := h₁ x hxS
    refine ⟨y, hy, (ne_of_mem_of_not_mem hy hxT).symm, h⟩

lemma maximal_pairwiseDisjoint_finset_iff {α β : Type*} [DecidableEq β]
    {S : Set α} {T : Finset α} {f : α → Finset β} (hf : ∀ t ∈ T, f t ≠ ⊥) :
    Maximal (fun U => U ⊆ S ∧ U.PairwiseDisjoint f) T ↔
      (T.toSet ⊆ S ∧ T.toSet.PairwiseDisjoint f) ∧ ∀ s ∈ S, ¬ Disjoint (f s) (T.biUnion f) := by
  rw [Set.maximal_iff_forall_insert ?g1]
  case g1 =>
    rintro s t ⟨htS, htf⟩ hst
    exact ⟨hst.trans htS, htf.subset hst⟩
  simp (config := { contextual := true }) only [mem_coe, Set.insert_subset_iff, ne_eq, exists_prop',
    Set.pairwiseDisjoint_insert, ne_eq, not_and, not_forall, nonempty_prop, and_imp, true_implies,
    disjoint_biUnion_right, and_congr_right_iff]
  refine fun _ _ => ⟨?mp, ?mpr⟩
  case mp =>
    rintro h s hs
    by_contra!
    have hsT : s ∉ T := by
      intro hs'
      have := this _ hs'
      simp only [disjoint_self] at this
      exact hf _ hs' this
    obtain ⟨t, ht, -, ht''⟩ := h _ hsT hs
    exact ht'' (this t ht)
  case mpr =>
    rintro h₁ x hxT hxS
    obtain ⟨y, hy, h⟩ := h₁ x hxS
    exact ⟨y, hy, (ne_of_mem_of_not_mem hy hxT).symm, h⟩

theorem sunflower_induction {M : ℕ}
    {F : Finset (Finset α)} (hFn : F.toSet.Sized (n + 1)) (hFr : ¬ containsSunflower F (r + 1))
    (ih : ∀ {G : Finset (Finset α)}, G.toSet.Sized n → ¬ containsSunflower G (r + 1) → G.card ≤ M) :
    F.card ≤ r * (n + 1) * M := by
  let P := F.powerset.filter fun F' => F'.toSet.PairwiseDisjoint id
  have : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨S, hS, hSm⟩ := P.exists_max_image (·.card) this
  simp only [mem_filter, mem_powerset, and_imp, P] at hS hSm
  have h₁ : S.card ≤ r := by
    contrapose! hFr
    obtain ⟨F'', hF'', h⟩ := exists_subset_card_eq hFr
    exact ⟨F'', hF''.trans hS.1, h, isSunflower_of_pairwiseDisjoint (hS.2.subset hF'')⟩
  set A := S.biUnion id
  have h₂ : A.card ≤ r * (n + 1) :=
    (card_biUnion_le.trans_eq (sum_const_nat (hFn.mono hS.1))).trans (by gcongr)
  obtain rfl | hF := F.eq_empty_or_nonempty
  case inl => simp
  have h₃ : ∀ f ∈ F, ¬ Disjoint f A := by
    intro f hf h
    simp only [A, Finset.disjoint_biUnion_right, id_eq] at h
    have hf' : f ∉ S := by
      intro hf'
      have h₁ := h f hf'
      simp only [disjoint_self, bot_eq_empty] at h₁
      have h₂ := hFn hf
      simp [h₁] at h₂
    have : (insert f S).toSet.PairwiseDisjoint id := by
      simp only [coe_insert]
      exact hS.2.insert_of_not_mem hf' h
    have := hSm (insert f S) (by simp [insert_subset_iff, hf, hS]) this
    simp [hf'] at this
  have hA : A.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hA
    apply hF.ne_empty
    simpa [hA, eq_empty_iff_forall_not_mem] using h₃
  have h₅ : F.card ≤ ∑ a ∈ A, (memberSubfamily a F).card := extracted_2 _ h₃
  obtain ⟨a, ha⟩ : ∃ a, F.card ≤ r * (n + 1) * (memberSubfamily a F).card := by
    -- TODO: golf this
    by_contra!
    have := sum_lt_sum_of_nonempty hA (fun a _ => this a)
    simp only [sum_const, smul_eq_mul] at this
    rw [←mul_sum] at this
    have : r * (n + 1) * ∑ i ∈ A, (memberSubfamily i F).card < r * (n + 1) * F.card := by
      refine this.trans_le ?_
      gcongr
    have := lt_of_mul_lt_mul_left this (by positivity)
    linarith
  have : ¬ containsSunflower (memberSubfamily a F) (r + 1) := by
    rintro ⟨G, hG, hGr, hG'⟩
    apply hFr
    rw [subset_memberSubfamily_iff] at hG
    refine ⟨image (insert a) G, hG.1, ?_, hG'.image_insert hG.2⟩
    rw [Finset.card_image_of_injOn, hGr]
    intro s hs t ht h
    simp only [mem_coe, mem_memberSubfamily] at hs ht
    exact (insert_erase_invOn (α := α)).2.injOn (hG.2 _ hs) (hG.2 _ ht) h
  have := ih (memberSubfamily_sized hFn) this
  refine ha.trans ?_
  gcongr

theorem sunflower_lemma_aux {F : Finset (Finset α)} (hFn : F.toSet.Sized n)
    (hFr : ¬ containsSunflower F (r + 1)) :
    F.card ≤ n ! * r ^ n := by
  induction n generalizing F
  case zero => simpa [←not_lt, one_lt_card_iff_nontrivial] using hFn.subsingleton
  case succ n ih =>
    calc F.card ≤ r * (n + 1) * (n ! * r ^ n) := sunflower_induction hFn hFr ih
      _ = (n + 1) ! * r ^ (n + 1) := by rw [Nat.factorial_succ]; ring

theorem sunflower_lemma {F : Finset (Finset α)} (hFn : F.toSet.Sized n)
    (hFr : ¬ containsSunflower F r) :
    F.card ≤ n ! * (r - 1) ^ n := by
  rcases r with rfl | r
  case zero => simp at hFr
  case succ => exact sunflower_lemma_aux hFn hFr

-- TODO: mark image_subset_image as gcongr
theorem containsSunflower_image_image {β : Type*} [DecidableEq β]
    {F : Finset (Finset α)} {f : α → β} (hf : Set.InjOn f (F.biUnion id)) :
    containsSunflower F r → containsSunflower (F.image (image f)) r := by
  rintro ⟨G, hGF, hGr, hG⟩
  refine ⟨G.image (image f), image_subset_image hGF, ?_, ?_⟩
  next =>
    rw [Finset.card_image_of_injOn, hGr]
    refine injOn_image <| hf.mono <| biUnion_subset_biUnion_of_subset_left id hGF
  next => exact isSunflower_image_image hG (hf.mono (biUnion_subset_biUnion_of_subset_left id hGF))

-- TODO: make subset_image_iff about finsets
theorem containsSunflower_of_image_image {β : Type*} [DecidableEq β]
    {F : Finset (Finset α)} {f : α → β} (hf : Set.InjOn f (F.biUnion id)) :
    containsSunflower (F.image (image f)) r → containsSunflower F r := by
  rintro ⟨G, hG₁, hGr, hG₂⟩
  have : G.toSet ⊆ image f '' F := by
    rw [← coe_image, coe_subset]
    exact hG₁
  rw [subset_image_iff] at this
  obtain ⟨G', hG', rfl⟩ := this
  have hf' := hf.mono (biUnion_subset_biUnion_of_subset_left id hG')
  have hG₃ : isSunflower G' := isSunflower_of_image_image hG₂ hf'
  refine ⟨G', hG', ?_, hG₃⟩
  rw [← hGr, card_image_of_injOn (injOn_image hf')]

theorem containsSunflower_iff_image_image {β : Type*} [DecidableEq β]
    {F : Finset (Finset α)} {f : α → β} (hf : Set.InjOn f (F.biUnion id)) :
    containsSunflower (F.image (image f)) r ↔ containsSunflower F r :=
  ⟨containsSunflower_of_image_image hf, containsSunflower_image_image hf⟩

@[simp] private abbrev sunflowerSet (n r : ℕ) : Set ℕ :=
  {card F | (F : Finset (Finset ℕ)) (_ : F.toSet.Sized n) (_ : ¬ containsSunflower F r)}

noncomputable def sunflowerNumber (n r : ℕ) : ℕ := sSup (sunflowerSet n r)

private lemma sunflowerSet_bddAbove (n r : ℕ) :
    BddAbove (sunflowerSet n r) := by
  refine ⟨n ! * (r - 1) ^ n, ?_⟩
  simp only [exists_prop', nonempty_prop, exists_and_left, mem_upperBounds, Set.mem_setOf_eq,
    forall_exists_index, and_imp, sunflowerSet]
  rintro _ F hFn hFr rfl
  exact sunflower_lemma hFn hFr

private lemma sunflowerSet_nonempty (hr : r ≠ 0) : (sunflowerSet n r).Nonempty :=
  ⟨0, ∅, by simp [*]⟩

lemma le_sunflowerNumber_nat {n r m : ℕ} (F : Finset (Finset ℕ)) (hFn : F.toSet.Sized n)
    (hFr : ¬ containsSunflower F r) (hSm : F.card = m) :
    m ≤ sunflowerNumber n r :=
  le_csSup (sunflowerSet_bddAbove n r) ⟨F, hFn, hFr, hSm⟩

lemma range_equiv {α : Type*} (s : Finset α) : Nonempty (range s.card ≃ s) := by
  rw [←Fintype.card_eq, Fintype.card_coe, Fintype.card_coe, card_range]

lemma le_sunflowerNumber {n r m : ℕ} (F : Finset (Finset α)) (hFn : F.toSet.Sized n)
    (hFr : ¬ containsSunflower F r) (hSm : F.card = m) :
    m ≤ sunflowerNumber n r := by
  obtain ⟨e⟩ : Nonempty (range (F.biUnion id).card ≃ F.biUnion id) := by
    rw [←Fintype.card_eq]
    simp
  let f (x : α) : ℕ := if hx : x ∈ F.biUnion id then e.symm ⟨x, hx⟩ else 0
  have hf : Set.InjOn f (F.biUnion id) := by
    intro x hx y hy h
    simp only [mem_coe] at hx hy
    simp only [f, dif_pos, hx, hy] at h
    rwa [←Subtype.ext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at h
  let G : Finset (Finset ℕ) := F.image (image f)
  have hGn : G.toSet.Sized n := by
    intro X
    simp only [coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp, G]
    rintro Y hY rfl
    rw [card_image_of_injOn, hFn hY]
    exact hf.mono (subset_biUnion_of_mem id hY)
  have hGm : G.card = m := by
    rw [card_image_of_injOn, hSm]
    exact injOn_image hf
  refine le_sunflowerNumber_nat G hGn ?_ hGm
  rwa [containsSunflower_iff_image_image hf]

/--
If `F` is a set family, all of whose elements have size `n` and it does not contain a sunflower,
then its cardinality is at most the sunflower number `sunflowerNumber n r`.
While this is primarily useful for constructing lower bounds on the sunflower number, it also
shows that large set families must contain a sunflower.

In the language of hypergraphs, this says that an `n`-uniform hypergraph with no sunflower must
have at most `sunflowerNumber n r` edges.
-/
lemma card_le_sunflowerNumber {n r : ℕ} {F : Finset (Finset α)} (hFn : F.toSet.Sized n)
    (hFr : ¬ containsSunflower F r) :
    card F ≤ sunflowerNumber n r :=
  le_sunflowerNumber F hFn hFr rfl

/-- For any `m`, there is a set family of size `m` which avoids a sunflower of any size `≥ 3`. -/
example (m : ℕ) : ∃ F : Finset (Finset ℕ), F.card = m ∧ ∀ r ≥ 3, ¬ containsSunflower F r := by
  refine ⟨(range m).image range, ?hc, fun r hr => ?hr⟩
  case hc =>
    rw [card_image_of_injective, card_range]
    exact strictMono_range.injective
  case hr =>
    rintro ⟨G, hGn, rfl, hG⟩
    have : IsChain (· ⊆ ·) (G : Set (Finset ℕ)) := by
      intro X hX Y hY hXY
      replace hX := hGn hX
      replace hY := hGn hY
      simp only [mem_image, mem_range] at hX hY
      obtain ⟨x, _, rfl⟩ := hX
      obtain ⟨y, _, rfl⟩ := hY
      simp [le_total]
    exact this.not_isSunflower hr hG

lemma exists_card_eq_sunflowerNumber_nat (n : ℕ) {r : ℕ} (hr : r ≠ 0) :
    ∃ F : Finset (Finset ℕ), F.toSet.Sized n ∧ ¬ containsSunflower F r ∧
      F.card = sunflowerNumber n r := by
  obtain ⟨F, h₁, h₂, h₃⟩ := Nat.sSup_mem (sunflowerSet_nonempty hr) (sunflowerSet_bddAbove n r)
  exact ⟨F, h₁, h₂, h₃⟩

lemma exists_card_eq_sunflowerNumber (α : Type*) [DecidableEq α] [Infinite α]
    (n : ℕ) {r : ℕ} (hr : r ≠ 0) :
    ∃ F : Finset (Finset α), F.toSet.Sized n ∧ ¬ containsSunflower F r ∧
      F.card = sunflowerNumber n r := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → α, Function.Injective f := ⟨_, (Infinite.natEmbedding α).injective⟩
  obtain ⟨F, h₁, h₂, h₃⟩ := exists_card_eq_sunflowerNumber_nat n hr
  refine ⟨F.image (image f), ?_, by rwa [containsSunflower_iff_image_image hf.injOn], ?_⟩
  next => simpa [Set.Sized, card_image_of_injective _ hf] using h₁
  next => rwa [card_image_of_injOn (injOn_image hf.injOn)]

lemma sunflowerNumber_lt (α : Type*) [DecidableEq α] [Infinite α]
    {n r m : ℕ} (hrm : r ≠ 0 ∨ m ≠ 0)
    (h : ∀ ⦃F : Finset (Finset α)⦄, F.toSet.Sized n → ¬ containsSunflower F r → F.card < m) :
    sunflowerNumber n r < m := by
  rcases eq_or_ne r 0 with rfl | hr
  case inl => simp_all [sunflowerNumber, pos_iff_ne_zero]
  obtain ⟨F, hFn, hFr, hF⟩ := exists_card_eq_sunflowerNumber α n hr
  have := h hFn hFr
  omega

lemma sunflowerNumber_le (α : Type*) [DecidableEq α] [Infinite α] {m : ℕ}
    (h : ∀ ⦃F : Finset (Finset α)⦄, F.toSet.Sized n → ¬ containsSunflower F r → F.card ≤ m) :
    sunflowerNumber n r ≤ m := by
  simp only [←Nat.lt_add_one_iff] at *
  exact sunflowerNumber_lt α (by simp) h

@[simp] lemma sunflowerNumber_right_zero (n : ℕ) : sunflowerNumber n 0 = 0 := by
  simp [sunflowerNumber]

@[simp] lemma sunflowerNumber_right_one (n : ℕ) : sunflowerNumber n 1 = 0 := by
  simp [sunflowerNumber]

@[simp] lemma sunflowerNumber_right_two (n : ℕ) : sunflowerNumber n 2 = 1 :=
  le_antisymm
    (sunflowerNumber_le ℕ (by simp [← one_lt_card_iff_nontrivial]))
    (le_sunflowerNumber {range n} (by simp) (by simp) (by simp))

lemma sunflowerNumber_left_zero_le (r : ℕ) : sunflowerNumber 0 r ≤ 1 :=
  sunflowerNumber_le ℕ fun F hF0 _ => by
    simpa [←not_lt, one_lt_card_iff_nontrivial] using hF0.subsingleton

lemma sunflowerNumber_left_zero_add_two (r : ℕ) : sunflowerNumber 0 (r + 2) = 1 := by
  refine le_antisymm (sunflowerNumber_left_zero_le _) ?_
  refine le_sunflowerNumber_nat {∅} (by simp) ?_ (by simp)
  rintro ⟨X, hX, hX', -⟩
  have := card_le_card hX
  simp only [card_singleton] at this
  omega

@[simp] lemma sunflowerNumber_left_zero {r : ℕ} (hr : 2 ≤ r) : sunflowerNumber 0 r = 1 :=
  match r with
  | 0 | 1 => by simp at hr
  | r + 2 => sunflowerNumber_left_zero_add_two _

lemma sunflowerNumber_le_mul_sunflowerNumber_aux (n r : ℕ) :
    sunflowerNumber (n + 1) (r + 1) ≤ r * (n + 1) * sunflowerNumber n (r + 1) :=
  sunflowerNumber_le ℕ fun _ hFn hFr => sunflower_induction hFn hFr card_le_sunflowerNumber

lemma sunflowerNumber_le_mul_sunflowerNumber (n r : ℕ) :
    sunflowerNumber (n + 1) r ≤ (r - 1) * (n + 1) * sunflowerNumber n r := by
  cases r
  case zero => simp
  case succ => exact sunflowerNumber_le_mul_sunflowerNumber_aux _ _

lemma sunflowerNumber_left_one_aux (r : ℕ) :
    sunflowerNumber 1 (r + 1) = r := by
  refine le_antisymm ?g1 ?g2
  case g1 =>
    refine (sunflowerNumber_le_mul_sunflowerNumber _ _).trans ?_
    simp only [add_tsub_cancel_right, zero_add, mul_one]
    exact mul_le_of_le_one_right (Nat.zero_le _) (sunflowerNumber_left_zero_le _)
  case g2 =>
    refine le_sunflowerNumber_nat ((range r).map ⟨_, singleton_injective⟩) ?g1 ?g2 (by simp)
    case g1 => simp [Set.Sized]
    case g2 =>
      rintro ⟨X, hX, hXc, _⟩
      have : X.card ≤ r := by
        have := card_le_card hX
        rwa [card_map, card_range] at this
      omega

@[simp] lemma sunflowerNumber_left_one (r : ℕ) :
    sunflowerNumber 1 r = r - 1 := by
  cases r
  case zero => simp
  case succ => rw [sunflowerNumber_left_one_aux, add_tsub_cancel_right]

/--
The **sunflower lemma*:
A simple but explicit upper bound on sunflower numbers, due to Erdős and Rado.
-/
theorem sunflowerNumber_le_factorial_mul_pow (n r : ℕ) : sunflowerNumber n r ≤ n ! * (r - 1) ^ n :=
  sunflowerNumber_le ℕ fun _ => sunflower_lemma

section sunflowerNumber_lower_bounds

theorem subset_image_iff {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β} :
    t ⊆ s.image f ↔ ∃ s' : Finset α, s' ⊆ s ∧ s'.image f = t := by
  refine ⟨fun ht => ?_, fun ⟨s', hs', h⟩ => h ▸ image_subset_image hs'⟩
  refine ⟨s.filter (f · ∈ t), filter_subset _ _, le_antisymm (by simp [image_subset_iff]) ?_⟩
  intro x hx
  specialize ht hx
  aesop

lemma image_toLeft_isSunflower [DecidableEq β] {F : Finset (Finset (α ⊕ β))} (hF : isSunflower F) :
    isSunflower (F.image toLeft) := by
  obtain ⟨K, hK⟩ := hF
  refine ⟨K.toLeft, ?_⟩
  simp only [hasKernel, Set.Pairwise, mem_coe, mem_image, ne_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro X hX Y hY h
  have : X ≠ Y := by contrapose! h; rw [h]
  specialize hK hX hY this
  rw [←toLeft_inter, hK]

lemma image_toRight_isSunflower [DecidableEq β] {F : Finset (Finset (α ⊕ β))} (hF : isSunflower F) :
    isSunflower (F.image toRight) := by
  obtain ⟨K, hK⟩ := hF
  refine ⟨K.toRight, ?_⟩
  simp only [hasKernel, Set.Pairwise, mem_coe, mem_image, ne_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro X hX Y hY h
  have : X ≠ Y := by contrapose! h; rw [h]
  specialize hK hX hY this
  rw [←toRight_inter, hK]

lemma mul_sunflowerNumber_aux {a b r : ℕ} (hr : 2 ≤ r) :
    sunflowerNumber a r * sunflowerNumber b r ≤ sunflowerNumber (a + b) r := by
  obtain ⟨FA, hFA₁, hFA₂, hFA₃⟩ := exists_card_eq_sunflowerNumber ℕ a (show r ≠ 0 by omega)
  obtain ⟨FB, hFB₁, hFB₂, hFB₃⟩ := exists_card_eq_sunflowerNumber ℕ b (show r ≠ 0 by omega)
  let F : Finset (Finset (ℕ ⊕ ℕ)) := Finset.image₂ Finset.disjSum FA FB
  have hF : F.card = sunflowerNumber a r * sunflowerNumber b r := by
    rw [card_image₂ Injective2_disjSum, hFA₃, hFB₃]
  have hFn : F.toSet.Sized (a + b) := by
    simp only [Set.Sized, F, coe_image₂, Set.mem_image2, mem_coe, forall_exists_index, and_imp]
    rintro _ A hA B hB rfl
    simp [hFA₁ hA, hFB₁ hB]
  suffices hFr : ¬ containsSunflower F r from le_sunflowerNumber F hFn hFr hF
  rintro ⟨G, hGF, hGr, hG⟩
  let GA := G.image toLeft
  let GB := G.image toRight
  have hGA : isSunflower GA := image_toLeft_isSunflower hG
  have hGB : isSunflower GB := image_toRight_isSunflower hG
  have hGAF : GA ⊆ FA := by
    refine (image_subset_image hGF).trans ?_
    simp (config := {contextual := true}) [F, image_image₂]
  have hGBF : GB ⊆ FB := by
    refine (image_subset_image hGF).trans ?_
    simp (config := {contextual := true}) [F, image_image₂]
  have hGL : ¬ G.toSet.InjOn toLeft := by
    rw [←card_image_iff, hGr]
    intro h
    exact hFA₂ ⟨_, hGAF, h, hGA⟩
  have hA : ∃ A, ∀ X ∈ G, X.toLeft = A := by
    simp only [Set.InjOn, mem_coe, not_forall, Classical.not_imp] at hGL
    obtain ⟨B, hB, C, hC, h₁, h₂⟩ := hGL
    refine ⟨B.toLeft, fun X hX => ?_⟩
    by_contra!
    obtain ⟨A, hA⟩ := hG
    cases hA hB hC h₂
    have hXBBC : _ = _ := hA hX hB fun h => this (h ▸ rfl)
    apply_fun toLeft at hXBBC
    rw [toLeft_inter, toLeft_inter, ←h₁, inter_self, inter_eq_right] at hXBBC
    have hXc : X.toLeft.card = a := hFA₁ (hGAF (mem_image_of_mem _ hX))
    have hBc : B.toLeft.card = a := hFA₁ (hGAF (mem_image_of_mem _ hB))
    exact this (eq_of_superset_of_card_ge hXBBC (by rw [hXc, hBc]))
  have hGR : ¬ G.toSet.InjOn toRight := by
    rw [←card_image_iff, hGr]
    intro h
    exact hFB₂ ⟨_, hGBF, h, hGB⟩
  have hB : ∃ B, ∀ X ∈ G, X.toRight = B := by
    simp only [Set.InjOn, mem_coe, not_forall, Classical.not_imp] at hGR
    obtain ⟨B, hB, C, hC, h₁, h₂⟩ := hGR
    refine ⟨B.toRight, fun X hX => ?_⟩
    by_contra!
    obtain ⟨A, hA⟩ := hG
    cases hA hB hC h₂
    have hXBBC : _ = _ := hA hX hB fun h => this (h ▸ rfl)
    apply_fun toRight at hXBBC
    rw [toRight_inter, toRight_inter, ←h₁, inter_self, inter_eq_right] at hXBBC
    have hXc : X.toRight.card = b := hFB₁ (hGBF (mem_image_of_mem _ hX))
    have hBc : B.toRight.card = b := hFB₁ (hGBF (mem_image_of_mem _ hB))
    exact this (eq_of_superset_of_card_ge hXBBC (by rw [hXc, hBc]))
  obtain ⟨A, hA⟩ := hA
  obtain ⟨B, hB⟩ := hB
  have : G ⊆ {A.disjSum B} := by
    intro X hX
    rw [mem_singleton, eq_comm, disjSum_eq_iff, hA _ hX, hB _ hX]
    simp
  have : G.card ≤ 1 := by
    rw [card_le_one_iff_subset_singleton]
    exact ⟨_, this⟩
  omega

lemma mul_sunflowerNumber {a b r : ℕ} :
    sunflowerNumber a r * sunflowerNumber b r ≤ sunflowerNumber (a + b) r :=
  match r with
  | 0 | 1 => by simp
  | r + 2 => mul_sunflowerNumber_aux (by simp)

lemma pow_le_sunflowerNumber {n r : ℕ} (hn : n ≠ 0) : (r - 1) ^ n ≤ sunflowerNumber n r :=
  match n, hn with
  | 1, _ => by simp
  | n + 2, _ =>
      (Nat.mul_le_mul (pow_le_sunflowerNumber (by simp))
        (sunflowerNumber_left_one _).ge).trans mul_sunflowerNumber
