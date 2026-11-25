/-
# Loose ends

* `sk_eq_of_linear`   : Corollary 3.6 (PDF remark after Definition 3.3): a linear `r`-uniform
                        hypergraph with `r ≥ 4` is its own skeleton.
* `normal_cancel`     : Theorem 6.2, normal-product clause.
* `strong_power`      : Theorem 6.2, powers clause: `A^{⊠k} ≅ B^{⊠k}` (`k ≥ 1`) implies `A ≅ B`.
  Powers are `strongPi` over `Fin k`; by `iso_strongPi_sum` / `iso_strongPi_unique` every
  bracketing of binary products is isomorphic to it.
-/
import Hg.Tilde

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

variable {r : ℕ} {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-! ## Corollary 3.6: linear hypergraphs are their own skeleton -/

theorem sk_eq_of_linear (hr : 4 ≤ r) {A : HG α} (hA : Uniform r A) (hl : Linear A) :
    (Sk A).E = A.E := by
  ext e
  simp only [Sk, mem_filter, and_iff_left_iff_imp]
  intro he ht
  obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.1 (by rw [hA e he]; omega : 1 < e.card)
  obtain ⟨E', hE', hne, hint⟩ := ht u hu w hw huw
  have := hl e he E' hE' (Ne.symm hne)
  rw [hint] at this
  have a1 := card_erase_add_one hu
  have a2 := card_erase_add_one (mem_erase.2 ⟨Ne.symm huw, hw⟩)
  rw [hA e he] at a1
  omega

/-! ## Theorem 6.2: the normal product -/

/-- **Theorem 6.2** (normal product): cancellation for `r`-uniform factors. -/
theorem normal_cancel [Nonempty γ] (hr : 2 ≤ r) {A : HG α} {B : HG β} {C : HG γ}
    (hA : Uniform r A) (hB : Uniform r B) (hC : Uniform r C)
    (h : Iso (normal A C) (normal B C)) : Iso A B := by
  rw [HG.ext' (normal_eq_strong hA hC), HG.ext' (normal_eq_strong hB hC)] at h
  exact strong_cancel hr C hA hB h

/-! ## Theorem 6.2: powers -/

section powers

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]

/-- Homomorphism counts into a structure that splits coordinatewise multiply. -/
lemma homCard_pi {δ : Type} [Fintype δ] {X : HG δ} {P : HG (∀ i, V i)} {Q : ∀ i, HG (V i)}
    (hP : ∀ e ∈ X.E, ∀ f : δ → ∀ i, V i,
      (e.image f ∈ P.E ↔ ∀ i, e.image (fun a => f a i) ∈ (Q i).E)) :
    homCard X P = ∏ i, homCard X (Q i) := by
  unfold homCard
  rw [← Fintype.card_pi]
  exact Fintype.card_congr
    { toFun := fun f i => ⟨fun a => f.1 a i, fun e he => (hP e he f.1).1 (f.2 e he) i⟩
      invFun := fun g => ⟨fun a i => (g i).1 a, fun e he => (hP e he _).2 fun i => (g i).2 e he⟩
      left_inv := fun f => rfl
      right_inv := fun g => rfl }

lemma mem_loops_strongPi {X : ∀ i, HG (V i)} (hX : ∀ i, Uniform r (X i))
    {S : Finset (∀ i, V i)} (hS : S.Nonempty) (hSr : S.card ≤ r) :
    S ∈ (loops (strongPi r X)).E ↔ ∀ i, (S.image fun x => x i) ∈ (loops (X i)).E := by
  simp only [mem_loops]
  constructor
  · rintro (h | ⟨v, rfl⟩) i
    · rcases (mem_strongPi.1 h).2.1 i with h1 | h1
      · exact Or.inr (card_eq_one.1 h1)
      · exact Or.inl h1
    · exact Or.inr ⟨v i, by simp⟩
  · intro h
    by_cases he : ∃ i, (S.image fun x => x i) ∈ (X i).E
    · obtain ⟨i, hi⟩ := he
      refine Or.inl (mem_strongPi.2 ⟨le_antisymm hSr ?_, fun j => ?_, i, hi⟩)
      · rw [← hX i _ hi]; exact card_image_le
      · rcases h j with h1 | ⟨v, hv⟩
        · exact Or.inr h1
        · exact Or.inl (by rw [hv, card_singleton])
    · push_neg at he
      have hs : ∀ i, (S.image fun x => x i).card = 1 := fun i => by
        rcases h i with h1 | ⟨v, hv⟩
        · exact absurd h1 (he i)
        · rw [hv, card_singleton]
      obtain ⟨x0, hx0⟩ := hS
      exact Or.inr ⟨x0, eq_singleton_iff_unique_mem.2 ⟨hx0, fun x hx =>
        funext fun i => eq_of_card_image_eq_one (hs i) hx hx0⟩⟩

lemma homCard_loops_power {δ : Type} [Fintype δ] {X : HG δ} (hX : Good r X) {A : HG α}
    (hA : Uniform r A) :
    homCard X (loops (strongPi r fun _ : ι => A)) = homCard X (loops A) ^ Fintype.card ι := by
  rw [homCard_pi (Q := fun _ : ι => loops A), prod_const, card_univ]
  intro e he f
  obtain ⟨hne, hle⟩ := hX e he
  rw [mem_loops_strongPi (fun _ => hA) (hne.image f) (card_image_le.trans hle)]
  simp only [image_image]
  rfl

/-- **Theorem 6.2** (powers): `A^{⊠k} ≅ B^{⊠k}` with `k ≥ 1` implies `A ≅ B`. The power is
indexed by any nonempty finite type `ι` (`k = |ι|`, e.g. `ι = Fin k`). -/
theorem strong_power [Nonempty ι] (hr : 2 ≤ r) {A : HG α} {B : HG β}
    (hA : Uniform r A) (hB : Uniform r B)
    (h : Iso (strongPi r fun _ : ι => A) (strongPi r fun _ : ι => B)) : Iso A B := by
  have hL := iso_loops h
  apply iso_of_iso_loops hr hA hB
  apply lovasz (good_loops (by omega) hA) (good_loops (by omega) hB)
  intro δ _ X hX
  have e1 := homCard_loops_power (ι := ι) hX hA
  have e2 := homCard_loops_power (ι := ι) hX hB
  rw [homCard_congr_right hL] at e1
  exact Nat.pow_left_injective Fintype.card_ne_zero (e1.symm.trans e2)

end powers

end HypProd
