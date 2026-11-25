/-
# Unique prime factorization for the strong product (paper's Theorem 3.5 / PDF Theorem 3.6)

Main result `unique_prime_factorization`: for `r ≥ 4`, an `r`-uniform hypergraph `H` whose
skeleton has connected 2-section has a factorization into strong-prime `r`-uniform factors,
unique up to reordering and isomorphism of the factors.

**Trusted assumption.** The proof uses one axiom, `cartesian_coordinatization`, a packaged
form of the unique-coordinatization theorem for Cartesian products of graphs (Imrich, Miller;
Hammack–Imrich–Klavžar Ch. 6): a connected finite graph has a coordinatization
`V ≃ Π k, U k` (all `U k` nontrivial) such that every Cartesian factorization into nontrivial
factors is a coarsening of it. It combines Sabidussi–Vizing existence of prime factorizations
with the coordinatization theorem the paper cites.

Products of factors are `strongPi` (Lemma 2.2's description), identified with nested binary
strong products by `iso_strongPi_sum` and `iso_strongPi_unique`.
-/
import Hg.Iterated
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

variable {r : ℕ}

/-! ## Isomorphism invariance of the skeleton -/

section invariance

variable {α β : Type} [Fintype α] [Fintype β] {A : HG α} {B : HG β} {φ : α ≃ β}

lemma IsoVia.symm (h : IsoVia A B φ) : IsoVia B A φ.symm := fun s => by
  rw [h, image_image_equiv]

lemma tc_of_isoVia (h : IsoVia A B φ) {E : Finset α} (ht : TC A E) : TC B (E.image φ) := by
  intro u' hu' w' hw' hne
  obtain ⟨u, hu, rfl⟩ := mem_image.1 hu'
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
  obtain ⟨E', hE', hne', hint⟩ := ht u hu w hw (fun h => hne (h ▸ rfl))
  refine ⟨E'.image φ, (h E').1 hE', fun h2 => hne' (image_injective φ.injective h2), ?_⟩
  rw [← image_inter _ _ φ.injective, hint, image_erase φ.injective, image_erase φ.injective]

lemma tc_iff_of_isoVia (h : IsoVia A B φ) (E : Finset α) : TC A E ↔ TC B (E.image φ) := by
  refine ⟨tc_of_isoVia h, fun ht => ?_⟩
  have := tc_of_isoVia h.symm ht
  rwa [image_image, show (⇑φ.symm ∘ ⇑φ) = id from funext fun x => by simp, image_id] at this

lemma sk_isoVia (h : IsoVia A B φ) : IsoVia (Sk A) (Sk B) φ := fun s => by
  simp only [Sk, mem_filter, h s, tc_iff_of_isoVia h]

end invariance

/-! ## Lines in an iterated product -/

section lines

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)] {X : ∀ i, HG (V i)}

lemma image_update_proj_self (c : ∀ i, V i) (i : ι) (e : Finset (V i)) :
    ((e.image (update c i)).image fun x => x i) = e := by
  rw [image_image]
  have : ((fun x : ∀ i, V i => x i) ∘ update c i) = id := funext fun v => by simp
  rw [this, image_id]

lemma image_update_proj_ne (c : ∀ i, V i) {i j : ι} (hij : j ≠ i) {e : Finset (V i)}
    (he : e.Nonempty) : ((e.image (update c i)).image fun x => x j) = {c j} := by
  rw [image_image]
  have : ((fun x : ∀ i, V i => x j) ∘ update c i) = fun _ => c j :=
    funext fun v => by simp [update_of_ne hij]
  rw [this, image_const he]

/-- A line `{c} ×…× e ×…× {c}` is an edge of the product iff `e` is an edge of its factor. -/
lemma mem_strongPi_line (hr : 2 ≤ r) (hX : ∀ i, Uniform r (X i)) (c : ∀ i, V i) (i : ι)
    (e : Finset (V i)) : e.image (update c i) ∈ (strongPi r X).E ↔ e ∈ (X i).E := by
  have hc : (e.image (update c i)).card = e.card :=
    card_image_of_injective _ (update_injective c i)
  rw [mem_strongPi, hc]
  constructor
  · rintro ⟨hcard, -, j, hj⟩
    by_cases hji : j = i
    · subst hji; rwa [image_update_proj_self] at hj
    · have hne : e.Nonempty := card_pos.1 (by omega)
      rw [image_update_proj_ne c hji hne] at hj
      have := hX j _ hj
      rw [card_singleton] at this; omega
  · intro he
    have hne : e.Nonempty := card_pos.1 (by rw [hX i e he]; omega)
    refine ⟨hX i e he, fun j => ?_, i, by rwa [image_update_proj_self]⟩
    by_cases hji : j = i
    · subst hji; rw [image_update_proj_self]; exact Or.inr he
    · rw [image_update_proj_ne c hji hne]; exact Or.inl (card_singleton _)

/-- A set whose projections other than `i` are singletons is a line through any of its points. -/
lemma eq_line {S : Finset (∀ i, V i)} {i : ι} (h : ∀ j ≠ i, (S.image fun x => x j).card = 1)
    {x0 : ∀ i, V i} (hx0 : x0 ∈ S) : S = (S.image fun x => x i).image (update x0 i) := by
  have key : ∀ x ∈ S, update x0 i (x i) = x := fun x hx => funext fun k => by
    by_cases hk : k = i
    · subst hk; simp
    · rw [update_of_ne hk]; exact eq_of_card_image_eq_one (h k hk) hx0 hx
  ext x
  rw [image_image]
  constructor
  · intro hx; exact mem_image.2 ⟨x, hx, key x hx⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    change update x0 i (y i) ∈ S
    rw [key y hy]; exact hy

end lines

/-! ## The skeleton of an iterated product -/

section skeletonPi

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)] {X : ∀ i, HG (V i)}

/-- Cartesian product of an indexed family: one projection an edge, the others singletons. -/
def boxPiH (Q : ∀ i, HG (V i)) : HG (∀ i, V i) where
  E := univ.filter fun S =>
    ∃ i, (S.image fun x => x i) ∈ (Q i).E ∧ ∀ j ≠ i, (S.image fun x => x j).card = 1

lemma tc_noncart_pi (hX : ∀ i, Uniform r (X i)) {S : Finset (∀ i, V i)}
    (hS : S ∈ (strongPi r X).E) {i j : ι} (hij : i ≠ j)
    (hi : (S.image fun x => x i) ∈ (X i).E) (hj : (S.image fun x => x j) ∈ (X j).E) :
    TC (strongPi r X) S := by
  have hc := (mem_strongPi.1 hS).1
  have ii : Set.InjOn (fun x : ∀ i, V i => x i) (S : Set (∀ i, V i)) :=
    injOn_of_card_image_eq (s := S) (by rw [hX i _ hi, hc])
  have ij : Set.InjOn (fun x : ∀ i, V i => x j) (S : Set (∀ i, V i)) :=
    injOn_of_card_image_eq (s := S) (by rw [hX j _ hj, hc])
  intro u hu w hw huw
  have di : u i ≠ w i := fun h => huw (ii hu hw h)
  have dj : u j ≠ w j := fun h => huw (ij hu hw h)
  set p := update u j (w j)
  set q := update w j (u j)
  have pi' : p i = u i := update_of_ne hij _ _
  have qi : q i = w i := update_of_ne hij _ _
  have pj : p j = w j := update_self _ _ _
  have qj : q j = u j := update_self _ _ _
  have hp : p ∉ S := fun h => dj (by rw [← pj, ii hu h pi'.symm])
  have hq : q ∉ S := fun h => dj (by rw [← qj, ii hw h qi.symm])
  have hpq : p ≠ q := fun h => di (by rw [← pi', ← qi, h])
  have hRS : (S.erase u).erase w ⊆ S := (erase_subset _ _).trans (erase_subset _ _)
  have hR : ∀ x, x ∈ (S.erase u).erase w ↔ x ≠ w ∧ x ≠ u ∧ x ∈ S := fun x => by
    simp only [mem_erase]
  set E' : Finset (∀ i, V i) := insert p (insert q ((S.erase u).erase w)) with hE'
  have hmem : ∀ x, x ∈ E' ↔ x = p ∨ x = q ∨ x ∈ (S.erase u).erase w :=
    fun x => by simp only [hE', mem_insert]
  have proj : ∀ k, (E'.image fun x => x k) = S.image fun x => x k := by
    intro k
    ext z
    simp only [mem_image]
    by_cases hk : k = j
    · subst hk
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases (hmem x).1 hx with rfl | rfl | hx
        · exact ⟨w, hw, pj.symm⟩
        · exact ⟨u, hu, qj.symm⟩
        · exact ⟨x, hRS hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : x = u
        · exact ⟨q, (hmem _).2 (Or.inr (Or.inl rfl)), by rw [qj, hxu]⟩
        by_cases hxw : x = w
        · exact ⟨p, (hmem _).2 (Or.inl rfl), by rw [pj, hxw]⟩
        exact ⟨x, (hmem _).2 (Or.inr (Or.inr ((hR x).2 ⟨hxw, hxu, hx⟩))), rfl⟩
    · have pk : p k = u k := update_of_ne hk _ _
      have qk : q k = w k := update_of_ne hk _ _
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases (hmem x).1 hx with rfl | rfl | hx
        · exact ⟨u, hu, pk.symm⟩
        · exact ⟨w, hw, qk.symm⟩
        · exact ⟨x, hRS hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : x = u
        · exact ⟨p, (hmem _).2 (Or.inl rfl), by rw [pk, hxu]⟩
        by_cases hxw : x = w
        · exact ⟨q, (hmem _).2 (Or.inr (Or.inl rfl)), by rw [qk, hxw]⟩
        exact ⟨x, (hmem _).2 (Or.inr (Or.inr ((hR x).2 ⟨hxw, hxu, hx⟩))), rfl⟩
  have cE : E'.card = r := by
    have hqR : q ∉ (S.erase u).erase w := fun h => hq (hRS h)
    have hpR : p ∉ insert q ((S.erase u).erase w) := by
      rw [mem_insert]
      rintro (h | h)
      · exact hpq h
      · exact hp (hRS h)
    rw [hE', card_insert_of_notMem hpR, card_insert_of_notMem hqR]
    have a1 := card_erase_add_one hu
    have a2 := card_erase_add_one (mem_erase.2 ⟨huw.symm, hw⟩)
    omega
  refine ⟨E', ?_, fun h => hp (h ▸ (hmem _).2 (Or.inl rfl)), ?_⟩
  · rw [mem_strongPi]
    simp only [proj]
    exact ⟨cE, (mem_strongPi.1 hS).2⟩
  · ext x
    rw [mem_inter, hmem]
    constructor
    · rintro ⟨hx, rfl | rfl | hx'⟩
      · exact absurd hx hp
      · exact absurd hx hq
      · exact hx'
    · intro hx
      exact ⟨hRS hx, Or.inr (Or.inr hx)⟩

lemma tc_line_iff (hr : 4 ≤ r) (hX : ∀ i, Uniform r (X i)) (c : ∀ i, V i) (i : ι)
    {e : Finset (V i)} (he : e ∈ (X i).E) :
    TC (strongPi r X) (e.image (update c i)) ↔ TC (X i) e := by
  have hinj : Injective (update c i) := update_injective c i
  have hLi : Injective fun f : Finset (V i) => f.image (update c i) := image_injective hinj
  constructor
  · intro ht a ha a' ha' haa
    obtain ⟨E', hE', hne, hint⟩ := ht _ (mem_image_of_mem _ ha) _ (mem_image_of_mem _ ha')
      (fun h => haa (hinj h))
    have hcS : (e.image (update c i)).card = r := by
      rw [card_image_of_injective _ hinj, hX i e he]
    have cI : 1 < (e.image (update c i) ∩ E').card := by
      rw [hint]
      have a1 := card_erase_add_one (mem_image_of_mem (update c i) ha)
      have a2 := card_erase_add_one (s := (e.image (update c i)).erase (update c i a))
        (a := update c i a')
        (mem_erase.2 ⟨fun h => haa (hinj h).symm, mem_image_of_mem _ ha'⟩)
      omega
    obtain ⟨x1, hx1, x2, hx2, hx12⟩ := one_lt_card.1 cI
    rw [mem_inter] at hx1 hx2
    have hc' := (mem_strongPi.1 hE').1
    -- in `L e`, points agree off coordinate `i`
    have agree : ∀ j ≠ i, x1 j = x2 j := by
      intro j hj
      obtain ⟨b1, -, rfl⟩ := mem_image.1 hx1.1
      obtain ⟨b2, -, rfl⟩ := mem_image.1 hx2.1
      rw [update_of_ne hj, update_of_ne hj]
    have hsing : ∀ j ≠ i, (E'.image fun x => x j).card = 1 := by
      intro j hj
      rcases (mem_strongPi.1 hE').2.1 j with h | h
      · exact h
      · exact absurd (injOn_of_card_image_eq (s := E') (by rw [hX j _ h, hc'])
          hx1.2 hx2.2 (agree j hj)) hx12
    have hE'line := eq_line hsing hx1.2
    -- the base point of `E'` agrees with `c` off `i`
    have hbase : update x1 i = update c i := by
      obtain ⟨b1, -, rfl⟩ := mem_image.1 hx1.1
      funext v k
      by_cases hk : k = i
      · subst hk; simp
      · simp [update_of_ne hk]
    rw [hbase] at hE'line
    set e' := E'.image fun x => x i
    have he' : e' ∈ (X i).E := by
      rw [hE'line] at hE'
      exact (mem_strongPi_line (by omega) hX c i e').1 hE'
    refine ⟨e', he', fun h => hne (by rw [hE'line, h]), hLi ?_⟩
    change (e ∩ e').image (update c i) = ((e.erase a).erase a').image (update c i)
    rw [image_inter _ _ hinj, image_erase hinj, image_erase hinj, ← hE'line]
    exact hint
  · intro ht u hu w hw huw
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
    obtain ⟨a', ha', rfl⟩ := mem_image.1 hw
    obtain ⟨e', he', hne, hint⟩ := ht a ha a' ha' (fun h => huw (h ▸ rfl))
    refine ⟨e'.image (update c i), (mem_strongPi_line (by omega) hX c i e').2 he', fun h => hne (hLi h), ?_⟩
    change e.image (update c i) ∩ e'.image (update c i) =
      ((e.image (update c i)).erase (update c i a)).erase (update c i a')
    rw [← image_inter _ _ hinj, hint, image_erase hinj, image_erase hinj]

/-- **Skeleton lemma for iterated products**: `Sk (⊠ᵢ Xᵢ) = □ᵢ Sk Xᵢ` for `r ≥ 4`. -/
theorem skeleton_pi (hr : 4 ≤ r) (hX : ∀ i, Uniform r (X i)) :
    (Sk (strongPi r X)).E = (boxPiH fun i => Sk (X i)).E := by
  ext S
  simp only [Sk, boxPiH, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hS, hn⟩
    obtain ⟨hc, hsoe, i, hi⟩ := mem_strongPi.1 hS
    have hsing : ∀ j ≠ i, (S.image fun x => x j).card = 1 := by
      intro j hj
      rcases hsoe j with h | h
      · exact h
      · exact absurd (tc_noncart_pi hX hS (Ne.symm hj) hi h) hn
    have hne : S.Nonempty := card_pos.1 (by omega)
    obtain ⟨x0, hx0⟩ := hne
    have hl := eq_line hsing hx0
    refine ⟨i, ⟨hi, fun ht => hn ?_⟩, hsing⟩
    rw [hl]; exact (tc_line_iff hr hX x0 i hi).2 ht
  · rintro ⟨i, ⟨hi, hn⟩, hsing⟩
    have hne : (S.image fun x => x i).Nonempty := card_pos.1 (by rw [hX i _ hi]; omega)
    obtain ⟨x0, hx0⟩ := hne.of_image
    have hl := eq_line hsing hx0
    rw [hl]
    exact ⟨(mem_strongPi_line (by omega) hX x0 i _).2 hi,
      fun ht => hn ((tc_line_iff hr hX x0 i hi).1 ht)⟩

end skeletonPi

/-! ## 2-sections and Cartesian products of graphs -/

/-- The 2-section `[H]₂`. -/
def twoSection {α : Type} (H : HG α) : SimpleGraph α where
  Adj u v := u ≠ v ∧ ∃ e ∈ H.E, u ∈ e ∧ v ∈ e
  symm := ⟨fun _ _ ⟨h, e, he, hu, hv⟩ => ⟨h.symm, e, he, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Cartesian product of an indexed family of graphs. -/
def boxPi {ι : Type} {V : ι → Type} (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (∀ i, V i) where
  Adj x y := ∃ i, (G i).Adj (x i) (y i) ∧ ∀ j ≠ i, x j = y j
  symm := ⟨fun _ _ ⟨i, h, h'⟩ => ⟨i, h.symm, fun j hj => (h' j hj).symm⟩⟩
  loopless := ⟨fun _ ⟨i, h, _⟩ => (G i).loopless.irrefl _ h⟩

lemma twoSection_congr {α : Type} {A B : HG α} (h : A.E = B.E) : twoSection A = twoSection B := by
  obtain ⟨EA⟩ := A
  obtain ⟨EB⟩ := B
  cases h
  rfl

lemma twoSection_adj_isoVia {α β : Type} [Fintype α] [Fintype β] {A : HG α} {B : HG β}
    {φ : α ≃ β} (h : IsoVia A B φ) (u v : α) :
    (twoSection A).Adj u v ↔ (twoSection B).Adj (φ u) (φ v) := by
  constructor
  · rintro ⟨huv, e, he, hu, hv⟩
    exact ⟨fun h => huv (φ.injective h), e.image φ, (h e).1 he, mem_image_of_mem _ hu,
      mem_image_of_mem _ hv⟩
  · rintro ⟨huv, e', he', hu, hv⟩
    refine ⟨fun h => huv (h ▸ rfl), e'.image φ.symm, (h _).2 (by rwa [image_image_equiv]),
      ?_, ?_⟩
    · exact mem_image.2 ⟨φ u, hu, by simp⟩
    · exact mem_image.2 ⟨φ v, hv, by simp⟩

lemma twoSection_boxPiH {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
    (Q : ∀ i, HG (V i)) (x y : ∀ i, V i) :
    (twoSection (boxPiH Q)).Adj x y ↔ (boxPi fun i => twoSection (Q i)).Adj x y := by
  constructor
  · rintro ⟨hxy, S, hS, hx, hy⟩
    simp only [boxPiH, mem_filter, mem_univ, true_and] at hS
    obtain ⟨i, hi, hsing⟩ := hS
    have hj : ∀ j ≠ i, x j = y j := fun j hj => eq_of_card_image_eq_one (hsing j hj) hx hy
    refine ⟨i, ⟨fun h => hxy (funext fun k => ?_), _, hi, mem_image_of_mem _ hx,
      mem_image_of_mem _ hy⟩, hj⟩
    by_cases hk : k = i
    · subst hk; exact h
    · exact hj k hk
  · rintro ⟨i, ⟨hxy, e, he, hx, hy⟩, hj⟩
    have hne : e.Nonempty := ⟨_, hx⟩
    have hyl : update x i (y i) = y := funext fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · rw [update_of_ne hk]; exact hj k hk
    refine ⟨fun h => hxy (h ▸ rfl), e.image (update x i), ?_, mem_image.2 ⟨x i, hx, by simp⟩,
      mem_image.2 ⟨y i, hy, hyl⟩⟩
    simp only [boxPiH, mem_filter, mem_univ, true_and]
    refine ⟨i, by rwa [image_update_proj_self], fun j hj => ?_⟩
    rw [image_update_proj_ne x hj hne, card_singleton]

/-- The 2-section of the skeleton of `H ≅ ⊠ₛ Pₛ` is `□ₛ [Sk Pₛ]₂`. -/
lemma adj_factorization (hr : 4 ≤ r) {V : Type} [Fintype V] {H : HG V} {S : Type} [Fintype S]
    {W : S → Type} [∀ s, Fintype (W s)] {P : ∀ s, HG (W s)} (hP : ∀ s, Uniform r (P s))
    {φ : (∀ s, W s) ≃ V} (hφ : IsoVia (strongPi r P) H φ) (x y : ∀ s, W s) :
    (twoSection (Sk H)).Adj (φ x) (φ y) ↔
      (boxPi fun s => twoSection (Sk (P s))).Adj x y := by
  rw [← twoSection_adj_isoVia (sk_isoVia hφ), ← twoSection_boxPiH]
  have : twoSection (Sk (strongPi r P)) = twoSection (boxPiH fun s => Sk (P s)) :=
    twoSection_congr (skeleton_pi hr hP)
  rw [this]

/-! ## The axiom -/

/-- **Axiom (unique coordinatization, packaged form).** Every connected finite graph `G` has a
coordinatization `ψ : V ≃ Π k, U k` with every `U k` nontrivial such that every Cartesian
factorization `φ : □ₛ Gₛ ≅ G` into nontrivial factors is a coarsening of it: there are a map
`σ : K → S` and bijections `αₛ : Wₛ ≃ Π_{σ k = s} U k` with `ψ (φ x) k = α_{σ k} (x_{σ k}) k`.

This is the standard consequence of Sabidussi–Vizing (existence and uniqueness of Cartesian
prime factorizations of connected graphs) together with the Imrich–Miller unique
coordinatization theorem (the paper's Theorem 3.4 / PDF Theorem 3.5). -/
axiom cartesian_coordinatization {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
  ∃ (K : Type) (_ : Fintype K) (U : K → Type) (_ : ∀ k, Fintype (U k)) (ψ : V ≃ ∀ k, U k),
    (∀ k, Nontrivial (U k)) ∧
    ∀ (S : Type) (_ : Fintype S) (W : S → Type) (_ : ∀ s, Fintype (W s))
      (Gs : ∀ s, SimpleGraph (W s)) (φ : (∀ s, W s) ≃ V),
      (∀ s, Nontrivial (W s)) → (∀ x y, G.Adj (φ x) (φ y) ↔ (boxPi Gs).Adj x y) →
      ∃ (σ : K → S) (α : ∀ s, W s ≃ ∀ k : {k // σ k = s}, U k),
        ∀ x k, ψ (φ x) k = α (σ k) (x (σ k)) ⟨k, rfl⟩

/-! ## Block decompositions in a fixed coordinatization -/

section decomp

variable {K : Type} [Fintype K] {U : K → Type} [∀ k, Fintype (U k)] (c : ∀ k, U k)

/-- Keep the coordinates in `B`, replace the others by those of the base point `c`. -/
def mix (B : K → Prop) (x : ∀ k, U k) : ∀ k, U k := fun k => if B k then x k else c k

/-- The shadow of `S` on the coordinates `B`. -/
def sh (B : K → Prop) (S : Finset (∀ k, U k)) : Finset (∀ k, U k) := S.image (mix c B)

/-- `H` is the strong product of its layers along the blocks of `σ` (Lemma 2.2 description). -/
def Decomp (H : HG (∀ k, U k)) (r : ℕ) {ι : Type} (σ : K → ι) : Prop :=
  ∀ S, S ∈ H.E ↔ S.card = r ∧ (∀ i, SoE H (sh c (fun k => σ k = i) S)) ∧
    ∃ i, sh c (fun k => σ k = i) S ∈ H.E

variable {c}

lemma sh_sh (B B' : K → Prop) (S : Finset (∀ k, U k)) :
    sh c B (sh c B' S) = sh c (fun k => B k ∧ B' k) S := by
  unfold sh
  rw [image_image]
  congr 1
  funext x k
  simp only [mix, comp_apply]
  by_cases hB : B k <;> by_cases hB' : B' k <;> simp [hB, hB']

lemma sh_congr {B B' : K → Prop} (h : ∀ k, B k ↔ B' k) (S : Finset (∀ k, U k)) :
    sh c B S = sh c B' S := by
  unfold sh
  congr 1
  funext x k
  simp only [mix, h]

lemma card_sh_le (B : K → Prop) (S : Finset (∀ k, U k)) : (sh c B S).card ≤ S.card :=
  card_image_le

lemma card_sh_empty {B : K → Prop} (hB : ∀ k, ¬ B k) {S : Finset (∀ k, U k)}
    (hS : S.Nonempty) : (sh c B S).card = 1 :=
  card_image_eq_one hS fun x _ x' _ => funext fun k => by simp [mix, hB k]

lemma card_sh_one {B : K → Prop} {S : Finset (∀ k, U k)} (hS : S.Nonempty)
    (h : ∀ x ∈ S, ∀ x' ∈ S, ∀ k, B k → x k = x' k) : (sh c B S).card = 1 :=
  card_image_eq_one hS fun x hx x' hx' => funext fun k => by
    simp only [mix]; split_ifs with hk
    · exact h x hx x' hx' k hk
    · rfl

lemma eq_of_card_sh_one {B : K → Prop} {S : Finset (∀ k, U k)} (h : (sh c B S).card = 1)
    {x x' : ∀ k, U k} (hx : x ∈ S) (hx' : x' ∈ S) {k : K} (hk : B k) : x k = x' k := by
  have := congrFun (eq_of_card_image_eq_one h hx hx') k
  simpa [mix, hk] using this

lemma card_sh_le_one_of {B B' : K → Prop} {S : Finset (∀ k, U k)}
    (h : (sh c B' S).card = 1) (hS : S.Nonempty) (hBB : ∀ k, B k → B' k) :
    (sh c B S).card = 1 :=
  card_sh_one hS fun x hx x' hx' k hk => eq_of_card_sh_one h hx hx' (hBB k hk)

variable {H : HG (∀ k, U k)}

lemma not_mem_of_card_one (hH : Uniform r H) (hr : 2 ≤ r) {T : Finset (∀ k, U k)}
    (h : T.card = 1) : T ∉ H.E := fun hT => by have := hH T hT; omega

/-- **Step 2**: decompositions are closed under common refinement. -/
theorem decomp_inf (hH : Uniform r H) (hr : 2 ≤ r) {ι κ : Type} {σ : K → ι} {τ : K → κ}
    (hσ : Decomp c H r σ) (hτ : Decomp c H r τ) :
    Decomp c H r fun k => (σ k, τ k) := by
  have blk : ∀ i j (S : Finset (∀ k, U k)), sh c (fun k => (σ k, τ k) = (i, j)) S =
      sh c (fun k => τ k = j) (sh c (fun k => σ k = i) S) := fun i j S => by
    rw [sh_sh]; exact sh_congr (fun k => by simp [Prod.mk.injEq, and_comm]) S
  -- if some sub-block shadow is an edge, the block shadow is an edge
  have up : ∀ (S : Finset (∀ k, U k)), S.card = r →
      (∀ p : ι × κ, SoE H (sh c (fun k => (σ k, τ k) = p) S)) →
      ∀ i j, sh c (fun k => (σ k, τ k) = (i, j)) S ∈ H.E →
      sh c (fun k => σ k = i) S ∈ H.E := by
    intro S hc h1 i j hij
    refine (hτ _).2 ⟨le_antisymm ((card_sh_le _ _).trans hc.le) ?_, fun j' => ?_, j, ?_⟩
    · rw [← hH _ hij, blk]; exact card_sh_le _ _
    · rw [← blk]; exact h1 (i, j')
    · rw [← blk]; exact hij
  intro S
  constructor
  · intro hS
    obtain ⟨hc, h1, i0, hi0⟩ := (hσ S).1 hS
    have hne : S.Nonempty := card_pos.1 (by omega)
    refine ⟨hc, fun ⟨i, j⟩ => ?_, ?_⟩
    · rw [blk]
      rcases h1 i with h | h
      · have hn : (sh c (fun k => σ k = i) S).Nonempty := card_pos.1 (by omega)
        exact Or.inl (le_antisymm (h ▸ card_sh_le _ _) (card_pos.2 (hn.image _)))
      · exact ((hτ _).1 h).2.1 j
    · obtain ⟨-, -, j0, hj0⟩ := (hτ _).1 hi0
      exact ⟨(i0, j0), by rw [blk]; exact hj0⟩
  · rintro ⟨hc, h1, ⟨i0, j0⟩, he⟩
    have hne : S.Nonempty := card_pos.1 (by omega)
    refine (hσ S).2 ⟨hc, fun i => ?_, i0, up S hc h1 i0 j0 he⟩
    by_cases hex : ∃ j, sh c (fun k => (σ k, τ k) = (i, j)) S ∈ H.E
    · obtain ⟨j, hj⟩ := hex
      exact Or.inr (up S hc h1 i j hj)
    · push_neg at hex
      refine Or.inl (card_sh_one hne fun x hx x' hx' k hk => ?_)
      have := (h1 (i, τ k)).resolve_right (hex (τ k))
      exact eq_of_card_sh_one this hx hx' (by simp [hk])

/-- Coarsening: a decomposition along `σ` is one along any `ρ` constant on `σ`-blocks. -/
theorem decomp_coarsen (hH : Uniform r H) (hr : 2 ≤ r) {ι κ : Type} {σ : K → ι} {ρ : K → κ}
    (hσ : Decomp c H r σ) (hρ : ∀ k k', σ k = σ k' → ρ k = ρ k') : Decomp c H r ρ := by
  have meet_in : ∀ i j (S : Finset (∀ k, U k)), (∃ k, σ k = i ∧ ρ k = j) →
      sh c (fun k => σ k = i) (sh c (fun k => ρ k = j) S) = sh c (fun k => σ k = i) S := by
    rintro i j S ⟨k, hk, hk'⟩
    rw [sh_sh]
    exact sh_congr (fun k' => ⟨fun h => h.1, fun h => ⟨h, (hρ k' k (h.trans hk.symm)).trans hk'⟩⟩) S
  have meet_out : ∀ i j (S : Finset (∀ k, U k)), ¬ (∃ k, σ k = i ∧ ρ k = j) → S.Nonempty →
      (sh c (fun k => σ k = i) (sh c (fun k => ρ k = j) S)).card = 1 := by
    intro i j S hno hne
    rw [sh_sh]
    exact card_sh_empty (fun k hk => hno ⟨k, hk⟩) hne
  have key_up : ∀ (S : Finset (∀ k, U k)), S.card = r →
      (∀ i, SoE H (sh c (fun k => σ k = i) S)) → ∀ j k, ρ k = j →
      sh c (fun k' => σ k' = σ k) S ∈ H.E → sh c (fun k => ρ k = j) S ∈ H.E := by
    intro S hc h1 j k hk he
    have hne : S.Nonempty := card_pos.1 (by omega)
    refine (hσ _).2 ⟨le_antisymm ((card_sh_le _ _).trans hc.le) ?_, fun i => ?_, σ k, ?_⟩
    · rw [← hH _ he, ← meet_in (σ k) j S ⟨k, rfl, hk⟩]; exact card_sh_le _ _
    · by_cases hex : ∃ k', σ k' = i ∧ ρ k' = j
      · rw [meet_in i j S hex]; exact h1 i
      · exact Or.inl (meet_out i j S hex hne)
    · rw [meet_in (σ k) j S ⟨k, rfl, hk⟩]; exact he
  intro S
  constructor
  · intro hS
    obtain ⟨hc, h1, i0, hi0⟩ := (hσ S).1 hS
    have hne : S.Nonempty := card_pos.1 (by omega)
    have hk0 : ∃ k, σ k = i0 := by
      by_contra hno
      push_neg at hno
      exact not_mem_of_card_one hH hr (card_sh_empty hno hne) hi0
    obtain ⟨k0, hk0⟩ := hk0
    refine ⟨hc, fun j => ?_, ρ k0, key_up S hc h1 (ρ k0) k0 rfl (by rw [hk0]; exact hi0)⟩
    by_cases hex : ∃ k, ρ k = j ∧ sh c (fun k' => σ k' = σ k) S ∈ H.E
    · obtain ⟨k, hk, he⟩ := hex
      exact Or.inr (key_up S hc h1 j k hk he)
    · push_neg at hex
      refine Or.inl (card_sh_one hne fun x hx x' hx' k hk => ?_)
      have := (h1 (σ k)).resolve_right (hex k hk)
      exact eq_of_card_sh_one this hx hx' rfl
  · rintro ⟨hc, h1, j0, hj0⟩
    have hne : S.Nonempty := card_pos.1 (by omega)
    refine (hσ S).2 ⟨hc, fun i => ?_, ?_⟩
    · by_cases hex : ∃ k, σ k = i
      · obtain ⟨k, hk⟩ := hex
        have hm := meet_in i (ρ k) S ⟨k, hk, rfl⟩
        rcases h1 (ρ k) with h | h
        · have hn : (sh c (fun k' => ρ k' = ρ k) S).Nonempty := card_pos.1 (by omega)
          left
          rw [← hm]
          exact le_antisymm (h ▸ card_sh_le _ _) (card_pos.2 (hn.image _))
        · rw [← hm]; exact ((hσ _).1 h).2.1 i
      · push_neg at hex
        exact Or.inl (card_sh_empty hex hne)
    · obtain ⟨-, -, i, hi⟩ := (hσ _).1 hj0
      refine ⟨i, ?_⟩
      by_cases hex : ∃ k, σ k = i ∧ ρ k = j0
      · rwa [meet_in i j0 S hex] at hi
      · exact absurd hi (not_mem_of_card_one hH hr (meet_out i j0 S hex hne))

end decomp

/-! ## Primes -/

/-- A hypergraph is prime for the strong product if it has at least two vertices and every
factorization `P ≅ X ⊠ Y` (into hypergraphs with nonempty edges) has a one-vertex factor. -/
def HGPrime {α : Type} [Fintype α] (P : HG α) : Prop :=
  2 ≤ Fintype.card α ∧ ∀ (β γ : Type) [Fintype β] [Fintype γ] (X : HG β) (Y : HG γ),
    (∀ e ∈ X.E, e.Nonempty) → (∀ e ∈ Y.E, e.Nonempty) → Iso P (strong X Y) →
    Fintype.card β ≤ 1 ∨ Fintype.card γ ≤ 1

/-! ## Step 1: a factorization gives a block decomposition -/

section transfer

variable {K : Type} [Fintype K] {U : K → Type} [∀ k, Fintype (U k)] {H : HG (∀ k, U k)}
  {S : Type} [Fintype S] {W : S → Type} [∀ s, Fintype (W s)] {P : ∀ s, HG (W s)}
  {Θ : (∀ s, W s) ≃ (∀ k, U k)} {σ : K → S} {α : ∀ s, W s ≃ ∀ k : {k // σ k = s}, U k}

lemma coord_eq (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (x : ∀ s, W s) (k : K) (s : S)
    (h : σ k = s) : Θ x k = α s (x s) ⟨k, h⟩ := by
  subst h; exact hΘ x k

lemma coord_update (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (x0 : ∀ s, W s) (s : S)
    (w : W s) (k : K) :
    Θ (update x0 s w) k = if h : σ k = s then α s w ⟨k, h⟩ else Θ x0 k := by
  split_ifs with h
  · rw [coord_eq hΘ _ k s h, update_self]
  · rw [hΘ, hΘ x0 k, update_of_ne h]

lemma mix_coord (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (x0 : ∀ s, W s) (s : S)
    (x : ∀ s, W s) : mix (Θ x0) (fun k => σ k = s) (Θ x) = Θ (update x0 s (x s)) := by
  funext k
  simp only [mix]
  rw [coord_update hΘ]
  split_ifs with h
  · exact coord_eq hΘ x k s h
  · rfl

lemma lift_mem (hr : 2 ≤ r) (hP : ∀ s, Uniform r (P s)) (hiso : IsoVia (strongPi r P) H Θ)
    (x0 : ∀ s, W s) (s : S) (e : Finset (W s)) :
    e.image (fun w => Θ (update x0 s w)) ∈ H.E ↔ e ∈ (P s).E := by
  have : e.image (fun w => Θ (update x0 s w)) = (e.image (update x0 s)).image Θ := by
    rw [image_image]; rfl
  rw [this, ← hiso, mem_strongPi_line hr hP]

/-- **Step 1** (paper): a factorization that is coordinatewise in the sense of the axiom
makes `H` decompose along the blocks of `σ`. -/
theorem decomp_of_factorization (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (hr : 2 ≤ r)
    (hP : ∀ s, Uniform r (P s)) (hiso : IsoVia (strongPi r P) H Θ) (x0 : ∀ s, W s) :
    Decomp (Θ x0) H r σ := by
  intro S'
  obtain ⟨S, rfl⟩ : ∃ S, S' = S.image Θ := ⟨S'.image Θ.symm, (image_image_equiv Θ S').symm⟩
  have hsh : ∀ s, sh (Θ x0) (fun k => σ k = s) (S.image Θ) =
      (S.image fun x => x s).image (fun w => Θ (update x0 s w)) := by
    intro s
    unfold sh
    rw [image_image, image_image]
    congr 1
    funext x
    exact mix_coord hΘ x0 s x
  have hinj : ∀ s, Injective fun w : W s => Θ (update x0 s w) :=
    fun s => Θ.injective.comp (update_injective x0 s)
  rw [← hiso S, mem_strongPi, card_image_of_injective _ Θ.injective]
  simp only [hsh, SoE, lift_mem hr hP hiso, card_image_of_injective _ (hinj _)]

/-! ## Step 3: a proper split of a block contradicts primality -/

/-- Embed a function on the coordinates `B` by filling the others from `c`. -/
def emb (c : ∀ k, U k) (B : K → Prop) (g : ∀ k : {k // B k}, U k) : ∀ k, U k :=
  fun k => if h : B k then g ⟨k, h⟩ else c k

/-- The layer of `H` on the coordinates `B` through `c`. -/
def layer (c : ∀ k, U k) (B : K → Prop) (H : HG (∀ k, U k)) : HG (∀ k : {k // B k}, U k) where
  E := univ.filter fun f => f.image (emb c B) ∈ H.E

lemma emb_injective (c : ∀ k, U k) (B : K → Prop) : Injective (emb c B) := by
  intro g g' h
  funext k
  have := congrFun h k.1
  simpa [emb, k.2] using this

lemma mem_layer {c : ∀ k, U k} {B : K → Prop} {f : Finset (∀ k : {k // B k}, U k)} :
    f ∈ (layer c B H).E ↔ f.image (emb c B) ∈ H.E := by
  simp only [layer, mem_filter, mem_univ, true_and]

lemma uniform_layer (hH : Uniform r H) (c : ∀ k, U k) (B : K → Prop) :
    Uniform r (layer c B H) := fun f hf => by
  rw [← card_image_of_injective _ (emb_injective c B)]; exact hH _ (mem_layer.1 hf)

lemma soe_layer {c : ∀ k, U k} {B : K → Prop} (f : Finset (∀ k : {k // B k}, U k)) :
    SoE (layer c B H) f ↔ SoE H (f.image (emb c B)) := by
  rw [SoE, SoE, mem_layer, card_image_of_injective _ (emb_injective c B)]

lemma forall_fin3 {p : Fin 3 → Prop} : (∀ j, p j) ↔ p 0 ∧ p 1 ∧ p 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨a, b, c⟩ j => by fin_cases j <;> assumption⟩

lemma exists_fin3 {p : Fin 3 → Prop} : (∃ j, p j) ↔ p 0 ∨ p 1 ∨ p 2 := by
  constructor
  · rintro ⟨j, h⟩
    fin_cases j
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

theorem not_prime_of_split (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (hr : 2 ≤ r)
    (hH : Uniform r H) (hP : ∀ s, Uniform r (P s)) (hiso : IsoVia (strongPi r P) H Θ)
    (x0 : ∀ s, W s) (hnt : ∀ k, Nontrivial (U k)) {s : S} {Bp : K → Prop}
    (hρ : Decomp (Θ x0) H r
      (fun k => if σ k = s ∧ Bp k then (0 : Fin 3) else if σ k = s then 1 else 2))
    {k1 k2 : K} (h1 : σ k1 = s ∧ Bp k1) (h2 : σ k2 = s ∧ ¬ Bp k2) : ¬ HGPrime (P s) := by
  intro hpr
  set c := Θ x0 with hc
  set B1 : K → Prop := fun k => σ k = s ∧ Bp k
  set B2 : K → Prop := fun k => σ k = s ∧ ¬ Bp k
  have b0 : ∀ k, ((if σ k = s ∧ Bp k then (0 : Fin 3) else if σ k = s then 1 else 2) = 0) ↔
      B1 k := fun k => by
    by_cases ha : σ k = s <;> by_cases hb : Bp k <;> simp [B1, ha, hb]
  have b1 : ∀ k, ((if σ k = s ∧ Bp k then (0 : Fin 3) else if σ k = s then 1 else 2) = 1) ↔
      B2 k := fun k => by
    by_cases ha : σ k = s <;> by_cases hb : Bp k <;> simp [B2, ha, hb]
  have b2 : ∀ k, ((if σ k = s ∧ Bp k then (0 : Fin 3) else if σ k = s then 1 else 2) = 2) ↔
      ¬ σ k = s := fun k => by
    by_cases ha : σ k = s <;> by_cases hb : Bp k <;> simp [ha, hb]
  -- the vertex bijection `W s ≃ (coordinates in B1) × (coordinates in B2)`
  let β : W s ≃ (∀ k : {k // B1 k}, U k) × (∀ k : {k // B2 k}, U k) :=
    { toFun := fun w => (fun k => Θ (update x0 s w) k.1, fun k => Θ (update x0 s w) k.1)
      invFun := fun p => (α s).symm fun k =>
        if hb : Bp k.1 then p.1 ⟨k.1, k.2, hb⟩ else p.2 ⟨k.1, k.2, hb⟩
      left_inv := fun w => by
        apply (α s).injective
        rw [Equiv.apply_symm_apply]
        funext k
        split_ifs <;> (dsimp only; rw [coord_update hΘ, dif_pos k.2])
      right_inv := fun p => by
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · change Θ (update x0 s _) k.1 = _
          rw [coord_update hΘ, dif_pos k.2.1, Equiv.apply_symm_apply, dif_pos k.2.2]
        · change Θ (update x0 s _) k.1 = _
          rw [coord_update hΘ, dif_pos k.2.1, Equiv.apply_symm_apply, dif_neg k.2.2] }
  have hinj : Injective fun w : W s => Θ (update x0 s w) :=
    Θ.injective.comp (update_injective x0 s)
  set X := layer c B1 H
  set Y := layer c B2 H
  have hX := uniform_layer hH c B1
  have hY := uniform_layer hH c B2
  have hiso' : IsoVia (P s) (strong X Y) β := by
    intro e
    set L := e.image fun w => Θ (update x0 s w)
    have sh1 : sh c (fun k => (if σ k = s ∧ Bp k then (0 : Fin 3) else
        if σ k = s then 1 else 2) = 0) L = ((e.image β).image Prod.fst).image (emb c B1) := by
      rw [sh_congr b0, sh, image_image, image_image, image_image]
      congr 1
    have sh2 : sh c (fun k => (if σ k = s ∧ Bp k then (0 : Fin 3) else
        if σ k = s then 1 else 2) = 1) L = ((e.image β).image Prod.snd).image (emb c B2) := by
      rw [sh_congr b1, sh, image_image, image_image, image_image]
      congr 1
    have sh3 : L.Nonempty → (sh c (fun k => (if σ k = s ∧ Bp k then (0 : Fin 3) else
        if σ k = s then 1 else 2) = 2) L).card = 1 := fun hne => by
      rw [sh_congr b2]
      refine card_sh_one hne fun x hx x' hx' k hk => ?_
      obtain ⟨w, -, rfl⟩ := mem_image.1 hx
      obtain ⟨w', -, rfl⟩ := mem_image.1 hx'
      rw [coord_update hΘ, coord_update hΘ, dif_neg hk, dif_neg hk]
    have hcL : (e.image β).card = L.card := by
      rw [card_image_of_injective _ β.injective, card_image_of_injective _ hinj]
    rw [← lift_mem hr hP hiso x0 s e, hρ L, forall_fin3, exists_fin3, sh1, sh2,
      mem_strong_uniform hX hY, soe_layer, soe_layer, mem_layer, mem_layer, hcL]
    constructor
    · rintro ⟨hc', ⟨s1, s2, -⟩, h | h | h⟩
      · exact ⟨hc', s1, s2, Or.inl h⟩
      · exact ⟨hc', s1, s2, Or.inr h⟩
      · exact absurd h (not_mem_of_card_one hH hr (sh3 (card_pos.1 (by omega))))
    · rintro ⟨hc', s1, s2, h⟩
      refine ⟨hc', ⟨s1, s2, Or.inl (sh3 (card_pos.1 (by omega)))⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hne : ∀ {B : K → Prop}, Uniform r (layer c B H) → ∀ e ∈ (layer c B H).E, e.Nonempty :=
    fun hu e he => card_pos.1 (by rw [hu e he]; omega)
  have n1 : 1 < Fintype.card (∀ k : {k // B1 k}, U k) := by
    haveI : Nontrivial (∀ k : {k // B1 k}, U k) :=
      Pi.nontrivial_at (f := fun k : {k // B1 k} => U k.1) ⟨k1, h1⟩
    exact Fintype.one_lt_card
  have n2 : 1 < Fintype.card (∀ k : {k // B2 k}, U k) := by
    haveI : Nontrivial (∀ k : {k // B2 k}, U k) :=
      Pi.nontrivial_at (f := fun k : {k // B2 k} => U k.1) ⟨k2, h2⟩
    exact Fintype.one_lt_card
  rcases hpr.2 _ _ X Y (hne hX) (hne hY) hiso'.iso with h | h <;> omega

/-- Blocks of a prime factorization are not split by any other decomposition. -/
theorem fibers_refine (hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩) (hr : 2 ≤ r)
    (hH : Uniform r H) (hP : ∀ s, Uniform r (P s)) (hpr : ∀ s, HGPrime (P s))
    (hiso : IsoVia (strongPi r P) H Θ) (x0 : ∀ s, W s) (hnt : ∀ k, Nontrivial (U k))
    {T : Type} {τ : K → T} (hτ : Decomp (Θ x0) H r τ) :
    ∀ k k', σ k = σ k' → τ k = τ k' := by
  intro k k' hkk
  by_contra hne
  have hσ := decomp_of_factorization hΘ hr hP hiso x0
  have hm := decomp_inf hH hr hσ hτ
  have hρ := decomp_coarsen hH hr hm (ρ := fun k'' =>
      if σ k'' = σ k ∧ τ k'' = τ k then (0 : Fin 3) else if σ k'' = σ k then 1 else 2)
    (fun a b hab => by
      simp only [Prod.mk.injEq] at hab
      simp only [hab.1, hab.2])
  exact not_prime_of_split hΘ hr hH hP hiso x0 hnt (Bp := fun k'' => τ k'' = τ k) hρ
    ⟨rfl, rfl⟩ ⟨hkk.symm, fun h => hne h.symm⟩ (hpr _)

end transfer

/-! ## Unique prime factorization -/

lemma iso_strong_congr {α α' γ γ' : Type} [Fintype α] [Fintype α'] [Fintype γ] [Fintype γ']
    {A : HG α} {A' : HG α'} {B : HG γ} {B' : HG γ'} (h1 : Iso A A') (h2 : Iso B B') :
    Iso (strong A B) (strong A' B') := by
  obtain ⟨φ1, h1⟩ := h1
  obtain ⟨φ2, h2⟩ := h2
  refine ⟨Equiv.prodCongr φ1 φ2, fun S => ?_⟩
  have p1 : (S.image (Equiv.prodCongr φ1 φ2)).image Prod.fst = (S.image Prod.fst).image φ1 := by
    rw [image_image, image_image]; rfl
  have p2 : (S.image (Equiv.prodCongr φ1 φ2)).image Prod.snd = (S.image Prod.snd).image φ2 := by
    rw [image_image, image_image]; rfl
  simp only [strong, mem_filter, mem_univ, true_and]
  rw [p1, p2, card_image_of_injective _ φ1.injective, card_image_of_injective _ φ2.injective,
    card_image_of_injective _ (Equiv.injective _), ← h1, ← h2]

/-- **Existence** of a prime factorization into `r`-uniform factors. -/
theorem upf_exists (hr : 2 ≤ r) : ∀ (n : ℕ) (V : Type) [Fintype V] (H : HG V),
    Fintype.card V = n → 1 ≤ n → Uniform r H →
    ∃ (S : Type) (_ : Fintype S) (W : S → Type) (_ : ∀ s, Fintype (W s))
      (P : ∀ s, HG (W s)), (∀ s, HGPrime (P s)) ∧ (∀ s, Uniform r (P s)) ∧
        Iso (strongPi r P) H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ H hn h1 hH
    by_cases hn1 : n = 1
    · subst hn1
      have hcard : Fintype.card (∀ _ : Empty, Unit) = Fintype.card V := by simp [hn]
      refine ⟨Empty, inferInstance, fun _ => Unit, fun _ => inferInstance,
        fun s => isEmptyElim s, fun s => isEmptyElim s, fun s => isEmptyElim s,
        Fintype.equivOfCardEq hcard, fun t => ⟨fun h => absurd h (strongPi_empty _ _),
          fun h => ?_⟩⟩
      have := hH _ h
      have := card_le_univ (t.image (Fintype.equivOfCardEq hcard))
      omega
    by_cases hp : HGPrime H
    · exact ⟨Unit, inferInstance, fun _ => V, fun _ => inferInstance, fun _ => H,
        fun _ => hp, fun _ => hH, ⟨_, iso_strongPi_unique (V := fun _ : Unit => V) fun _ => hH⟩⟩
    · have hnp : ¬ ∀ (β γ : Type) [Fintype β] [Fintype γ] (X : HG β) (Y : HG γ),
          (∀ e ∈ X.E, e.Nonempty) → (∀ e ∈ Y.E, e.Nonempty) → Iso H (strong X Y) →
          Fintype.card β ≤ 1 ∨ Fintype.card γ ≤ 1 := fun h => hp ⟨by omega, h⟩
      push_neg at hnp
      obtain ⟨β, γ, iβ, iγ, X, Y, hXn, hYn, hiso, cβ, cγ⟩ := hnp
      have hcard : n = Fintype.card β * Fintype.card γ := by
        obtain ⟨φ, -⟩ := hiso
        rw [← hn, Fintype.card_congr φ, Fintype.card_prod]
      have lβ : Fintype.card β * 2 ≤ n := hcard ▸ Nat.mul_le_mul_left _ cγ
      have lγ : 2 * Fintype.card γ ≤ n := hcard ▸ Nat.mul_le_mul_right _ cβ
      haveI : Nonempty β := Fintype.card_pos_iff.1 (by omega)
      haveI : Nonempty γ := Fintype.card_pos_iff.1 (by omega)
      have hXu := uniform_left_of_iso hH hiso hXn
      have hYu := uniform_right_of_iso hH hiso hYn
      obtain ⟨S1, i1, W1, iW1, P1, hp1, hu1, hiso1⟩ :=
        ih (Fintype.card β) (by omega) β X rfl (by omega) hXu
      obtain ⟨S2, i2, W2, iW2, P2, hp2, hu2, hiso2⟩ :=
        ih (Fintype.card γ) (by omega) γ Y rfl (by omega) hYu
      let W : S1 ⊕ S2 → Type := Sum.elim W1 W2
      let iW : ∀ i, Fintype (W i) := fun i => Sum.rec (motive := fun i => Fintype (W i)) iW1 iW2 i
      let P : ∀ i, HG (W i) := fun i => Sum.rec (motive := fun i => HG (W i)) P1 P2 i
      have hu : ∀ i, Uniform r (P i) := by rintro (a | b); exacts [hu1 a, hu2 b]
      refine ⟨S1 ⊕ S2, inferInstance, W, iW, P, by rintro (a | b); exacts [hp1 a, hp2 b], hu, ?_⟩
      exact ((iso_strongPi_sum (by omega) hu).iso.trans' (iso_strong_congr hiso1 hiso2)).trans'
        (Iso.symm' hiso)

/-- **Uniqueness** of prime factorizations (paper's Theorem 3.5, uniqueness part). -/
theorem upf_unique (hr : 4 ≤ r) {V : Type} [Fintype V] {H : HG V} (hH : Uniform r H)
    (hsk : (twoSection (Sk H)).Connected)
    {S T : Type} [Fintype S] [Fintype T] {W : S → Type} {W' : T → Type}
    [∀ s, Fintype (W s)] [∀ t, Fintype (W' t)] {P : ∀ s, HG (W s)} {P' : ∀ t, HG (W' t)}
    (hP : ∀ s, Uniform r (P s)) (hP' : ∀ t, Uniform r (P' t))
    (hpr : ∀ s, HGPrime (P s)) (hpr' : ∀ t, HGPrime (P' t))
    (h1 : Iso (strongPi r P) H) (h2 : Iso (strongPi r P') H) :
    ∃ π : S ≃ T, ∀ s, Iso (P s) (P' (π s)) := by
  obtain ⟨φ, hφ⟩ := h1
  obtain ⟨φ', hφ'⟩ := h2
  obtain ⟨K, iK, U, iU, ψ, hU, hax⟩ := cartesian_coordinatization _ hsk
  have ntW : ∀ s, Nontrivial (W s) := fun s => Fintype.one_lt_card_iff_nontrivial.1 (hpr s).1
  have ntW' : ∀ t, Nontrivial (W' t) :=
    fun t => Fintype.one_lt_card_iff_nontrivial.1 (hpr' t).1
  obtain ⟨σ, α, hσ⟩ := hax S inferInstance W inferInstance _ φ ntW (adj_factorization hr hP hφ)
  obtain ⟨τ, α', hτ⟩ := hax T inferInstance W' inferInstance _ φ' ntW' (adj_factorization hr hP' hφ')
  let H' : HG (∀ k, U k) := ⟨H.E.image fun e => e.image ψ⟩
  have hψ : IsoVia H H' ψ := fun s =>
    ⟨fun h => mem_image_of_mem _ h, fun h => by
      obtain ⟨t, ht, he⟩ := mem_image.1 h
      rwa [← image_injective ψ.injective he]⟩
  have hH' : Uniform r H' := fun e he => by
    obtain ⟨t, ht, rfl⟩ := mem_image.1 he
    rw [card_image_of_injective _ ψ.injective]; exact hH t ht
  let Θ := φ.trans ψ
  let Θ' := φ'.trans ψ
  have hΘ : ∀ x k, Θ x k = α (σ k) (x (σ k)) ⟨k, rfl⟩ := hσ
  have hΘ' : ∀ x k, Θ' x k = α' (τ k) (x (τ k)) ⟨k, rfl⟩ := hτ
  have hiso : IsoVia (strongPi r P) H' Θ := fun s => by rw [hφ, hψ, image_image]; rfl
  have hiso' : IsoVia (strongPi r P') H' Θ' := fun s => by rw [hφ', hψ, image_image]; rfl
  let x0 : ∀ s, W s := fun s => Classical.arbitrary _
  let x0' : ∀ t, W' t := Θ'.symm (Θ x0)
  have hc' : Θ' x0' = Θ x0 := Θ'.apply_symm_apply _
  have hDσ := decomp_of_factorization hΘ (by omega) hP hiso x0
  have hDτ : Decomp (Θ x0) H' r τ := hc' ▸ decomp_of_factorization hΘ' (by omega) hP' hiso' x0'
  have A := fibers_refine hΘ (by omega) hH' hP hpr hiso x0 hU hDτ
  have B := fibers_refine hΘ' (by omega) hH' hP' hpr' hiso' x0' hU (hc'.symm ▸ hDσ)
  have neσ : ∀ s, ∃ k, σ k = s := fun s => by
    by_contra hno
    push_neg at hno
    obtain ⟨a, b, hab⟩ := (ntW s).exists_pair_ne
    exact hab ((α s).injective (funext fun k => absurd k.2 (hno k.1)))
  have neτ : ∀ t, ∃ k, τ k = t := fun t => by
    by_contra hno
    push_neg at hno
    obtain ⟨a, b, hab⟩ := (ntW' t).exists_pair_ne
    exact hab ((α' t).injective (funext fun k => absurd k.2 (hno k.1)))
  choose kσ hkσ using neσ
  choose kτ hkτ using neτ
  let π : S ≃ T :=
    { toFun := fun s => τ (kσ s)
      invFun := fun t => σ (kτ t)
      left_inv := fun s => (B _ _ (hkτ _)).trans (hkσ s)
      right_inv := fun t => (A _ _ (hkσ _)).trans (hkτ t) }
  have hτσ : ∀ k, τ k = π (σ k) := fun k => A k (kσ (σ k)) (hkσ (σ k)).symm
  have hiff : ∀ s k, σ k = s ↔ τ k = π s := fun s k =>
    ⟨fun h => h ▸ hτσ k, fun h => π.injective ((hτσ k).symm.trans h)⟩
  refine ⟨π, fun s => ?_⟩
  let blk : (∀ k : {k // σ k = s}, U k) ≃ (∀ k : {k // τ k = π s}, U k) :=
    { toFun := fun f k => f ⟨k.1, (hiff s k.1).2 k.2⟩
      invFun := fun g k => g ⟨k.1, (hiff s k.1).1 k.2⟩
      left_inv := fun f => rfl
      right_inv := fun g => rfl }
  let γ : W s ≃ W' (π s) := (α s).trans (blk.trans (α' (π s)).symm)
  refine ⟨γ, fun e => ?_⟩
  rw [← lift_mem (by omega) hP hiso x0 s e,
    ← lift_mem (by omega) hP' hiso' x0' (π s) (e.image γ), image_image]
  have : (fun w => Θ (update x0 s w)) = (fun w' => Θ' (update x0' (π s) w')) ∘ γ := by
    funext w k
    simp only [comp_apply]
    rw [coord_update hΘ, coord_update hΘ']
    by_cases h : σ k = s
    · rw [dif_pos h, dif_pos ((hiff s k).1 h)]
      simp [γ, blk]
    · rw [dif_neg h, dif_neg (fun h' => h ((hiff s k).2 h')), hc']
  rw [this]

/-- **Unique prime factorization** (paper's Theorem 3.5; PDF Theorem 3.6). Let `r ≥ 4` and let
`H` be `r`-uniform with connected skeleton. Then `H` is a strong product of `r`-uniform primes,
and any two such factorizations agree up to a bijection of the factors and isomorphism.
Depends on the axiom `cartesian_coordinatization`. -/
theorem unique_prime_factorization (hr : 4 ≤ r) {V : Type} [Fintype V] {H : HG V}
    (hH : Uniform r H) (hsk : (twoSection (Sk H)).Connected) :
    (∃ (S : Type) (_ : Fintype S) (W : S → Type) (_ : ∀ s, Fintype (W s))
      (P : ∀ s, HG (W s)), (∀ s, HGPrime (P s)) ∧ (∀ s, Uniform r (P s)) ∧
        Iso (strongPi r P) H) ∧
    ∀ (S T : Type) [Fintype S] [Fintype T] (W : S → Type) (W' : T → Type)
      [∀ s, Fintype (W s)] [∀ t, Fintype (W' t)] (P : ∀ s, HG (W s)) (P' : ∀ t, HG (W' t)),
      (∀ s, HGPrime (P s)) → (∀ t, HGPrime (P' t)) →
      (∀ s, Uniform r (P s)) → (∀ t, Uniform r (P' t)) →
      Iso (strongPi r P) H → Iso (strongPi r P') H →
      ∃ π : S ≃ T, ∀ s, Iso (P s) (P' (π s)) := by
  haveI := hsk.nonempty
  refine ⟨upf_exists (by omega) _ V H rfl Fintype.card_pos hH, ?_⟩
  intro S T _ _ W W' _ _ P P' hp hp' hu hu' h1 h2
  exact upf_unique hr hH hsk hu hu' hp hp' h1 h2

end HypProd
