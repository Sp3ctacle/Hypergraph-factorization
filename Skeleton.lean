/-
# The intersection skeleton and the skeleton lemma

Definition 3.3 and Lemma 3.4 of *Unique factorization and cancellation for products of
uniform hypergraphs*:

* `TC H E`  : the edge `E` of `H` is transposition-complete.
* `Sk H`    : the skeleton, i.e. the edges of `H` that are not transposition-complete.
* `box X Y` : the Cartesian product `X □ Y` (edges `e × {y}` and `{x} × f`).
* `skeleton`: for `r ≥ 4` and `r`-uniform `X`, `Y`, `Sk (X ⊠ Y) = Sk X □ Sk Y`.
-/
import Hg.HypergraphCancellation3

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

variable {α γ : Type} [Fintype α] [Fintype γ]

/-- `E` is transposition-complete in `H` (Definition 3.3). -/
def TC [DecidableEq α] (H : HG α) (E : Finset α) : Prop :=
  ∀ u ∈ E, ∀ w ∈ E, u ≠ w → ∃ E' ∈ H.E, E' ≠ E ∧ E ∩ E' = (E.erase u).erase w

/-- The intersection skeleton (Definition 3.3). -/
def Sk [DecidableEq α] (H : HG α) : HG α where
  E := H.E.filter fun E => ¬ TC H E

/-- Cartesian product: one projection an edge, the other a singleton. -/
def box (X : HG α) (Y : HG γ) : HG (α × γ) where
  E := univ.filter fun S =>
    (S.image Prod.fst ∈ X.E ∧ (S.image Prod.snd).card = 1) ∨
    ((S.image Prod.fst).card = 1 ∧ S.image Prod.snd ∈ Y.E)

/-! ## Helpers -/

lemma snd_const {S : Finset (α × γ)} (h : (S.image Prod.snd).card = 1) :
    ∃ y, ∀ x ∈ S, x.2 = y := by
  obtain ⟨y, hy⟩ := card_eq_one.1 h
  refine ⟨y, fun x hx => ?_⟩
  have := mem_image_of_mem Prod.snd hx
  rwa [hy, mem_singleton] at this

lemma fst_const {S : Finset (α × γ)} (h : (S.image Prod.fst).card = 1) :
    ∃ a, ∀ x ∈ S, x.1 = a := by
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  refine ⟨a, fun x hx => ?_⟩
  have := mem_image_of_mem Prod.fst hx
  rwa [ha, mem_singleton] at this

lemma mem_iff_of_snd {S : Finset (α × γ)} {y : γ} (hy : ∀ x ∈ S, x.2 = y) (x : α × γ) :
    x ∈ S ↔ x.1 ∈ S.image Prod.fst ∧ x.2 = y := by
  refine ⟨fun hx => ⟨mem_image_of_mem _ hx, hy x hx⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨x', hx', h⟩ := mem_image.1 h1
  rwa [← Prod.ext h ((hy x' hx').trans h2.symm)]

lemma mem_iff_of_fst {S : Finset (α × γ)} {a : α} (ha : ∀ x ∈ S, x.1 = a) (x : α × γ) :
    x ∈ S ↔ x.1 = a ∧ x.2 ∈ S.image Prod.snd := by
  refine ⟨fun hx => ⟨ha x hx, mem_image_of_mem _ hx⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨x', hx', h⟩ := mem_image.1 h2
  rwa [← Prod.ext ((ha x' hx').trans h1.symm) h]

lemma mem_image_mk_right {e : Finset α} {y : γ} {x : α × γ} :
    x ∈ e.image (fun a => (a, y)) ↔ x.1 ∈ e ∧ x.2 = y := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 h
    exact ⟨ha, rfl⟩
  · rintro ⟨h1, h2⟩
    exact mem_image.2 ⟨x.1, h1, Prod.ext rfl h2.symm⟩

lemma mem_image_mk_left {f : Finset γ} {a : α} {x : α × γ} :
    x ∈ f.image (fun b => (a, b)) ↔ x.1 = a ∧ x.2 ∈ f := by
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := mem_image.1 h
    exact ⟨rfl, hb⟩
  · rintro ⟨h1, h2⟩
    exact mem_image.2 ⟨x.2, h2, Prod.ext h1.symm rfl⟩

variable {r : ℕ} {X : HG α} {Y : HG γ}

/-- Edges of the strong product of `r`-uniform hypergraphs have `r` elements. -/
lemma card_mem_strong (hX : Uniform r X) (hY : Uniform r Y) {S : Finset (α × γ)}
    (hS : S ∈ (strong X Y).E) : S.card = r := by
  simp only [strong, mem_filter, mem_univ, true_and] at hS
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, hc⟩
  · obtain ⟨y, hy⟩ := snd_const h2
    rw [← hX _ h1, card_image_of_injOn fun x hx x' hx' h =>
      Prod.ext h ((hy x hx).trans (hy x' hx').symm)]
  · obtain ⟨a, ha⟩ := fst_const h1
    rw [← hY _ h2, card_image_of_injOn fun x hx x' hx' h =>
      Prod.ext ((ha x hx).trans (ha x' hx').symm) h]
  · rw [hc, hX _ h1, hY _ h2, max_self]

/-! ## Non-Cartesian edges are transposition-complete -/

lemma tc_noncart (hX : Uniform r X) (hY : Uniform r Y) {S : Finset (α × γ)}
    (h1 : S.image Prod.fst ∈ X.E) (h2 : S.image Prod.snd ∈ Y.E) (hc : S.card = r) :
    TC (strong X Y) S := by
  have i1 : Set.InjOn Prod.fst (S : Set (α × γ)) := injOn_of_card_image_eq (s := S) (by rw [hX _ h1, hc])
  have i2 : Set.InjOn Prod.snd (S : Set (α × γ)) := injOn_of_card_image_eq (s := S) (by rw [hY _ h2, hc])
  intro u hu w hw huw
  have d1 : u.1 ≠ w.1 := fun h => huw (i1 hu hw h)
  have d2 : u.2 ≠ w.2 := fun h => huw (i2 hu hw h)
  have hp : ((u.1, w.2) : α × γ) ∉ S := fun h => d2 (by have := congrArg Prod.snd (i1 hu h rfl : u = (u.1, w.2)); exact this)
  have hq : ((w.1, u.2) : α × γ) ∉ S := fun h => d2 (by have := congrArg Prod.snd (i1 hw h rfl : w = (w.1, u.2)); exact this.symm)
  have hpq : ((u.1, w.2) : α × γ) ≠ (w.1, u.2) := fun h => d1 (by have := congrArg Prod.fst h; exact this)
  have hRS : (S.erase u).erase w ⊆ S := (erase_subset _ _).trans (erase_subset _ _)
  have hR : ∀ x, x ∈ (S.erase u).erase w ↔ x ≠ w ∧ x ≠ u ∧ x ∈ S := fun x => by
    simp only [mem_erase]
  set E' : Finset (α × γ) := insert (u.1, w.2) (insert (w.1, u.2) ((S.erase u).erase w))
    with hE'
  have hmem : ∀ x, x ∈ E' ↔ x = (u.1, w.2) ∨ x = (w.1, u.2) ∨ x ∈ (S.erase u).erase w :=
    fun x => by simp only [hE', mem_insert]
  have f1 : E'.image Prod.fst = S.image Prod.fst := by
    ext z
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (hmem x).1 hx with rfl | rfl | hx
      · exact ⟨u, hu, rfl⟩
      · exact ⟨w, hw, rfl⟩
      · exact ⟨x, hRS hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hxu : x = u
      · exact ⟨(u.1, w.2), (hmem _).2 (Or.inl rfl), by rw [hxu]⟩
      by_cases hxw : x = w
      · exact ⟨(w.1, u.2), (hmem _).2 (Or.inr (Or.inl rfl)), by rw [hxw]⟩
      exact ⟨x, (hmem _).2 (Or.inr (Or.inr ((hR x).2 ⟨hxw, hxu, hx⟩))), rfl⟩
  have f2 : E'.image Prod.snd = S.image Prod.snd := by
    ext z
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (hmem x).1 hx with rfl | rfl | hx
      · exact ⟨w, hw, rfl⟩
      · exact ⟨u, hu, rfl⟩
      · exact ⟨x, hRS hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hxu : x = u
      · exact ⟨(w.1, u.2), (hmem _).2 (Or.inr (Or.inl rfl)), by rw [hxu]⟩
      by_cases hxw : x = w
      · exact ⟨(u.1, w.2), (hmem _).2 (Or.inl rfl), by rw [hxw]⟩
      exact ⟨x, (hmem _).2 (Or.inr (Or.inr ((hR x).2 ⟨hxw, hxu, hx⟩))), rfl⟩
  have cE : E'.card = r := by
    have hqR : ((w.1, u.2) : α × γ) ∉ (S.erase u).erase w := fun h => hq (hRS h)
    have hpR : ((u.1, w.2) : α × γ) ∉ insert (w.1, u.2) ((S.erase u).erase w) := by
      rw [mem_insert]
      rintro (h | h)
      · exact hpq h
      · exact hp (hRS h)
    rw [hE', card_insert_of_notMem hpR, card_insert_of_notMem hqR]
    have a1 := card_erase_add_one hu
    have a2 := card_erase_add_one (mem_erase.2 ⟨huw.symm, hw⟩)
    omega
  refine ⟨E', ?_, fun h => hp (h ▸ (hmem _).2 (Or.inl rfl)), ?_⟩
  · simp only [strong, mem_filter, mem_univ, true_and]
    right; right
    rw [f1, f2]
    exact ⟨h1, h2, by rw [cE, hX _ h1, hY _ h2, max_self]⟩
  · ext x
    rw [mem_inter, hmem]
    constructor
    · rintro ⟨hx, rfl | rfl | hx'⟩
      · exact absurd hx hp
      · exact absurd hx hq
      · exact hx'
    · intro hx
      exact ⟨hRS hx, Or.inr (Or.inr hx)⟩

/-! ## Cartesian edges -/

/-- An edge `e × {y}` is transposition-complete in `X ⊠ Y` iff `e` is in `X`. -/
lemma tc_cart_snd (hr : 4 ≤ r) (hX : Uniform r X) (hY : Uniform r Y) {S : Finset (α × γ)}
    (h1 : S.image Prod.fst ∈ X.E) (h2 : (S.image Prod.snd).card = 1) :
    TC (strong X Y) S ↔ TC X (S.image Prod.fst) := by
  obtain ⟨y, hy⟩ := snd_const h2
  have hS := mem_iff_of_snd hy
  constructor
  · intro ht a ha a' ha' haa
    have hu : (a, y) ∈ S := (hS _).2 ⟨ha, rfl⟩
    have hw : (a', y) ∈ S := (hS _).2 ⟨ha', rfl⟩
    obtain ⟨E', hE', hne, hint⟩ := ht _ hu _ hw (fun h => haa (congrArg Prod.fst h))
    have cS : S.card = r := (card_image_of_injOn fun x hx x' hx' h =>
      Prod.ext h ((hy x hx).trans (hy x' hx').symm)).symm.trans (hX _ h1)
    have cI : 1 < (S ∩ E').card := by
      rw [hint]
      have a1 := card_erase_add_one hu
      have a2 := card_erase_add_one
        (mem_erase.2 ⟨fun (h : ((a', y) : α × γ) = (a, y)) => haa (congrArg Prod.fst h).symm, hw⟩)
      omega
    obtain ⟨x1, hx1, x2, hx2, hx12⟩ := one_lt_card.1 cI
    rw [mem_inter] at hx1 hx2
    have hnot : E'.image Prod.snd ∉ Y.E := fun hm =>
      hx12 (injOn_of_card_image_eq (by rw [hY _ hm, card_mem_strong hX hY hE'])
        hx1.2 hx2.2 ((hy _ hx1.1).trans (hy _ hx2.1).symm))
    obtain ⟨g1, g2⟩ : E'.image Prod.fst ∈ X.E ∧ (E'.image Prod.snd).card = 1 := by
      simp only [strong, mem_filter, mem_univ, true_and] at hE'
      rcases hE' with h | ⟨-, h⟩ | ⟨-, h, -⟩
      · exact h
      · exact absurd h hnot
      · exact absurd h hnot
    obtain ⟨y', hy'⟩ := snd_const g2
    have hE'm := mem_iff_of_snd fun x hx =>
      (hy' x hx).trans ((hy' _ hx1.2).symm.trans (hy _ hx1.1))
    refine ⟨E'.image Prod.fst, g1, fun h => hne (ext fun x => by rw [hE'm, hS, h]), ?_⟩
    ext b
    have key := Finset.ext_iff.1 hint (b, y)
    simp only [mem_inter, mem_erase, hS, hE'm, ne_eq, Prod.mk.injEq, and_true] at key
    simp only [mem_inter, mem_erase]
    exact key
  · intro ht u hu w hw huw
    have hu' := (hS u).1 hu
    have hw' := (hS w).1 hw
    obtain ⟨e', he', hne, hint⟩ :=
      ht _ hu'.1 _ hw'.1 (fun h => huw (Prod.ext h (hu'.2.trans hw'.2.symm)))
    have ne' : e'.Nonempty := card_pos.1 (by rw [hX _ he']; omega)
    have hp1 : (e'.image fun a => (a, y)).image Prod.fst = e' := by
      rw [image_image]; exact image_id'
    refine ⟨e'.image fun a => (a, y), ?_, fun h => hne (by rw [← hp1, h]), ?_⟩
    · simp only [strong, mem_filter, mem_univ, true_and]
      left
      refine ⟨by rw [hp1]; exact he', ?_⟩
      rw [image_image]
      rw [show (Prod.snd ∘ fun a => (a, y)) = fun _ => y from rfl, image_const ne',
        card_singleton]
    · ext x
      have key := Finset.ext_iff.1 hint x.1
      rw [mem_inter, mem_erase, mem_erase] at key
      rw [mem_inter, mem_erase, mem_erase, hS, mem_image_mk_right]
      constructor
      · rintro ⟨⟨a, b⟩, c, -⟩
        obtain ⟨k1, k2, -⟩ := key.1 ⟨a, c⟩
        exact ⟨fun h => k1 (congrArg Prod.fst h), fun h => k2 (congrArg Prod.fst h), a, b⟩
      · rintro ⟨n1, n2, a, b⟩
        have := key.2 ⟨fun h => n1 (Prod.ext h (b.trans hw'.2.symm)),
          fun h => n2 (Prod.ext h (b.trans hu'.2.symm)), a⟩
        exact ⟨⟨a, b⟩, this.2, b⟩

/-- An edge `{x} × f` is transposition-complete in `X ⊠ Y` iff `f` is in `Y`. -/
lemma tc_cart_fst (hr : 4 ≤ r) (hX : Uniform r X) (hY : Uniform r Y) {S : Finset (α × γ)}
    (h1 : (S.image Prod.fst).card = 1) (h2 : S.image Prod.snd ∈ Y.E) :
    TC (strong X Y) S ↔ TC Y (S.image Prod.snd) := by
  obtain ⟨a, ha⟩ := fst_const h1
  have hS := mem_iff_of_fst ha
  constructor
  · intro ht b hb b' hb' hbb
    have hu : (a, b) ∈ S := (hS _).2 ⟨rfl, hb⟩
    have hw : (a, b') ∈ S := (hS _).2 ⟨rfl, hb'⟩
    obtain ⟨E', hE', hne, hint⟩ := ht _ hu _ hw (fun h => hbb (congrArg Prod.snd h))
    have cS : S.card = r := (card_image_of_injOn fun x hx x' hx' h =>
      Prod.ext ((ha x hx).trans (ha x' hx').symm) h).symm.trans (hY _ h2)
    have cI : 1 < (S ∩ E').card := by
      rw [hint]
      have a1 := card_erase_add_one hu
      have a2 := card_erase_add_one
        (mem_erase.2 ⟨fun (h : ((a, b') : α × γ) = (a, b)) => hbb (congrArg Prod.snd h).symm, hw⟩)
      omega
    obtain ⟨x1, hx1, x2, hx2, hx12⟩ := one_lt_card.1 cI
    rw [mem_inter] at hx1 hx2
    have hnot : E'.image Prod.fst ∉ X.E := fun hm =>
      hx12 (injOn_of_card_image_eq (by rw [hX _ hm, card_mem_strong hX hY hE'])
        hx1.2 hx2.2 ((ha _ hx1.1).trans (ha _ hx2.1).symm))
    obtain ⟨g1, g2⟩ : (E'.image Prod.fst).card = 1 ∧ E'.image Prod.snd ∈ Y.E := by
      simp only [strong, mem_filter, mem_univ, true_and] at hE'
      rcases hE' with ⟨h, -⟩ | h | ⟨h, -, -⟩
      · exact absurd h hnot
      · exact h
      · exact absurd h hnot
    obtain ⟨a', ha'⟩ := fst_const g1
    have hE'm := mem_iff_of_fst fun x hx =>
      (ha' x hx).trans ((ha' _ hx1.2).symm.trans (ha _ hx1.1))
    refine ⟨E'.image Prod.snd, g2, fun h => hne (ext fun x => by rw [hE'm, hS, h]), ?_⟩
    ext c
    have key := Finset.ext_iff.1 hint (a, c)
    simp only [mem_inter, mem_erase, hS, hE'm, ne_eq, Prod.mk.injEq, true_and] at key
    simp only [mem_inter, mem_erase]
    exact key
  · intro ht u hu w hw huw
    have hu' := (hS u).1 hu
    have hw' := (hS w).1 hw
    obtain ⟨f', hf', hne, hint⟩ :=
      ht _ hu'.2 _ hw'.2 (fun h => huw (Prod.ext (hu'.1.trans hw'.1.symm) h))
    have nf' : f'.Nonempty := card_pos.1 (by rw [hY _ hf']; omega)
    have hp2 : (f'.image fun b => (a, b)).image Prod.snd = f' := by
      rw [image_image]; exact image_id'
    refine ⟨f'.image fun b => (a, b), ?_, fun h => hne (by rw [← hp2, h]), ?_⟩
    · simp only [strong, mem_filter, mem_univ, true_and]
      right; left
      refine ⟨?_, by rw [hp2]; exact hf'⟩
      rw [image_image]
      rw [show (Prod.fst ∘ fun b => (a, b)) = fun _ => a from rfl, image_const nf',
        card_singleton]
    · ext x
      have key := Finset.ext_iff.1 hint x.2
      rw [mem_inter, mem_erase, mem_erase] at key
      rw [mem_inter, mem_erase, mem_erase, hS, mem_image_mk_left]
      constructor
      · rintro ⟨⟨b, c⟩, -, d⟩
        obtain ⟨k1, k2, -⟩ := key.1 ⟨c, d⟩
        exact ⟨fun h => k1 (congrArg Prod.snd h), fun h => k2 (congrArg Prod.snd h), b, c⟩
      · rintro ⟨n1, n2, b, c⟩
        have := key.2 ⟨fun h => n1 (Prod.ext (b.trans hw'.1.symm) h),
          fun h => n2 (Prod.ext (b.trans hu'.1.symm) h), c⟩
        exact ⟨⟨b, c⟩, b, this.2⟩

/-! ## The skeleton lemma -/

/-- **Skeleton lemma** (Lemma 3.4). For `r ≥ 4` and `r`-uniform `X`, `Y`,
`Sk (X ⊠ Y) = Sk X □ Sk Y`. -/
theorem skeleton (hr : 4 ≤ r) (hX : Uniform r X) (hY : Uniform r Y) :
    (Sk (strong X Y)).E = (box (Sk X) (Sk Y)).E := by
  ext S
  simp only [Sk, box, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hS, hn⟩
    have hS' := hS
    simp only [strong, mem_filter, mem_univ, true_and] at hS'
    rcases hS' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨⟨h1, fun ht => hn ((tc_cart_snd hr hX hY h1 h2).2 ht)⟩, h2⟩
    · exact Or.inr ⟨h1, h2, fun ht => hn ((tc_cart_fst hr hX hY h1 h2).2 ht)⟩
    · exact absurd (tc_noncart hX hY h1 h2 (card_mem_strong hX hY hS)) hn
  · rintro (⟨⟨h1, hn⟩, h2⟩ | ⟨h1, h2, hn⟩)
    · refine ⟨?_, fun ht => hn ((tc_cart_snd hr hX hY h1 h2).1 ht)⟩
      simp only [strong, mem_filter, mem_univ, true_and]
      exact Or.inl ⟨h1, h2⟩
    · refine ⟨?_, fun ht => hn ((tc_cart_fst hr hX hY h1 h2).1 ht)⟩
      simp only [strong, mem_filter, mem_univ, true_and]
      exact Or.inr (Or.inl ⟨h1, h2⟩)

end HypProd
