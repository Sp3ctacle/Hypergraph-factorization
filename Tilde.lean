/-
# Square roots for the square, r-uniform direct and non-rank-preserving direct products

* `sq_square`      : Proposition 4.4(iii) / PDF 4.5(iii), `A ⊡ A ≅ B ⊡ B → A ≅ B`.
* `rdirect_square` : Proposition 4.4(ii)  / PDF 4.5(ii), `A ×ᵣ A ≅ B ×ᵣ B → A ≅ B`
                     (`maxDirect_eq`, `minDirect_eq`: the max- and min-rank direct products
                     coincide with `×ᵣ` on `r`-uniform factors).
* Lemma 7.1 (`tedge_fst`, `tedge_snd`, `tedge_count_fst`, `tedge_inj`),
  Lemma 7.2 (`inter_tedge_le`, `card_inter_tedge_same_x`, `card_inter_tedge_same_y`,
  `card_inter_tedge_diff`), Lemma 7.3 (`codeg_same_fst`, `codeg_diff`),
  Proposition 7.4 (`blockOf_tedge`, `sq_eq_blocks`), Proposition 7.5 (`isApex_iff`),
  Lemma 7.7 / PDF 7.7 (`fl_prod_iso`, `iso_of_fl_iso`).
* `tdp_square`     : Theorem 7.7 / PDF 7.8, square roots for `×̃` on linear `r`-uniform
                     hypergraphs, `r ≥ 2`.
-/
import Hg.Iterated
import Hg.TwoSorted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

variable {r : ℕ} {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma image_inst_eq {δ ε : Type} {i1 i2 : DecidableEq ε} (f : δ → ε) (s : Finset δ) :
    @image δ ε i1 f s = @image δ ε i2 f s := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

lemma HG.ext' {A B : HG α} (h : A.E = B.E) : A = B := by
  obtain ⟨EA⟩ := A; obtain ⟨EB⟩ := B; cases h; rfl

/-! ## Isomorphisms of two-sorted structures -/

lemma IsoTS.symm' {J P B P' B' : Type} {S : TS P B J} {T : TS P' B' J} (h : IsoTS S T) :
    IsoTS T S := by
  obtain ⟨f, g, h⟩ := h
  exact ⟨f.symm, g.symm, fun j x => by rw [h]; simp⟩

lemma IsoTS.trans' {J P B P' B' P'' B'' : Type} {S : TS P B J} {T : TS P' B' J}
    {U : TS P'' B'' J} (h1 : IsoTS S T) (h2 : IsoTS T U) : IsoTS S U := by
  obtain ⟨f, g, h1⟩ := h1
  obtain ⟨f', g', h2⟩ := h2
  exact ⟨f.trans f', g.trans g', fun j x => by rw [h1, h2]; rfl⟩

/-- An isomorphism maps the edge set onto the edge set. -/
lemma edges_isoVia {A : HG α} {B : HG β} {φ : α ≃ β} (h : IsoVia A B φ) :
    B.E = A.E.image fun t => t.image φ := by
  ext t
  constructor
  · intro ht
    exact mem_image.2 ⟨t.image φ.symm, (h _).2 (by rwa [image_image_equiv]),
      image_image_equiv φ t⟩
  · rintro h'
    obtain ⟨s, hs, rfl⟩ := mem_image.1 h'
    exact (h s).1 hs

/-- The blocks-as-subtype equivalence induced by an isomorphism. -/
def blockEquiv {A : HG α} {B : HG β} {φ : α ≃ β} (h : IsoVia A B φ) :
    {e // e ∈ A.E} ≃ {e // e ∈ B.E} where
  toFun e := ⟨e.1.image φ, (h e.1).1 e.2⟩
  invFun e := ⟨e.1.image φ.symm, (h _).2 (by rw [image_image_equiv]; exact e.2)⟩
  left_inv e := Subtype.ext (by simpa using image_image_equiv φ.symm e.1)
  right_inv e := Subtype.ext (image_image_equiv φ e.1)

/-! ## Proposition 4.4(iii): the square product -/

/-- Square product `A ⊡ B`: edges `e × f`. -/
def sq (A : HG α) (B : HG γ) : HG (α × γ) := ⟨(A.E ×ˢ B.E).image fun p => p.1 ×ˢ p.2⟩

/-- Incidence structure `I(H)`: points, edges, membership. -/
def inc (H : HG α) : TS α {e // e ∈ H.E} Unit := ⟨fun _ => univ.filter fun x => x.1 ∈ x.2.1⟩

lemma mem_inc {H : HG α} {j : Unit} {x : α × {e // e ∈ H.E}} : x ∈ (inc H).R j ↔ x.1 ∈ x.2.1 := by
  simp only [inc, mem_filter, mem_univ, true_and]

lemma product_inj {e e' : Finset α} {f f' : Finset γ} (he : e.Nonempty) (hf : f.Nonempty)
    (h : e ×ˢ f = e' ×ˢ f') : e = e' ∧ f = f' := by
  have hne : (e' ×ˢ f').Nonempty := h ▸ he.product hf
  obtain ⟨he', hf'⟩ := nonempty_product.1 hne
  refine ⟨?_, ?_⟩
  · rw [← product_image_fst (s := e) hf, h, product_image_fst hf']
  · rw [← product_image_snd (t := f) he, h, product_image_snd he']

lemma inc_prod_iso {A : HG α} {B : HG γ} (hA : ∀ e ∈ A.E, e.Nonempty)
    (hB : ∀ e ∈ B.E, e.Nonempty) : IsoTS (prodTS (inc A) (inc B)) (inc (sq A B)) := by
  let g : {e // e ∈ A.E} × {f // f ∈ B.E} → {s // s ∈ (sq A B).E} := fun p =>
    ⟨p.1.1 ×ˢ p.2.1, by
      unfold sq
      exact mem_image_of_mem (fun p : Finset α × Finset γ => p.1 ×ˢ p.2)
        (mem_product.2 ⟨p.1.2, p.2.2⟩ : (p.1.1, p.2.1) ∈ A.E ×ˢ B.E)⟩
  have bij : Bijective g := by
    refine ⟨fun p q hpq => ?_, fun s => ?_⟩
    · have := product_inj (hA _ p.1.2) (hB _ p.2.2) (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
    · have hs2 : s.1 ∈ (A.E ×ˢ B.E).image fun p => p.1 ×ˢ p.2 := s.2
      obtain ⟨⟨e, f⟩, hef, hs⟩ := mem_image.1 hs2
      obtain ⟨he, hf⟩ := mem_product.1 hef
      exact ⟨(⟨e, he⟩, ⟨f, hf⟩), Subtype.ext hs⟩
  refine ⟨Equiv.refl _, Equiv.ofBijective g bij, fun j x => ?_⟩
  rw [mem_prodTS, mem_inc, mem_inc, mem_inc]
  simp [g, mem_product]

lemma inc_iso_of_iso {A : HG α} {B : HG β} (h : Iso A B) : IsoTS (inc A) (inc B) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, blockEquiv hφ, fun j x => ?_⟩
  rw [mem_inc, mem_inc]
  simp [blockEquiv]

lemma iso_of_inc_iso {A : HG α} {B : HG β} (h : IsoTS (inc A) (inc B)) : Iso A B := by
  obtain ⟨f, g, hfg⟩ := h
  have key : ∀ b : {e // e ∈ A.E}, (g b).1 = b.1.image f := fun b => by
    ext y
    have := hfg () (f.symm y, b)
    rw [mem_inc, mem_inc] at this
    simp only [Equiv.apply_symm_apply] at this
    rw [← this, mem_image]
    exact ⟨fun h => ⟨_, h, by simp⟩, fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa using hx⟩
  refine ⟨f, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [← key ⟨s, hs⟩]; exact (g _).2
  · set b := g.symm ⟨s.image f, hs⟩
    have : (g b).1 = s.image f := by simp [b]
    rw [key] at this
    rw [← image_injective f.injective this]
    exact b.2

/-- **Proposition 4.4(iii)** (PDF 4.5(iii)). -/
theorem sq_square {A : HG α} {B : HG β} (hA : ∀ e ∈ A.E, e.Nonempty)
    (hB : ∀ e ∈ B.E, e.Nonempty) (h : Iso (sq A A) (sq B B)) : Iso A B :=
  iso_of_inc_iso (sqrtTS ((inc_prod_iso hA hA).trans'
    ((inc_iso_of_iso h).trans' (inc_prod_iso hB hB).symm')))

/-! ## Proposition 4.4(ii): the r-uniform direct product -/

/-- `r`-uniform direct product: the `r`-sets whose projections are edges. -/
def rdirect (r : ℕ) (A : HG α) (B : HG γ) : HG (α × γ) :=
  ⟨univ.filter fun S => S.card = r ∧ S.image Prod.fst ∈ A.E ∧ S.image Prod.snd ∈ B.E⟩

/-- Max-rank direct product. -/
def maxDirect (A : HG α) (B : HG γ) : HG (α × γ) :=
  ⟨univ.filter fun S => S.image Prod.fst ∈ A.E ∧ S.image Prod.snd ∈ B.E ∧
    S.card = max (S.image Prod.fst).card (S.image Prod.snd).card⟩

/-- Min-rank direct product. -/
def minDirect (A : HG α) (B : HG γ) : HG (α × γ) :=
  ⟨univ.filter fun S => S.image Prod.fst ∈ A.E ∧ S.image Prod.snd ∈ B.E ∧
    S.card = min (S.image Prod.fst).card (S.image Prod.snd).card⟩

lemma maxDirect_eq {A : HG α} {B : HG γ} (hA : Uniform r A) (hB : Uniform r B) :
    (maxDirect A B).E = (rdirect r A B).E := by
  ext S
  simp only [maxDirect, rdirect, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, hc⟩; rw [hA _ h1, hB _ h2, max_self] at hc; exact ⟨hc, h1, h2⟩
  · rintro ⟨hc, h1, h2⟩; exact ⟨h1, h2, by rw [hA _ h1, hB _ h2, max_self, hc]⟩

lemma minDirect_eq {A : HG α} {B : HG γ} (hA : Uniform r A) (hB : Uniform r B) :
    (minDirect A B).E = (rdirect r A B).E := by
  ext S
  simp only [minDirect, rdirect, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, hc⟩; rw [hA _ h1, hB _ h2, min_self] at hc; exact ⟨hc, h1, h2⟩
  · rintro ⟨hc, h1, h2⟩; exact ⟨h1, h2, by rw [hA _ h1, hB _ h2, min_self, hc]⟩

lemma homCard_rdirect {X : HG δ} (hX : Good r X) {A : HG α} {B : HG γ} (hA : Uniform r A) :
    homCard X (rdirect r A B) = homCard X A * homCard X B := by
  apply homCard_mul
  intro e he f
  obtain ⟨-, hle⟩ := hX e he
  have hc : (e.image f).card ≤ r := card_image_le.trans hle
  have key : ∀ T : Finset (α × γ), T.card ≤ r →
      (T ∈ (rdirect r A B).E ↔ T.image Prod.fst ∈ A.E ∧ T.image Prod.snd ∈ B.E) := by
    intro T hT
    simp only [rdirect, mem_filter, mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨le_antisymm hT ?_, h⟩⟩
    rw [← hA _ h.1]; exact card_image_le
  have k := key (e.image f) hc
  rw [image_image, image_image] at k
  convert k using 2
  exact image_inst_eq f e

/-- **Proposition 4.4(ii)** (PDF 4.5(ii)). -/
theorem rdirect_square (hr : 1 ≤ r) {A : HG α} {B : HG β} (hA : Uniform r A)
    (hB : Uniform r B) (h : Iso (rdirect r A A) (rdirect r B B)) : Iso A B := by
  have gA : Good r A := fun e he => ⟨card_pos.1 (by rw [hA e he]; omega), (hA e he).le⟩
  have gB : Good r B := fun e he => ⟨card_pos.1 (by rw [hB e he]; omega), (hB e he).le⟩
  apply lovasz gA gB
  intro δ _ X hX
  have e1 := homCard_rdirect hX hA (B := A)
  have e2 := homCard_rdirect hX hB (B := B)
  rw [homCard_congr_right h] at e1
  exact Nat.pow_left_injective two_ne_zero
    (show homCard X A ^ 2 = homCard X B ^ 2 by rw [pow_two, pow_two, ← e1, e2])

/-! ## The non-rank-preserving direct product -/

/-- The edge `⟨x, e; y, f⟩ = {(x, y)} ∪ (e ∖ {x}) × (f ∖ {y})`. -/
def tedge (x : α) (e : Finset α) (y : γ) (f : Finset γ) : Finset (α × γ) :=
  insert (x, y) ((e.erase x) ×ˢ (f.erase y))

/-- Flags `(x, e)` with `x ∈ e ∈ E(A)`. -/
def flags (A : HG α) : Finset (α × Finset α) := univ.filter fun q => q.1 ∈ q.2 ∧ q.2 ∈ A.E

lemma mem_flags {A : HG α} {q : α × Finset α} : q ∈ flags A ↔ q.1 ∈ q.2 ∧ q.2 ∈ A.E := by
  simp only [flags, mem_filter, mem_univ, true_and]

/-- `tedge` applied to a pair of flags. -/
def tedge' (q : (α × Finset α) × (γ × Finset γ)) : Finset (α × γ) :=
  tedge q.1.1 q.1.2 q.2.1 q.2.2

/-- Non-rank-preserving direct product `A ×̃ B`. -/
def tdp (A : HG α) (B : HG γ) : HG (α × γ) := ⟨(flags A ×ˢ flags B).image tedge'⟩

/-- Linear: distinct edges meet in at most one vertex. -/
def Linear (A : HG α) : Prop := ∀ e ∈ A.E, ∀ e' ∈ A.E, e ≠ e' → (e ∩ e').card ≤ 1

lemma eq_of_two_mem {A : HG α} (hl : Linear A) {e e' : Finset α} (he : e ∈ A.E)
    (he' : e' ∈ A.E) {a a' : α} (haa : a ≠ a') (ha : a ∈ e) (ha' : a' ∈ e) (hb : a ∈ e')
    (hb' : a' ∈ e') : e = e' := by
  by_contra hne
  have := hl e he e' he' hne
  have h2 : ({a, a'} : Finset α) ⊆ e ∩ e' := by
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact mem_inter.2 ⟨ha, hb⟩
    · rw [mem_singleton.1 hz]; exact mem_inter.2 ⟨ha', hb'⟩
  have := card_le_card h2
  rw [card_pair haa] at this
  omega

lemma mem_tedge {x : α} {e : Finset α} {y : γ} {f : Finset γ} {z : α × γ} :
    z ∈ tedge x e y f ↔ z = (x, y) ∨ ((z.1 ≠ x ∧ z.1 ∈ e) ∧ (z.2 ≠ y ∧ z.2 ∈ f)) := by
  simp only [tedge, mem_insert, mem_product, mem_erase]

lemma tedge_subset {x : α} {e : Finset α} {y : γ} {f : Finset γ} (hx : x ∈ e) (hy : y ∈ f) :
    tedge x e y f ⊆ e ×ˢ f := fun z hz => by
  rcases mem_tedge.1 hz with rfl | ⟨⟨-, h1⟩, -, h2⟩
  · exact mem_product.2 ⟨hx, hy⟩
  · exact mem_product.2 ⟨h1, h2⟩

lemma card_tedge {x : α} {e : Finset α} {y : γ} {f : Finset γ} :
    (tedge x e y f).card = (e.erase x).card * (f.erase y).card + 1 := by
  rw [tedge, card_insert_of_notMem, card_product]
  intro h
  simp at h

lemma card_erase_uniform {A : HG α} (hA : Uniform r A) {q : α × Finset α} (hq : q ∈ flags A) :
    (q.2.erase q.1).card = r - 1 := by
  rw [card_erase_of_mem (mem_flags.1 hq).1, hA _ (mem_flags.1 hq).2]

/-- **Lemma 7.1**: projections of `⟨x, e; y, f⟩`. -/
lemma tedge_fst {x : α} {e : Finset α} {y : γ} {f : Finset γ} (hx : x ∈ e)
    (hf : (f.erase y).Nonempty) : (tedge x e y f).image Prod.fst = e := by
  ext a
  rw [mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases mem_tedge.1 hz with rfl | ⟨⟨-, h⟩, -⟩
    · exact hx
    · exact h
  · intro ha
    by_cases hax : a = x
    · exact ⟨(x, y), mem_insert_self _ _, hax.symm⟩
    · obtain ⟨b, hb⟩ := hf
      exact ⟨(a, b), mem_tedge.2 (Or.inr ⟨⟨hax, ha⟩, mem_erase.1 hb⟩), rfl⟩

lemma tedge_snd {x : α} {e : Finset α} {y : γ} {f : Finset γ} (hy : y ∈ f)
    (he : (e.erase x).Nonempty) : (tedge x e y f).image Prod.snd = f := by
  ext b
  rw [mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases mem_tedge.1 hz with rfl | ⟨-, -, h⟩
    · exact hy
    · exact h
  · intro hb
    by_cases hby : b = y
    · exact ⟨(x, y), mem_insert_self _ _, hby.symm⟩
    · obtain ⟨a, ha⟩ := he
      exact ⟨(a, b), mem_tedge.2 (Or.inr ⟨mem_erase.1 ha, hby, hb⟩), rfl⟩

/-- **Lemma 7.1**: `x` is the only element of `e` that is the first coordinate of exactly one
element of `⟨x, e; y, f⟩`. -/
lemma tedge_count_fst {x a : α} {e : Finset α} {y : γ} {f : Finset γ} (hf : 2 ≤ (f.erase y).card)
    : ((tedge x e y f).filter fun z => z.1 = a).card = 1 ↔ a = x := by
  by_cases hax : a = x
  · subst hax
    have : (tedge a e y f).filter (fun z => z.1 = a) = {(a, y)} := by
      ext z
      rw [mem_filter, mem_tedge, mem_singleton]
      constructor
      · rintro ⟨h | ⟨⟨h1, -⟩, -⟩, h2⟩
        · exact h
        · exact absurd h2 h1
      · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
    simp [this]
  · by_cases hae : a ∈ e
    · have : (tedge x e y f).filter (fun z => z.1 = a) = {a} ×ˢ (f.erase y) := by
        ext z
        rw [mem_filter, mem_tedge, mem_product, mem_singleton, mem_erase]
        constructor
        · rintro ⟨h | ⟨-, h⟩, h2⟩
          · rw [h] at h2; exact absurd h2.symm hax
          · exact ⟨h2, h⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr ⟨⟨h1 ▸ hax, h1 ▸ hae⟩, h2⟩, h1⟩
      rw [this, card_product, card_singleton]
      simp only [one_mul, hax, iff_false]
      omega
    · have : (tedge x e y f).filter (fun z => z.1 = a) = ∅ := by
        ext z
        rw [mem_filter, mem_tedge]
        simp only [notMem_empty, iff_false, not_and]
        rintro (h | ⟨⟨-, h⟩, -⟩) h2
        · rw [h] at h2; exact hax h2.symm
        · exact hae (h2 ▸ h)
      simp [this, hax]

lemma tedge_count_snd {x : α} {e : Finset α} {y b : γ} {f : Finset γ}
    (he : 2 ≤ (e.erase x).card) :
    ((tedge x e y f).filter fun z => z.2 = b).card = 1 ↔ b = y := by
  have hsw : (tedge x e y f).image Prod.swap = tedge y f x e := by
    ext z
    simp only [mem_image, mem_tedge]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1⟩
    · intro hz
      refine ⟨z.swap, ?_, Prod.swap_swap z⟩
      rcases hz with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1⟩
  have : ((tedge x e y f).filter fun z => z.2 = b).card =
      ((tedge y f x e).filter fun z => z.1 = b).card := by
    rw [← hsw, filter_image, card_image_of_injective _ Prod.swap_injective]
    rfl
  rw [this, tedge_count_fst he]

variable {A : HG α} {B : HG γ}

/-- **Lemma 7.1**: `⟨x, e; y, f⟩` determines `(x, e, y, f)`. -/
lemma tedge_inj (hr : 3 ≤ r) (hA : Uniform r A) (hB : Uniform r B) :
    Set.InjOn (tedge' (α := α) (γ := γ)) ((flags A ×ˢ flags B : Finset _) : Set _) := by
  rintro ⟨⟨x, e⟩, ⟨y, f⟩⟩ hq ⟨⟨x', e'⟩, ⟨y', f'⟩⟩ hq' h
  simp only [coe_product, Set.mem_prod, mem_coe] at hq hq'
  have hq1 := mem_flags.1 hq.1
  have hq2 := mem_flags.1 hq.2
  have hq1' := mem_flags.1 hq'.1
  have hq2' := mem_flags.1 hq'.2
  simp only at hq1 hq2 hq1' hq2'
  have ce := card_erase_uniform hA hq.1
  have cf := card_erase_uniform hB hq.2
  have ce' := card_erase_uniform hA hq'.1
  have cf' := card_erase_uniform hB hq'.2
  simp only at ce cf ce' cf'
  have hfne : ∀ {s : Finset γ} {b : γ}, (s.erase b).card = r - 1 → (s.erase b).Nonempty :=
    fun h => card_pos.1 (by omega)
  have hene : ∀ {s : Finset α} {b : α}, (s.erase b).card = r - 1 → (s.erase b).Nonempty :=
    fun h => card_pos.1 (by omega)
  have h' : tedge x e y f = tedge x' e' y' f' := h
  have he : e = e' := by
    rw [← tedge_fst hq1.1 (hfne cf), h', tedge_fst hq1'.1 (hfne cf')]
  have hf : f = f' := by
    rw [← tedge_snd hq2.1 (hene ce), h', tedge_snd hq2'.1 (hene ce')]
  have hx : x = x' := by
    have := (tedge_count_fst (x := x') (e := e') (y := y') (f := f') (a := x') (by omega)).2 rfl
    rw [← h'] at this
    exact ((tedge_count_fst (x := x) (e := e) (y := y) (f := f) (by omega)).1 this).symm
  have hy : y = y' := by
    have := (tedge_count_snd (x := x') (e := e') (y := y') (f := f') (b := y') (by omega)).2 rfl
    rw [← h'] at this
    exact ((tedge_count_snd (x := x) (e := e) (y := y) (f := f) (by omega)).1 this).symm
  subst he hf hx hy
  rfl

lemma mem_tdp {E : Finset (α × γ)} :
    E ∈ (tdp A B).E ↔ ∃ q ∈ flags A ×ˢ flags B, tedge' q = E := by
  simp only [tdp, mem_image]

/-! ### Lemma 7.2: intersections -/

lemma tedge_mem_tdp {x : α} {e : Finset α} {y : γ} {f : Finset γ} (hx : x ∈ e) (he : e ∈ A.E)
    (hy : y ∈ f) (hf : f ∈ B.E) : tedge x e y f ∈ (tdp A B).E :=
  mem_tdp.2 ⟨((x, e), (y, f)), mem_product.2 ⟨mem_flags.2 ⟨hx, he⟩, mem_flags.2 ⟨hy, hf⟩⟩, rfl⟩

/-- **Lemma 7.2(i)**: edges with different blocks meet in at most `r` points. -/
lemma inter_tedge_le (hA : Uniform r A) (hB : Uniform r B) (hlA : Linear A) (hlB : Linear B)
    {x x' : α} {e e' : Finset α} {y y' : γ} {f f' : Finset γ} (hx : x ∈ e) (he : e ∈ A.E)
    (hx' : x' ∈ e') (he' : e' ∈ A.E) (hy : y ∈ f) (hf : f ∈ B.E) (hy' : y' ∈ f')
    (hf' : f' ∈ B.E) (hne : (e, f) ≠ (e', f')) :
    (tedge x e y f ∩ tedge x' e' y' f').card ≤ r := by
  have sub : tedge x e y f ∩ tedge x' e' y' f' ⊆ (e ∩ e') ×ˢ (f ∩ f') := fun z hz => by
    rw [mem_inter] at hz
    have h1 := mem_product.1 (tedge_subset hx hy hz.1)
    have h2 := mem_product.1 (tedge_subset hx' hy' hz.2)
    exact mem_product.2 ⟨mem_inter.2 ⟨h1.1, h2.1⟩, mem_inter.2 ⟨h1.2, h2.2⟩⟩
  refine (card_le_card sub).trans ?_
  rw [card_product]
  by_cases hee : e = e'
  · have hff : f ≠ f' := fun h => hne (by rw [hee, h])
    have := hlB f hf f' hf' hff
    have : (e ∩ e').card ≤ r := (card_le_card inter_subset_left).trans (hA e he).le
    nlinarith
  · have := hlA e he e' he' hee
    have : (f ∩ f').card ≤ r := (card_le_card inter_subset_left).trans (hB f hf).le
    nlinarith

/-- **Lemma 7.2(ii)**, case `x = x'`. -/
lemma card_inter_tedge_same_x (hB : Uniform r B) (hA : Uniform r A) {x : α} {e : Finset α}
    {y y' : γ} {f : Finset γ} (hx : x ∈ e) (he : e ∈ A.E) (hy : y ∈ f) (hy' : y' ∈ f)
    (hf : f ∈ B.E) (hyy : y ≠ y') :
    (tedge x e y f ∩ tedge x e y' f).card = (r - 1) * (r - 2) := by
  have : tedge x e y f ∩ tedge x e y' f = (e.erase x) ×ˢ ((f.erase y).erase y') := by
    ext ⟨a, b⟩
    simp only [mem_inter, mem_tedge, mem_product, mem_erase, Prod.mk.injEq]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.2.symm.trans h2.2) hyy
      · exact absurd h1.1 h2.1.1
      · exact absurd h2.1 h1.1.1
      · exact ⟨h1.1, h2.2.1, h1.2.1, h1.2.2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨Or.inr ⟨h1, h3, h4⟩, Or.inr ⟨h1, h2, h4⟩⟩
  rw [this, card_product, card_erase_of_mem hx, card_erase_of_mem (mem_erase.2 ⟨hyy.symm, hy'⟩),
    card_erase_of_mem hy, hA e he, hB f hf, show r - 1 - 1 = r - 2 from by omega]

/-- **Lemma 7.2(ii)**, case `y = y'`. -/
lemma card_inter_tedge_same_y (hA : Uniform r A) (hB : Uniform r B) {x x' : α}
    {e : Finset α} {y : γ} {f : Finset γ} (hx : x ∈ e) (hx' : x' ∈ e) (he : e ∈ A.E)
    (hy : y ∈ f) (hf : f ∈ B.E) (hxx : x ≠ x') :
    (tedge x e y f ∩ tedge x' e y f).card = (r - 1) * (r - 2) := by
  have : tedge x e y f ∩ tedge x' e y f = ((e.erase x).erase x') ×ˢ (f.erase y) := by
    ext ⟨a, b⟩
    simp only [mem_inter, mem_tedge, mem_product, mem_erase, Prod.mk.injEq]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.1.symm.trans h2.1) hxx
      · exact absurd h1.2 h2.2.1
      · exact absurd h2.2 h1.2.1
      · exact ⟨⟨h2.1.1, h1.1.1, h1.1.2⟩, h1.2⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨Or.inr ⟨⟨h2, h3⟩, h4⟩, Or.inr ⟨⟨h1, h3⟩, h4⟩⟩
  rw [this, card_product, card_erase_of_mem (mem_erase.2 ⟨hxx.symm, hx'⟩), card_erase_of_mem hx,
    card_erase_of_mem hy, hA e he, hB f hf, show r - 1 - 1 = r - 2 from by omega, mul_comm]

/-- **Lemma 7.2(iii)**. -/
lemma card_inter_tedge_diff (hA : Uniform r A) (hB : Uniform r B) {x x' : α}
    {e : Finset α} {y y' : γ} {f : Finset γ} (hx : x ∈ e) (hx' : x' ∈ e) (he : e ∈ A.E)
    (hy : y ∈ f) (hy' : y' ∈ f) (hf : f ∈ B.E) (hxx : x ≠ x') (hyy : y ≠ y') :
    (tedge x e y f ∩ tedge x' e y' f).card = (r - 2) ^ 2 + 2 := by
  set G := ((e.erase x).erase x') ×ˢ ((f.erase y).erase y')
  have : tedge x e y f ∩ tedge x' e y' f = insert (x, y) (insert (x', y') G) := by
    ext ⟨a, b⟩
    simp only [G, mem_inter, mem_tedge, mem_insert, mem_product, mem_erase, Prod.mk.injEq]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.1.symm.trans h2.1) hxx
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨⟨h2.1.1, h1.1.1, h1.1.2⟩, h2.2.1, h1.2.1, h1.2.2⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩)
      · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨⟨hxx, hx⟩, hyy, hy⟩⟩
      · exact ⟨Or.inr ⟨⟨Ne.symm hxx, hx'⟩, Ne.symm hyy, hy'⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨Or.inr ⟨⟨h2, h3⟩, h5, h6⟩, Or.inr ⟨⟨h1, h3⟩, h4, h6⟩⟩
  have n1 : (x', y') ∉ G := by simp [G]
  have n2 : (x, y) ∉ insert (x', y') G := by
    simp only [G, mem_insert, Prod.mk.injEq, mem_product, mem_erase]
    rintro (⟨h, -⟩ | ⟨⟨-, h, -⟩, -⟩)
    · exact hxx h
    · exact h rfl
  rw [this, card_insert_of_notMem n2, card_insert_of_notMem n1, card_product,
    card_erase_of_mem (mem_erase.2 ⟨hxx.symm, hx'⟩), card_erase_of_mem hx,
    card_erase_of_mem (mem_erase.2 ⟨hyy.symm, hy'⟩), card_erase_of_mem hy, hA e he, hB f hf,
    show r - 1 - 1 = r - 2 from by omega, pow_two]

/-! ### Proposition 7.4: blocks (r ≥ 4) -/

/-- `E ∪ ⋃ {E' : |E ∩ E'| > r}`. -/
def blockOf (r : ℕ) {V : Type} (H : HG V) (E : Finset V) : Finset V :=
  E ∪ (H.E.filter fun E' => r < (E ∩ E').card).biUnion id

lemma lt_of_four (hr : 4 ≤ r) : r < (r - 1) * (r - 2) ∧ r < (r - 2) ^ 2 + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
  have h1 : k + 4 - 1 = k + 3 := by omega
  have h2 : k + 4 - 2 = k + 2 := by omega
  rw [h1, h2]
  constructor <;> nlinarith

/-- **Proposition 7.4**: for `r ≥ 4` the block of `⟨x, e; y, f⟩` is `e × f`. -/
lemma blockOf_tedge (hr : 4 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (hlA : Linear A)
    (hlB : Linear B) {x : α} {e : Finset α} {y : γ} {f : Finset γ} (hx : x ∈ e) (he : e ∈ A.E)
    (hy : y ∈ f) (hf : f ∈ B.E) : blockOf r (tdp A B) (tedge x e y f) = e ×ˢ f := by
  obtain ⟨l1, l2⟩ := lt_of_four hr
  apply Subset.antisymm
  · intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact tedge_subset hx hy hz
    · obtain ⟨E', hE', hz⟩ := mem_biUnion.1 hz
      rw [mem_filter] at hE'
      obtain ⟨⟨⟨x', e'⟩, ⟨y', f'⟩⟩, hq, rfl⟩ := mem_tdp.1 hE'.1
      obtain ⟨hq1, hq2⟩ := mem_product.1 hq
      rw [mem_flags] at hq1 hq2
      have hsame : (e, f) = (e', f') := by
        by_contra hne
        have := inter_tedge_le hA hB hlA hlB hx he hq1.1 hq1.2 hy hf hq2.1 hq2.2 hne
        exact absurd hE'.2 (by simp only [tedge'] at this ⊢; omega)
      simp only [Prod.mk.injEq] at hsame
      obtain ⟨rfl, rfl⟩ := hsame
      exact tedge_subset hq1.1 hq2.1 hz
  · rintro ⟨c, d⟩ hcd
    obtain ⟨hc, hd⟩ := mem_product.1 hcd
    by_cases hxy : (c, d) = (x, y)
    · rw [hxy]; exact mem_union_left _ (mem_insert_self _ _)
    · refine mem_union_right _ (mem_biUnion.2 ⟨tedge c e d f, mem_filter.2
        ⟨tedge_mem_tdp hc he hd hf, ?_⟩, mem_insert_self _ _⟩)
      by_cases hcx : c = x
      · subst hcx
        have hdy : d ≠ y := fun h => hxy (by rw [h])
        rw [card_inter_tedge_same_x hB hA hc he hy hd hf (Ne.symm hdy)]; exact l1
      · by_cases hdy : d = y
        · subst hdy
          rw [card_inter_tedge_same_y hA hB hx hc he hd hf (Ne.symm hcx)]; exact l1
        · rw [card_inter_tedge_diff hA hB hx hc he hy hd hf (Ne.symm hcx) (Ne.symm hdy)]
          exact l2

lemma blockOf_isoVia {V V' : Type} [Fintype V] [Fintype V'] {H : HG V} {H' : HG V'}
    {φ : V ≃ V'} (h : IsoVia H H' φ) (E : Finset V) :
    blockOf r H' (E.image φ) = (blockOf r H E).image φ := by
  unfold blockOf
  rw [edges_isoVia h, filter_image, image_biUnion, image_union, biUnion_image]
  congr 1
  refine biUnion_congr ?_ (fun _ _ => rfl)
  ext E'
  simp only [mem_filter]
  rw [← image_inter _ _ φ.injective, card_image_of_injective _ φ.injective]

/-- **Proposition 7.4**: `A ×̃ B` determines `A ⊡ B` for `r ≥ 4`. -/
lemma sq_eq_blocks (hr : 4 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (hlA : Linear A)
    (hlB : Linear B) : (sq A B).E = (tdp A B).E.image (blockOf r (tdp A B)) := by
  ext s
  simp only [sq, mem_image, mem_product]
  constructor
  · rintro ⟨⟨e, f⟩, ⟨he, hf⟩, rfl⟩
    obtain ⟨x, hx⟩ := card_pos.1 (by rw [hA e he]; omega : 0 < e.card)
    obtain ⟨y, hy⟩ := card_pos.1 (by rw [hB f hf]; omega : 0 < f.card)
    exact ⟨tedge x e y f, tedge_mem_tdp hx he hy hf, blockOf_tedge hr hA hB hlA hlB hx he hy hf⟩
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨⟨⟨x, e⟩, ⟨y, f⟩⟩, hq, rfl⟩ := mem_tdp.1 hE
    obtain ⟨hq1, hq2⟩ := mem_product.1 hq
    rw [mem_flags] at hq1 hq2
    exact ⟨(e, f), ⟨hq1.2, hq2.2⟩, (blockOf_tedge hr hA hB hlA hlB hq1.1 hq1.2 hq2.1 hq2.2).symm⟩

theorem sq_iso_of_tdp_iso (hr : 4 ≤ r) {A : HG α} {B : HG β} (hA : Uniform r A)
    (hB : Uniform r B) (hlA : Linear A) (hlB : Linear B) (h : Iso (tdp A A) (tdp B B)) :
    Iso (sq A A) (sq B B) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun s => ?_⟩
  rw [sq_eq_blocks hr hA hA hlA hlA, sq_eq_blocks hr hB hB hlB hlB]
  constructor
  · intro hs
    obtain ⟨E, hE, rfl⟩ := mem_image.1 hs
    exact mem_image.2 ⟨E.image φ, (hφ E).1 hE, blockOf_isoVia hφ E⟩
  · intro hs
    obtain ⟨E', hE', heq⟩ := mem_image.1 hs
    refine mem_image.2 ⟨E'.image φ.symm, (hφ _).2 (by rwa [image_image_equiv]), ?_⟩
    apply image_injective φ.injective
    rw [← blockOf_isoVia hφ, image_image_equiv, heq]

/-! ### Lemma 7.3: codegrees -/

/-- Codegree: the number of edges containing both `u` and `w`. -/
def codeg {V : Type} (H : HG V) (u w : V) : ℕ := (H.E.filter fun E => u ∈ E ∧ w ∈ E).card

/-- Degree. -/
def deg {V : Type} (H : HG V) (a : V) : ℕ := (H.E.filter fun e => a ∈ e).card

lemma codeg_tdp (hr : 3 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (u w : α × γ) :
    codeg (tdp A B) u w =
      ((flags A ×ˢ flags B).filter fun q => u ∈ tedge' q ∧ w ∈ tedge' q).card := by
  unfold codeg tdp
  rw [filter_image, card_image_of_injOn]
  exact (tedge_inj hr hA hB).mono fun q hq => by
    simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hq
    exact mem_coe.2 (mem_product.2 hq.1)

/-- **Lemma 7.3(ii)**: two points differing in both coordinates have codegree `(r-2)² + 2`. -/
lemma codeg_diff (hr : 3 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (hlA : Linear A)
    (hlB : Linear B) {x0 : α} {e0 : Finset α} {y0 : γ} {f0 : Finset γ} (hx0 : x0 ∈ e0)
    (he0 : e0 ∈ A.E) (hy0 : y0 ∈ f0) (hf0 : f0 ∈ B.E) {a a' : α} {b b' : γ}
    (hu : (a, b) ∈ tedge x0 e0 y0 f0) (hw : (a', b') ∈ tedge x0 e0 y0 f0) (haa : a ≠ a')
    (hbb : b ≠ b') : codeg (tdp A B) (a, b) (a', b') = (r - 2) ^ 2 + 2 := by
  rw [codeg_tdp hr hA hB]
  obtain ⟨ha, hb⟩ := mem_product.1 (tedge_subset hx0 hy0 hu)
  obtain ⟨ha', hb'⟩ := mem_product.1 (tedge_subset hx0 hy0 hw)
  simp only at ha hb ha' hb'
  set Z := insert (a, b) (insert (a', b') (((e0.erase a).erase a') ×ˢ ((f0.erase b).erase b')))
  have hZ : ((flags A ×ˢ flags B).filter fun q => (a, b) ∈ tedge' q ∧ (a', b') ∈ tedge' q) =
      Z.image fun z => ((z.1, e0), (z.2, f0)) := by
    ext q
    rw [mem_filter, mem_image]
    obtain ⟨⟨x, e⟩, ⟨y, f⟩⟩ := q
    simp only [mem_product, mem_flags, tedge']
    constructor
    · rintro ⟨⟨⟨hx, he⟩, hy, hf⟩, h1, h2⟩
      have s1 := mem_product.1 (tedge_subset hx hy h1)
      have s2 := mem_product.1 (tedge_subset hx hy h2)
      simp only at s1 s2
      obtain rfl := eq_of_two_mem hlA he he0 haa s1.1 s2.1 ha ha'
      obtain rfl := eq_of_two_mem hlB hf hf0 hbb s1.2 s2.2 hb hb'
      refine ⟨(x, y), ?_, rfl⟩
      rw [mem_tedge] at h1 h2
      simp only [Z, mem_insert, mem_product, mem_erase, Prod.mk.injEq]
      rcases h1 with h1 | ⟨⟨h1a, -⟩, h1b, -⟩
      · simp only [Prod.mk.injEq] at h1
        exact Or.inl ⟨h1.1.symm, h1.2.symm⟩
      · rcases h2 with h2 | ⟨⟨h2a, -⟩, h2b, -⟩
        · simp only [Prod.mk.injEq] at h2
          exact Or.inr (Or.inl ⟨h2.1.symm, h2.2.symm⟩)
        · exact Or.inr (Or.inr ⟨⟨fun h => h2a h.symm, fun h => h1a h.symm, hx⟩,
            fun h => h2b h.symm, fun h => h1b h.symm, hy⟩)
    · rintro ⟨⟨c, d⟩, hz, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      simp only [Z, mem_insert, mem_product, mem_erase, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
      · exact ⟨⟨⟨ha, he0⟩, hb, hf0⟩, mem_tedge.2 (Or.inl rfl),
          mem_tedge.2 (Or.inr ⟨⟨Ne.symm haa, ha'⟩, Ne.symm hbb, hb'⟩)⟩
      · exact ⟨⟨⟨ha', he0⟩, hb', hf0⟩, mem_tedge.2 (Or.inr ⟨⟨haa, ha⟩, hbb, hb⟩),
          mem_tedge.2 (Or.inl rfl)⟩
      · exact ⟨⟨⟨h3, he0⟩, h6, hf0⟩, mem_tedge.2 (Or.inr ⟨⟨Ne.symm h2, ha⟩, Ne.symm h5, hb⟩),
          mem_tedge.2 (Or.inr ⟨⟨Ne.symm h1, ha'⟩, Ne.symm h4, hb'⟩)⟩
  have hinj : Injective fun z : α × γ => ((z.1, e0), (z.2, f0)) := fun z z' h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 h.2.1
  have n1 : (a', b') ∉ ((e0.erase a).erase a') ×ˢ ((f0.erase b).erase b') := by simp
  have n2 : (a, b) ∉ insert (a', b') (((e0.erase a).erase a') ×ˢ ((f0.erase b).erase b')) := by
    simp only [mem_insert, Prod.mk.injEq, mem_product, mem_erase]
    rintro (⟨h, -⟩ | ⟨⟨-, h, -⟩, -⟩)
    · exact haa h
    · exact h rfl
  rw [hZ, card_image_of_injective _ hinj, card_insert_of_notMem n2, card_insert_of_notMem n1,
    card_product, card_erase_of_mem (mem_erase.2 ⟨Ne.symm haa, ha'⟩), card_erase_of_mem ha,
    card_erase_of_mem (mem_erase.2 ⟨Ne.symm hbb, hb'⟩), card_erase_of_mem hb, hA e0 he0,
    hB f0 hf0, show r - 1 - 1 = r - 2 from by omega, pow_two]

/-- **Lemma 7.3(i)**: two points sharing their first coordinate `a` have codegree
`deg_A(a) (r-1) (r-2)`. -/
lemma codeg_same_fst (hr : 3 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (hlB : Linear B)
    {x0 : α} {e0 : Finset α} {y0 : γ} {f0 : Finset γ} (hx0 : x0 ∈ e0) (hy0 : y0 ∈ f0)
    (hf0 : f0 ∈ B.E) {a : α} {b b' : γ} (hu : (a, b) ∈ tedge x0 e0 y0 f0)
    (hw : (a, b') ∈ tedge x0 e0 y0 f0) (hbb : b ≠ b') :
    codeg (tdp A B) (a, b) (a, b') = deg A a * (r - 1) * (r - 2) := by
  rw [codeg_tdp hr hA hB]
  obtain ⟨-, hb⟩ := mem_product.1 (tedge_subset hx0 hy0 hu)
  obtain ⟨-, hb'⟩ := mem_product.1 (tedge_subset hx0 hy0 hw)
  simp only at hb hb'
  set D := ((A.E.filter fun e => a ∈ e).sigma fun e => e.erase a) ×ˢ ((f0.erase b).erase b')
  have hD : ((flags A ×ˢ flags B).filter fun q => (a, b) ∈ tedge' q ∧ (a, b') ∈ tedge' q) =
      D.image fun p => ((p.1.2, p.1.1), (p.2, f0)) := by
    ext q
    rw [mem_filter, mem_image]
    obtain ⟨⟨x, e⟩, ⟨y, f⟩⟩ := q
    simp only [mem_product, mem_flags, tedge']
    constructor
    · rintro ⟨⟨⟨hx, he⟩, hy, hf⟩, h1, h2⟩
      rw [mem_tedge] at h1 h2
      have g1 : (a ≠ x ∧ a ∈ e) ∧ (b ≠ y ∧ b ∈ f) := by
        rcases h1 with h1 | h1
        · simp only [Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          rcases h2 with h2 | ⟨⟨h2, -⟩, -⟩
          · simp only [Prod.mk.injEq] at h2; exact absurd h2.2.symm hbb
          · exact absurd rfl h2
        · exact h1
      have g2 : (a ≠ x ∧ a ∈ e) ∧ (b' ≠ y ∧ b' ∈ f) := by
        rcases h2 with h2 | h2
        · simp only [Prod.mk.injEq] at h2
          exact absurd h2.1 g1.1.1
        · exact h2
      obtain rfl := eq_of_two_mem hlB hf hf0 hbb g1.2.2 g2.2.2 hb hb'
      refine ⟨⟨⟨e, x⟩, y⟩, ?_, rfl⟩
      simp only [D, mem_product, mem_sigma, mem_filter, mem_erase]
      exact ⟨⟨⟨he, g1.1.2⟩, Ne.symm g1.1.1, hx⟩, Ne.symm g2.2.1, Ne.symm g1.2.1, hy⟩
    · rintro ⟨⟨⟨e', x'⟩, y'⟩, hp, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      simp only [D, mem_product, mem_sigma, mem_filter, mem_erase] at hp
      obtain ⟨⟨⟨he, hae⟩, hxa, hx⟩, hyb', hyb, hy⟩ := hp
      exact ⟨⟨⟨hx, he⟩, hy, hf0⟩, mem_tedge.2 (Or.inr ⟨⟨Ne.symm hxa, hae⟩, Ne.symm hyb, hb⟩),
        mem_tedge.2 (Or.inr ⟨⟨Ne.symm hxa, hae⟩, Ne.symm hyb', hb'⟩)⟩
  have hinj : Injective fun p : (Σ _ : Finset α, α) × γ => ((p.1.2, p.1.1), (p.2, f0)) := by
    rintro ⟨⟨e, x⟩, y⟩ ⟨⟨e', x'⟩, y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, -⟩ := h
    rfl
  rw [hD, card_image_of_injective _ hinj, card_product, card_sigma,
    sum_const_nat (m := r - 1) (fun e he => by
      rw [mem_filter] at he
      rw [card_erase_of_mem he.2, hA e he.1]),
    card_erase_of_mem (mem_erase.2 ⟨Ne.symm hbb, hb'⟩), card_erase_of_mem hb, hB f0 hf0,
    show r - 1 - 1 = r - 2 from by omega]
  rfl

/-! ### Proposition 7.5: apices (r = 3 or r ≥ 5) -/

/-- `v` is an apex of `E`: every other point of `E` has codegree `(r-2)² + 2` with `v`. -/
def IsApex (r : ℕ) {V : Type} (H : HG V) (v : V) (E : Finset V) : Prop :=
  v ∈ E ∧ ∀ w ∈ E, w ≠ v → codeg H v w = (r - 2) ^ 2 + 2

/-- **Proposition 7.5**: for `r = 3` or `r ≥ 5` the apex is recognized by codegrees. -/
theorem isApex_iff (hr : r = 3 ∨ 5 ≤ r) (hA : Uniform r A) (hB : Uniform r B)
    (hlA : Linear A) (hlB : Linear B) {x : α} {e : Finset α} {y : γ} {f : Finset γ}
    (hx : x ∈ e) (he : e ∈ A.E) (hy : y ∈ f) (hf : f ∈ B.E) (v : α × γ) :
    IsApex r (tdp A B) v (tedge x e y f) ↔ v = (x, y) := by
  have hr3 : 3 ≤ r := by omega
  constructor
  · rintro ⟨hv, hall⟩
    by_contra hne
    obtain ⟨s, t⟩ := v
    rcases mem_tedge.1 hv with h | ⟨⟨hsx, hs⟩, hty, ht⟩
    · exact hne h
    have hc : 0 < ((f.erase y).erase t).card := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hty, ht⟩), card_erase_of_mem hy, hB f hf]; omega
    obtain ⟨t', ht'⟩ := card_pos.1 hc
    obtain ⟨ht't, ht'y, ht'f⟩ : t' ≠ t ∧ t' ≠ y ∧ t' ∈ f := by
      simpa only [mem_erase] using ht'
    have hw : (s, t') ∈ tedge x e y f := mem_tedge.2 (Or.inr ⟨⟨hsx, hs⟩, ht'y, ht'f⟩)
    have h1 := hall (s, t') hw (fun h => ht't (by simpa using h))
    rw [codeg_same_fst hr3 hA hB hlB hx hy hf hv hw (Ne.symm ht't)] at h1
    have hd : 1 ≤ deg A s := card_pos.2 ⟨e, mem_filter.2 ⟨he, hs⟩⟩
    rcases hr with rfl | hr5
    · norm_num at h1; omega
    · obtain ⟨k, rfl⟩ : ∃ k, r = k + 5 := ⟨r - 5, by omega⟩
      have e1 : k + 5 - 1 = k + 4 := by omega
      have e2 : k + 5 - 2 = k + 3 := by omega
      rw [e1, e2] at h1
      nlinarith
  · rintro rfl
    refine ⟨mem_insert_self _ _, fun w hw hne => ?_⟩
    obtain ⟨w1, w2⟩ := w
    rcases mem_tedge.1 hw with h | ⟨⟨h1, -⟩, h2, -⟩
    · exact absurd h hne
    exact codeg_diff hr3 hA hB hlA hlB hx he hy hf (mem_insert_self _ _) hw (Ne.symm h1)
      (Ne.symm h2)

/-! ### Flags and Lemma 7.7 -/

/-- The flag structure `Fl(H)`: points, flags, `P = (apex, flag)`, `Q = (other point, flag)`. -/
def Fl (A : HG α) : TS α {q // q ∈ flags A} Bool :=
  ⟨fun j => univ.filter fun z => if j then z.1 = z.2.1.1 else z.1 ∈ z.2.1.2.erase z.2.1.1⟩

/-- The apex structure of `H`: points, edges, `P = (apex, edge)`, `Q = (other point, edge)`. -/
def ApexTS (r : ℕ) {V : Type} [Fintype V] (H : HG V) : TS V {E // E ∈ H.E} Bool :=
  ⟨fun j => univ.filter fun z =>
    if j then IsApex r H z.1 z.2.1 else z.1 ∈ z.2.1 ∧ ¬ IsApex r H z.1 z.2.1⟩

lemma codeg_isoVia {V V' : Type} [Fintype V] [Fintype V'] {H : HG V} {H' : HG V'}
    {φ : V ≃ V'} (h : IsoVia H H' φ) (u w : V) : codeg H' (φ u) (φ w) = codeg H u w := by
  unfold codeg
  rw [edges_isoVia h, filter_image, card_image_of_injective _ (image_injective φ.injective)]
  simp only [φ.injective.mem_finset_image]

lemma isApex_isoVia {V V' : Type} [Fintype V] [Fintype V'] {H : HG V} {H' : HG V'}
    {φ : V ≃ V'} (h : IsoVia H H' φ) (v : V) (E : Finset V) :
    IsApex r H' (φ v) (E.image φ) ↔ IsApex r H v E := by
  unfold IsApex
  rw [φ.injective.mem_finset_image, forall_mem_image]
  simp only [ne_eq, φ.injective.eq_iff, codeg_isoVia h]

lemma apexTS_iso {V V' : Type} [Fintype V] [Fintype V'] {H : HG V} {H' : HG V'}
    {φ : V ≃ V'} (h : IsoVia H H' φ) : IsoTS (ApexTS r H) (ApexTS r H') := by
  refine ⟨φ, blockEquiv h, fun j z => ?_⟩
  cases j <;> simp [ApexTS, blockEquiv, isApex_isoVia h, φ.injective.mem_finset_image]

lemma fl_prod_iso (hr : r = 3 ∨ 5 ≤ r) (hA : Uniform r A) (hB : Uniform r B) (hlA : Linear A)
    (hlB : Linear B) : IsoTS (prodTS (Fl A) (Fl B)) (ApexTS r (tdp A B)) := by
  have hr3 : 3 ≤ r := by omega
  let g : {q // q ∈ flags A} × {q // q ∈ flags B} → {E // E ∈ (tdp A B).E} := fun p =>
    ⟨tedge' (p.1.1, p.2.1), by
      unfold tdp
      exact mem_image_of_mem _ (mem_product.2 ⟨p.1.2, p.2.2⟩ : (p.1.1, p.2.1) ∈ _)⟩
  have bij : Bijective g := by
    refine ⟨fun p p' hpp => ?_, fun E => ?_⟩
    · have := tedge_inj hr3 hA hB (mem_coe.2 (mem_product.2 ⟨p.1.2, p.2.2⟩))
        (mem_coe.2 (mem_product.2 ⟨p'.1.2, p'.2.2⟩)) (congrArg Subtype.val hpp)
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
    · obtain ⟨q, hq, hqE⟩ := mem_tdp.1 E.2
      obtain ⟨h1, h2⟩ := mem_product.1 hq
      exact ⟨(⟨q.1, h1⟩, ⟨q.2, h2⟩), Subtype.ext hqE⟩
  refine ⟨Equiv.refl _, Equiv.ofBijective g bij, fun j z => ?_⟩
  obtain ⟨v, ⟨⟨x, e⟩, hq1⟩, ⟨⟨y, f⟩, hq2⟩⟩ := z
  rw [mem_flags] at hq1 hq2
  simp only at hq1 hq2
  have hapex := isApex_iff hr hA hB hlA hlB hq1.1 hq1.2 hq2.1 hq2.2 v
  cases j
  · simp only [mem_prodTS, Fl, ApexTS, mem_filter, mem_univ, true_and, Bool.false_eq_true,
      if_false, Equiv.refl_apply, Equiv.ofBijective_apply, g, tedge']
    rw [hapex, mem_tedge, mem_erase, mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr ⟨h1, h2⟩, fun h => h1.1 (by rw [h])⟩
    · rintro ⟨h | h, hne⟩
      · exact absurd h hne
      · exact h
  · simp only [mem_prodTS, Fl, ApexTS, mem_filter, mem_univ, true_and, if_true,
      Equiv.refl_apply, Equiv.ofBijective_apply, g, tedge']
    rw [hapex, Prod.ext_iff]

lemma mem_Fl_either {A : HG α} (b : {q // q ∈ flags A}) (v : α) :
    v ∈ b.1.2 ↔ (v, b) ∈ (Fl A).R true ∨ (v, b) ∈ (Fl A).R false := by
  have hb := (mem_flags.1 b.2).1
  simp only [Fl, mem_filter, mem_univ, true_and, if_true, Bool.false_eq_true, if_false,
    mem_erase]
  constructor
  · intro hv
    by_cases h : v = b.1.1
    · exact Or.inl h
    · exact Or.inr ⟨h, hv⟩
  · rintro (h | h)
    · rw [h]; exact hb
    · exact h.2

/-- **Lemma 7.7(ii)**: the flag structure determines the hypergraph. -/
lemma iso_of_fl_iso {A : HG α} {B : HG β} (hA : ∀ e ∈ A.E, e.Nonempty)
    (hB : ∀ e ∈ B.E, e.Nonempty) (h : IsoTS (Fl A) (Fl B)) : Iso A B := by
  obtain ⟨f, g, hfg⟩ := h
  have key : ∀ b : {q // q ∈ flags A}, (g b).1.2 = b.1.2.image f := fun b => by
    ext w
    have h1 := hfg true (f.symm w, b)
    have h2 := hfg false (f.symm w, b)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [mem_Fl_either, ← h1, ← h2, ← mem_Fl_either, mem_image]
    exact ⟨fun h => ⟨_, h, by simp⟩, fun ⟨x, hx, hxw⟩ => by rw [← hxw]; simpa using hx⟩
  refine ⟨f, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hA s hs
    have := (mem_flags.1 (g ⟨(x, s), mem_flags.2 ⟨hx, hs⟩⟩).2).2
    rwa [key] at this
  · obtain ⟨y, hy⟩ := hB _ hs
    set b := g.symm ⟨(y, s.image f), mem_flags.2 ⟨hy, hs⟩⟩
    have hgb : (g b).1.2 = s.image f := by simp [b]
    rw [key] at hgb
    rw [← image_injective f.injective hgb]
    exact (mem_flags.1 b.2).2

/-! ### r = 2 -/

lemma tdp_eq_rdirect (hA : Uniform 2 A) (hB : Uniform 2 B) :
    (tdp A B).E = (rdirect 2 A B).E := by
  ext S
  simp only [rdirect, mem_filter, mem_univ, true_and]
  constructor
  · intro hS
    obtain ⟨⟨⟨x, e⟩, ⟨y, f⟩⟩, hq, rfl⟩ := mem_tdp.1 hS
    obtain ⟨h1, h2⟩ := mem_product.1 hq
    rw [mem_flags] at h1 h2
    have ce := card_erase_uniform hA (mem_flags.2 h1)
    have cf := card_erase_uniform hB (mem_flags.2 h2)
    simp only at ce cf h1 h2
    refine ⟨by rw [tedge', card_tedge, ce, cf], ?_, ?_⟩
    · rw [tedge', tedge_fst (y := y) (f := f) h1.1 (card_pos.1 (by rw [cf]; norm_num))]
      exact h1.2
    · rw [tedge', tedge_snd (x := x) (e := e) h2.1 (card_pos.1 (by rw [ce]; norm_num))]
      exact h2.2
  · rintro ⟨hc, h1, h2⟩
    obtain ⟨u, w, huw, rfl⟩ := card_eq_two.1 hc
    have p1 : ({u, w} : Finset (α × γ)).image Prod.fst = {u.1, w.1} := by simp
    have p2 : ({u, w} : Finset (α × γ)).image Prod.snd = {u.2, w.2} := by simp
    rw [p1] at h1
    rw [p2] at h2
    have d1 : u.1 ≠ w.1 := fun h => by
      have := hA _ h1; rw [h, pair_eq_singleton, card_singleton] at this; norm_num at this
    have d2 : u.2 ≠ w.2 := fun h => by
      have := hB _ h2; rw [h, pair_eq_singleton, card_singleton] at this; norm_num at this
    refine mem_tdp.2 ⟨((u.1, {u.1, w.1}), (u.2, {u.2, w.2})),
      mem_product.2 ⟨mem_flags.2 ⟨mem_insert_self _ _, h1⟩, mem_flags.2 ⟨mem_insert_self _ _, h2⟩⟩,
      ?_⟩
    ext z
    simp only [tedge', mem_tedge, mem_insert, mem_singleton]
    constructor
    · rintro (h | ⟨⟨h1, h1' | h1'⟩, h2, h2' | h2'⟩)
      · exact Or.inl h
      all_goals first
        | exact absurd h1' h1
        | exact absurd h2' h2
        | exact Or.inr (Prod.ext h1' h2')
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨Ne.symm d1, Or.inr rfl⟩, Ne.symm d2, Or.inr rfl⟩

/-! ## Theorem 7.7 (PDF 7.8) -/

/-- **Theorem 7.7** (PDF 7.8). Square roots for `×̃` are unique on linear `r`-uniform
hypergraphs, `r ≥ 2`. -/
theorem tdp_square (hr : 2 ≤ r) {A : HG α} {B : HG β} (hA : Uniform r A) (hB : Uniform r B)
    (hlA : Linear A) (hlB : Linear B) (h : Iso (tdp A A) (tdp B B)) : Iso A B := by
  have hAne : ∀ e ∈ A.E, e.Nonempty := fun e he => card_pos.1 (by rw [hA e he]; omega)
  have hBne : ∀ e ∈ B.E, e.Nonempty := fun e he => card_pos.1 (by rw [hB e he]; omega)
  rcases (by omega : r = 2 ∨ r = 3 ∨ 4 ≤ r) with rfl | rfl | h4
  · apply rdirect_square (by norm_num) hA hB
    rw [← HG.ext' (tdp_eq_rdirect hA hA), ← HG.ext' (tdp_eq_rdirect hB hB)]
    exact h
  · obtain ⟨φ, hφ⟩ := h
    exact iso_of_fl_iso hAne hBne (sqrtTS ((fl_prod_iso (Or.inl rfl) hA hA hlA hlA).trans'
      ((apexTS_iso (r := 3) hφ).trans' (fl_prod_iso (Or.inl rfl) hB hB hlB hlB).symm')))
  · exact sq_square hAne hBne (sq_iso_of_tdp_iso h4 hA hB hlA hlB h)

end HypProd
