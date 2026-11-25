/-
# Iterated strong products of uniform hypergraphs (Lemmas 2.2, 3.1, 3.2)

* `strongPi r X` : the strong product of an indexed family of `r`-uniform hypergraphs,
  defined by the description of Lemma 2.2 (the `r`-sets whose projections are singletons or
  edges, at least one an edge).
* `mem_strong_uniform` : Lemma 2.2 for two factors: the binary strong product of `r`-uniform
  hypergraphs has exactly that description.
* `iso_strongPi_sum`   : Lemma 2.2, iterated form: the product over `ι ⊕ κ` is the binary
  product of the products over `ι` and over `κ`. With `iso_strongPi_unique` this identifies
  `strongPi` with every bracketing of binary products.
* `iso_strong_assoc`, `iso_strong_comm` : associativity and commutativity.
* `uniform_left_of_iso`, `uniform_right_of_iso` : Lemma 3.1 (factors are `r`-uniform).
* `mem_strong_box`, `mem_strong_layer` : Lemma 3.2 (boxes).
* `normal_eq_strong` : the normal product equals the strong product on uniform factors.
-/
import Hg.Skeleton

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

/-! ## Small facts about images -/

lemma card_image_eq_one {δ ε : Type} {S : Finset δ} {f : δ → ε} (hS : S.Nonempty)
    (h : ∀ x ∈ S, ∀ x' ∈ S, f x = f x') : (S.image f).card = 1 := by
  obtain ⟨x0, hx0⟩ := hS
  rw [card_eq_one]
  refine ⟨f x0, eq_singleton_iff_unique_mem.2 ⟨mem_image_of_mem _ hx0, fun z hz => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
  exact h x hx x0 hx0

lemma eq_of_card_image_eq_one {δ ε : Type} {S : Finset δ} {f : δ → ε}
    (h : (S.image f).card = 1) {x x' : δ} (hx : x ∈ S) (hx' : x' ∈ S) : f x = f x' := by
  obtain ⟨z, hz⟩ := card_eq_one.1 h
  have h1 := mem_image_of_mem f hx
  have h2 := mem_image_of_mem f hx'
  rw [hz, mem_singleton] at h1 h2
  rw [h1, h2]

/-- "singleton or edge". -/
def SoE {β : Type} (X : HG β) (s : Finset β) : Prop := s.card = 1 ∨ s ∈ X.E

/-! ## The iterated strong product -/

variable {r : ℕ}

/-- Strong product of an indexed family of `r`-uniform hypergraphs (Lemma 2.2). -/
def strongPi (r : ℕ) {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
    (X : ∀ i, HG (V i)) : HG (∀ i, V i) where
  E := univ.filter fun S => S.card = r ∧
    (∀ i, SoE (X i) (S.image fun x => x i)) ∧ ∃ i, (S.image fun x => x i) ∈ (X i).E

lemma mem_strongPi {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
    {X : ∀ i, HG (V i)} {S : Finset (∀ i, V i)} :
    S ∈ (strongPi r X).E ↔ S.card = r ∧
      (∀ i, SoE (X i) (S.image fun x => x i)) ∧ ∃ i, (S.image fun x => x i) ∈ (X i).E := by
  simp only [strongPi, mem_filter, mem_univ, true_and]

lemma uniform_strongPi {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
    (X : ∀ i, HG (V i)) : Uniform r (strongPi r X) := fun _ h => (mem_strongPi.1 h).1

/-! ## Lemma 2.2 for two factors -/

section binary

variable {α γ : Type} [Fintype α] [Fintype γ] {X : HG α} {Y : HG γ}

/-- **Lemma 2.2**, two factors. -/
lemma mem_strong_uniform (hX : Uniform r X) (hY : Uniform r Y) (S : Finset (α × γ)) :
    S ∈ (strong X Y).E ↔ S.card = r ∧ SoE X (S.image Prod.fst) ∧ SoE Y (S.image Prod.snd) ∧
      (S.image Prod.fst ∈ X.E ∨ S.image Prod.snd ∈ Y.E) := by
  constructor
  · intro hS
    refine ⟨card_mem_strong hX hY hS, ?_⟩
    simp only [strong, mem_filter, mem_univ, true_and] at hS
    rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · exact ⟨Or.inr h1, Or.inl h2, Or.inl h1⟩
    · exact ⟨Or.inl h1, Or.inr h2, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inr h2, Or.inl h1⟩
  · rintro ⟨hc, h1, h2, h3⟩
    simp only [strong, mem_filter, mem_univ, true_and]
    rcases h3 with e1 | e2
    · rcases h2 with s2 | e2
      · exact Or.inl ⟨e1, s2⟩
      · exact Or.inr (Or.inr ⟨e1, e2, by rw [hc, hX _ e1, hY _ e2, max_self]⟩)
    · rcases h1 with s1 | e1
      · exact Or.inr (Or.inl ⟨s1, e2⟩)
      · exact Or.inr (Or.inr ⟨e1, e2, by rw [hc, hX _ e1, hY _ e2, max_self]⟩)

lemma uniform_strong (hX : Uniform r X) (hY : Uniform r Y) : Uniform r (strong X Y) :=
  fun _ h => card_mem_strong hX hY h

/-- Grouping lemma: membership of a paired projection in a binary strong product. -/
lemma group_pair (hr : 1 ≤ r) (hX : Uniform r X) (hY : Uniform r Y) {δ : Type}
    {S : Finset δ} (hS : S.card = r) (q1 : δ → α) (q2 : δ → γ) :
    (SoE (strong X Y) (S.image fun x => (q1 x, q2 x)) ↔
      SoE X (S.image q1) ∧ SoE Y (S.image q2)) ∧
    ((S.image fun x => (q1 x, q2 x)) ∈ (strong X Y).E ↔
      SoE X (S.image q1) ∧ SoE Y (S.image q2) ∧ (S.image q1 ∈ X.E ∨ S.image q2 ∈ Y.E)) := by
  set T := S.image fun x => (q1 x, q2 x)
  have p1 : T.image Prod.fst = S.image q1 := by rw [image_image]; rfl
  have p2 : T.image Prod.snd = S.image q2 := by rw [image_image]; rfl
  have hT : T.card ≤ r := hS ▸ card_image_le
  have hne : S.Nonempty := card_pos.1 (by omega)
  have key : T ∈ (strong X Y).E ↔
      SoE X (S.image q1) ∧ SoE Y (S.image q2) ∧ (S.image q1 ∈ X.E ∨ S.image q2 ∈ Y.E) := by
    rw [mem_strong_uniform hX hY, p1, p2]
    constructor
    · exact fun h => h.2
    · rintro ⟨h1, h2, h3⟩
      refine ⟨le_antisymm hT ?_, h1, h2, h3⟩
      rcases h3 with e | e
      · rw [← hX _ e, ← p1]; exact card_image_le
      · rw [← hY _ e, ← p2]; exact card_image_le
  refine ⟨?_, key⟩
  constructor
  · rintro (h | h)
    · have hTn : T.Nonempty := card_pos.1 (by omega)
      have c1 : (T.image Prod.fst).card = 1 :=
        le_antisymm (h ▸ card_image_le) (card_pos.2 (hTn.image _))
      have c2 : (T.image Prod.snd).card = 1 :=
        le_antisymm (h ▸ card_image_le) (card_pos.2 (hTn.image _))
      rw [p1] at c1; rw [p2] at c2
      exact ⟨Or.inl c1, Or.inl c2⟩
    · exact ⟨(key.1 h).1, (key.1 h).2.1⟩
  · rintro ⟨h1, h2⟩
    by_cases he : S.image q1 ∈ X.E ∨ S.image q2 ∈ Y.E
    · exact Or.inr (key.2 ⟨h1, h2, he⟩)
    · push_neg at he
      have s1 : (S.image q1).card = 1 := h1.resolve_right he.1
      have s2 : (S.image q2).card = 1 := h2.resolve_right he.2
      refine Or.inl (card_image_eq_one hne fun x hx x' hx' => ?_)
      rw [eq_of_card_image_eq_one s1 hx hx', eq_of_card_image_eq_one s2 hx hx']

end binary

/-! ## Grouping for indexed products -/

lemma group_pi (hr : 1 ≤ r) {J : Type} [Fintype J] {β : J → Type} [∀ j, Fintype (β j)]
    {Y : ∀ j, HG (β j)} (hY : ∀ j, Uniform r (Y j)) {δ : Type} {S : Finset δ}
    (hS : S.card = r) (q : ∀ j, δ → β j) :
    (SoE (strongPi r Y) (S.image fun x j => q j x) ↔ ∀ j, SoE (Y j) (S.image (q j))) ∧
    ((S.image fun x j => q j x) ∈ (strongPi r Y).E ↔
      (∀ j, SoE (Y j) (S.image (q j))) ∧ ∃ j, S.image (q j) ∈ (Y j).E) := by
  set T := S.image fun x j => q j x
  have pj : ∀ j, (T.image fun y => y j) = S.image (q j) := fun j => by rw [image_image]; rfl
  have hT : T.card ≤ r := hS ▸ card_image_le
  have hne : S.Nonempty := card_pos.1 (by omega)
  have key : T ∈ (strongPi r Y).E ↔
      (∀ j, SoE (Y j) (S.image (q j))) ∧ ∃ j, S.image (q j) ∈ (Y j).E := by
    rw [mem_strongPi]
    simp only [pj]
    constructor
    · exact fun h => h.2
    · rintro ⟨h1, j, hj⟩
      refine ⟨le_antisymm hT ?_, h1, j, hj⟩
      rw [← hY j _ hj, ← pj]; exact card_image_le
  refine ⟨?_, key⟩
  constructor
  · rintro (h | h)
    · have hTn : T.Nonempty := card_pos.1 (by omega)
      intro j
      have c : (T.image fun y => y j).card = 1 :=
        le_antisymm (h ▸ card_image_le) (card_pos.2 (hTn.image _))
      rw [pj] at c
      exact Or.inl c
    · exact (key.1 h).1
  · intro h
    by_cases he : ∃ j, S.image (q j) ∈ (Y j).E
    · exact Or.inr (key.2 ⟨h, he⟩)
    · push_neg at he
      refine Or.inl (card_image_eq_one hne fun x hx x' hx' => funext fun j => ?_)
      exact eq_of_card_image_eq_one ((h j).resolve_right (he j)) hx hx'

/-! ## Lemma 2.2: iterated form, associativity, commutativity -/

/-- An isomorphism given by an explicit vertex bijection. -/
def IsoVia {α β : Type} [Fintype α] [Fintype β] (A : HG α) (B : HG β) (φ : α ≃ β) : Prop :=
  ∀ s : Finset α, s ∈ A.E ↔ s.image φ ∈ B.E

lemma IsoVia.iso {α β : Type} {_ : Fintype α} {_ : Fintype β} {A : HG α} {B : HG β} {φ : α ≃ β}
    (h : IsoVia A B φ) : Iso A B := ⟨φ, h⟩

lemma image_image_equiv {α β : Type} (φ : α ≃ β) (s : Finset β) :
    (s.image φ.symm).image φ = s := by
  rw [image_image]; simp [Function.comp_def]

lemma Iso.symm' {α β : Type} [Fintype α] [Fintype β] {A : HG α} {B : HG β}
    (h : Iso A B) : Iso B A := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun s => ?_⟩
  rw [hφ, image_image_equiv]

lemma Iso.trans' {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] {A : HG α} {B : HG β}
    {C : HG γ} (h1 : Iso A B) (h2 : Iso B C) : Iso A C := by
  obtain ⟨φ, hφ⟩ := h1
  obtain ⟨ψ, hψ⟩ := h2
  refine ⟨φ.trans ψ, fun s => ?_⟩
  rw [hφ, hψ, image_image]; rfl

lemma Iso.refl' {α : Type} [Fintype α] (A : HG α) : Iso A A :=
  ⟨Equiv.refl α, fun s => by simp⟩

/-- **Lemma 2.2**, iterated form: the product over `ι ⊕ κ` is the binary product of the
products over `ι` and over `κ`. -/
theorem iso_strongPi_sum (hr : 1 ≤ r) {ι κ : Type} [Fintype ι] [Fintype κ]
    {V : ι ⊕ κ → Type} [∀ i, Fintype (V i)] {X : ∀ i, HG (V i)} (hX : ∀ i, Uniform r (X i)) :
    IsoVia (strongPi r X)
      (strong (strongPi r fun a => X (Sum.inl a)) (strongPi r fun b => X (Sum.inr b)))
      (Equiv.sumPiEquivProdPi V) := by
  intro S
  rw [mem_strong_uniform (uniform_strongPi _) (uniform_strongPi _),
    card_image_of_injective _ (Equiv.injective _), image_image, image_image, mem_strongPi]
  constructor
  · rintro ⟨hc, h1, i, hi⟩
    have g1 := group_pi hr (fun a => hX (Sum.inl a)) hc fun a (x : ∀ i, V i) => x (Sum.inl a)
    have g2 := group_pi hr (fun b => hX (Sum.inr b)) hc fun b (x : ∀ i, V i) => x (Sum.inr b)
    refine ⟨hc, g1.1.2 fun a => h1 _, g2.1.2 fun b => h1 _, ?_⟩
    rcases i with a | b
    · exact Or.inl (g1.2.2 ⟨fun a => h1 _, a, hi⟩)
    · exact Or.inr (g2.2.2 ⟨fun b => h1 _, b, hi⟩)
  · rintro ⟨hc, h1, h2, h3⟩
    have g1 := group_pi hr (fun a => hX (Sum.inl a)) hc fun a (x : ∀ i, V i) => x (Sum.inl a)
    have g2 := group_pi hr (fun b => hX (Sum.inr b)) hc fun b (x : ∀ i, V i) => x (Sum.inr b)
    have f1 := g1.1.1 h1
    have f2 := g2.1.1 h2
    refine ⟨hc, fun i => ?_, ?_⟩
    · rcases i with a | b
      · exact f1 a
      · exact f2 b
    · rcases h3 with e | e
      · obtain ⟨-, a, ha⟩ := g1.2.1 e
        exact ⟨Sum.inl a, ha⟩
      · obtain ⟨-, b, hb⟩ := g2.2.1 e
        exact ⟨Sum.inr b, hb⟩

/-- A one-factor product is the factor. -/
theorem iso_strongPi_unique {ι : Type} [Fintype ι] [Unique ι] {V : ι → Type}
    [∀ i, Fintype (V i)] {X : ∀ i, HG (V i)} (hX : ∀ i, Uniform r (X i)) :
    IsoVia (strongPi r X) (X default) (Equiv.piUnique V) := by
  intro S
  have hinj : Injective (Equiv.piUnique V) := Equiv.injective _
  have himg : S.image (Equiv.piUnique V) = S.image fun x => x default := rfl
  rw [mem_strongPi, himg]
  constructor
  · rintro ⟨-, -, i, hi⟩
    rwa [Unique.eq_default i] at hi
  · intro h
    refine ⟨?_, fun i => ?_, default, h⟩
    · rw [← card_image_of_injective _ hinj, himg, hX _ _ h]
    · rw [Unique.eq_default i]; exact Or.inr h

/-- A product over an empty index set has no edges. -/
lemma strongPi_empty {ι : Type} [Fintype ι] [IsEmpty ι] {V : ι → Type}
    [∀ i, Fintype (V i)] (X : ∀ i, HG (V i)) (S : Finset (∀ i, V i)) :
    S ∉ (strongPi r X).E := fun h => by
  obtain ⟨-, -, i, -⟩ := mem_strongPi.1 h
  exact isEmptyElim i

section assoc

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] {X : HG α} {Y : HG β} {Z : HG γ}

/-- **Lemma 2.2**: associativity. -/
theorem iso_strong_assoc (hr : 1 ≤ r) (hX : Uniform r X) (hY : Uniform r Y)
    (hZ : Uniform r Z) :
    IsoVia (strong (strong X Y) Z) (strong X (strong Y Z)) (Equiv.prodAssoc α β γ) := by
  intro S
  rw [mem_strong_uniform (uniform_strong hX hY) hZ, mem_strong_uniform hX (uniform_strong hY hZ),
    card_image_of_injective _ (Equiv.injective _), image_image, image_image]
  constructor
  · rintro ⟨hc, h1, h2, h3⟩
    have g := group_pair hr hX hY hc (fun x : (α × β) × γ => x.1.1) (fun x => x.1.2)
    have g' := group_pair hr hY hZ hc (fun x : (α × β) × γ => x.1.2) (fun x => x.2)
    have e1 : S.image Prod.fst = S.image fun x : (α × β) × γ => (x.1.1, x.1.2) := rfl
    rw [e1] at h1 h3
    obtain ⟨a, b⟩ := g.1.1 h1
    refine ⟨hc, a, g'.1.2 ⟨b, h2⟩, ?_⟩
    rcases h3 with e | e
    · obtain ⟨-, -, e | e⟩ := g.2.1 e
      · exact Or.inl e
      · exact Or.inr (g'.2.2 ⟨b, h2, Or.inl e⟩)
    · exact Or.inr (g'.2.2 ⟨b, h2, Or.inr e⟩)
  · rintro ⟨hc, h1, h2, h3⟩
    have g := group_pair hr hX hY hc (fun x : (α × β) × γ => x.1.1) (fun x => x.1.2)
    have g' := group_pair hr hY hZ hc (fun x : (α × β) × γ => x.1.2) (fun x => x.2)
    have e1 : S.image Prod.fst = S.image fun x : (α × β) × γ => (x.1.1, x.1.2) := rfl
    have e2 : S.image (Prod.snd ∘ ⇑(Equiv.prodAssoc α β γ)) =
        S.image fun x : (α × β) × γ => (x.1.2, x.2) := rfl
    have e3 : S.image (Prod.fst ∘ ⇑(Equiv.prodAssoc α β γ)) =
        S.image fun x : (α × β) × γ => x.1.1 := rfl
    rw [e2] at h2 h3
    rw [e3] at h1 h3
    obtain ⟨b, c⟩ := g'.1.1 h2
    rw [e1]
    refine ⟨hc, g.1.2 ⟨h1, b⟩, c, ?_⟩
    rcases h3 with e | e
    · exact Or.inl (g.2.2 ⟨h1, b, Or.inl e⟩)
    · obtain ⟨-, -, e | e⟩ := g'.2.1 e
      · exact Or.inl (g.2.2 ⟨h1, b, Or.inr e⟩)
      · exact Or.inr e

/-- **Lemma 2.2**: commutativity. -/
theorem iso_strong_comm (hX : Uniform r X) (hY : Uniform r Y) :
    IsoVia (strong X Y) (strong Y X) (Equiv.prodComm α β) := by
  intro S
  rw [mem_strong_uniform hX hY, mem_strong_uniform hY hX,
    card_image_of_injective _ (Equiv.injective _), image_image, image_image]
  have e1 : S.image (Prod.fst ∘ ⇑(Equiv.prodComm α β)) = S.image Prod.snd := rfl
  have e2 : S.image (Prod.snd ∘ ⇑(Equiv.prodComm α β)) = S.image Prod.fst := rfl
  rw [e1, e2]
  tauto

end assoc

/-! ## Lemma 3.1: factors are uniform -/

section factors

variable {V α γ : Type} [Fintype V] [Fintype α] [Fintype γ] {H : HG V} {X : HG α} {Y : HG γ}

/-- **Lemma 3.1** (uniformity part), left factor. -/
theorem uniform_left_of_iso [Nonempty γ] (hH : Uniform r H) (h : Iso H (strong X Y))
    (hX : ∀ e ∈ X.E, e.Nonempty) : Uniform r X := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨y⟩ := ‹Nonempty γ›
  intro e he
  set S := e.image fun a => (a, y)
  have hinj : Injective fun a : α => (a, y) := fun a b h => congrArg Prod.fst h
  have hS : S ∈ (strong X Y).E := by
    simp only [strong, mem_filter, mem_univ, true_and]
    left
    refine ⟨by rw [image_image]; simpa [Function.comp_def] using he, ?_⟩
    rw [image_image, show (Prod.snd ∘ fun a : α => (a, y)) = fun _ => y from rfl,
      image_const (hX e he), card_singleton]
  have h2 := (hφ (S.image φ.symm)).2 (by rwa [image_image_equiv])
  rw [← hH _ h2, card_image_of_injective _ φ.symm.injective, card_image_of_injective _ hinj]

/-- **Lemma 3.1** (uniformity part), right factor. -/
theorem uniform_right_of_iso [Nonempty α] (hH : Uniform r H) (h : Iso H (strong X Y))
    (hY : ∀ e ∈ Y.E, e.Nonempty) : Uniform r Y := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨x⟩ := ‹Nonempty α›
  intro f hf
  set S := f.image fun b => (x, b)
  have hinj : Injective fun b : γ => (x, b) := fun a b h => congrArg Prod.snd h
  have hS : S ∈ (strong X Y).E := by
    simp only [strong, mem_filter, mem_univ, true_and]
    right; left
    refine ⟨?_, by rw [image_image]; simpa [Function.comp_def] using hf⟩
    rw [image_image, show (Prod.fst ∘ fun b : γ => (x, b)) = fun _ => x from rfl,
      image_const (hY f hf), card_singleton]
  have h2 := (hφ (S.image φ.symm)).2 (by rwa [image_image_equiv])
  rw [← hH _ h2, card_image_of_injective _ φ.symm.injective, card_image_of_injective _ hinj]

end factors

/-! ## Lemma 3.2: boxes -/

section boxes

variable {α γ : Type} [Fintype α] [Fintype γ] {X : HG α} {Y : HG γ}

/-- Induced subhypergraph: the edges contained in `B`. -/
def induced {β : Type} (X : HG β) (B : Finset β) : HG β where
  E := X.E.filter fun e => e ⊆ B

lemma uniform_induced {β : Type} {X : HG β} (hX : Uniform r X) (B : Finset β) :
    Uniform r (induced X B) := fun e he => hX e (mem_filter.1 he).1

/-- **Lemma 3.2** (boxes). On `B₁ × B₂` the strong product `X ⊠ Y` agrees with
`X[B₁] ⊠ Y[B₂]`. -/
theorem mem_strong_box (hX : Uniform r X) (hY : Uniform r Y) (B1 : Finset α) (B2 : Finset γ)
    {S : Finset (α × γ)} (hS : S ⊆ B1 ×ˢ B2) :
    S ∈ (strong X Y).E ↔ S ∈ (strong (induced X B1) (induced Y B2)).E := by
  have s1 : S.image Prod.fst ⊆ B1 := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ha; exact (mem_product.1 (hS hx)).1
  have s2 : S.image Prod.snd ⊆ B2 := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 ha; exact (mem_product.1 (hS hx)).2
  have m1 : S.image Prod.fst ∈ (induced X B1).E ↔ S.image Prod.fst ∈ X.E := by
    simp only [induced, mem_filter, s1, and_true]
  have m2 : S.image Prod.snd ∈ (induced Y B2).E ↔ S.image Prod.snd ∈ Y.E := by
    simp only [induced, mem_filter, s2, and_true]
  rw [mem_strong_uniform hX hY, mem_strong_uniform (uniform_induced hX _)
    (uniform_induced hY _), SoE, SoE, SoE, SoE, m1, m2]

/-- **Lemma 3.2**, layers: the edges of `X ⊠ Y` inside `V(X) × {y}` are the sets `e × {y}`. -/
theorem mem_strong_layer (hr : 2 ≤ r) (hX : Uniform r X) (hY : Uniform r Y) (y : γ)
    {S : Finset (α × γ)} (hS : ∀ x ∈ S, x.2 = y) :
    S ∈ (strong X Y).E ↔ ∃ e ∈ X.E, S = e.image fun a => (a, y) := by
  constructor
  · intro h
    have hc := card_mem_strong hX hY h
    have hne : S.Nonempty := card_pos.1 (by omega)
    have c2 : (S.image Prod.snd).card = 1 :=
      card_image_eq_one hne fun x hx x' hx' => (hS x hx).trans (hS x' hx').symm
    have e1 : S.image Prod.fst ∈ X.E := by
      rw [mem_strong_uniform hX hY] at h
      rcases h.2.2.2 with e | e
      · exact e
      · have := hY _ e; omega
    refine ⟨_, e1, ext fun x => ?_⟩
    rw [mem_iff_of_snd hS, mem_image_mk_right]
  · rintro ⟨e, he, rfl⟩
    have hne : e.Nonempty := card_pos.1 (by rw [hX e he]; omega)
    simp only [strong, mem_filter, mem_univ, true_and]
    left
    refine ⟨by rw [image_image]; simpa [Function.comp_def] using he, ?_⟩
    rw [image_image, show (Prod.snd ∘ fun a : α => (a, y)) = fun _ => y from rfl,
      image_const hne, card_singleton]

end boxes

/-! ## The normal product -/

section normal

variable {α γ : Type} [Fintype α] [Fintype γ]

/-- Normal product: Cartesian edges and the sets `S ⊆ e₁ × e₂` with
`|S| = |p₁ S| = |p₂ S| = min (|e₁|, |e₂|)`. -/
def normal (X : HG α) (Y : HG γ) : HG (α × γ) where
  E := univ.filter fun S =>
    (S.image Prod.fst ∈ X.E ∧ (S.image Prod.snd).card = 1) ∨
    ((S.image Prod.fst).card = 1 ∧ S.image Prod.snd ∈ Y.E) ∨
    (∃ e1 ∈ X.E, ∃ e2 ∈ Y.E, S ⊆ e1 ×ˢ e2 ∧ S.card = (S.image Prod.fst).card ∧
      S.card = (S.image Prod.snd).card ∧ S.card = min e1.card e2.card)

/-- The normal and strong products agree on `r`-uniform factors. -/
theorem normal_eq_strong {X : HG α} {Y : HG γ} (hX : Uniform r X) (hY : Uniform r Y) :
    (normal X Y).E = (strong X Y).E := by
  ext S
  simp only [normal, strong, mem_filter, mem_univ, true_and]
  refine or_congr Iff.rfl (or_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨e1, he1, e2, he2, hsub, c1, c2, c3⟩
    rw [hX _ he1, hY _ he2, min_self] at c3
    have s1 : S.image Prod.fst ⊆ e1 := fun a ha => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha; exact (mem_product.1 (hsub hx)).1
    have s2 : S.image Prod.snd ⊆ e2 := fun a ha => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha; exact (mem_product.1 (hsub hx)).2
    have q1 : S.image Prod.fst = e1 := eq_of_subset_of_card_le s1 (by rw [hX _ he1]; omega)
    have q2 : S.image Prod.snd = e2 := eq_of_subset_of_card_le s2 (by rw [hY _ he2]; omega)
    refine ⟨q1 ▸ he1, q2 ▸ he2, ?_⟩
    rw [q1, q2, hX _ he1, hY _ he2, max_self]; exact c3
  · rintro ⟨h1, h2, hc⟩
    rw [hX _ h1, hY _ h2, max_self] at hc
    refine ⟨_, h1, _, h2, fun x hx => mem_product.2
      ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩, ?_, ?_, ?_⟩
    · rw [hX _ h1, hc]
    · rw [hY _ h2, hc]
    · rw [hX _ h1, hY _ h2, min_self, hc]

end normal

end HypProd
