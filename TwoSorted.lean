/-
# Two-sorted structures and their Lovász square-root theorem (paper's Lemma 4.3 / PDF 4.4)

A two-sorted structure has points `P`, blocks `B` and relations `R j ⊆ P × B` (`j : J`).
Products are taken sortwise. `sqrtTS`: `S × S ≅ T × T → S ≅ T`.

The proof is the homomorphism-counting argument of `HypProd.lovasz`, done directly for
two-sorted structures (kernels are pairs of setoids, one per sort).
-/
import Hg.HypergraphCancellation3

open Finset Function

open scoped Classical

attribute [-instance] instDecidableEqProd Fintype.decidablePiFintype

noncomputable section

namespace HypProd

/-- A two-sorted structure with relations indexed by `J`. -/
structure TS (P B J : Type) where
  R : J → Finset (P × B)

variable {J : Type} {P B P' B' P'' B'' : Type} [Fintype P] [Fintype B] [Fintype P'] [Fintype B']
  [Fintype P''] [Fintype B'']

/-- `(f, g)` is a homomorphism. -/
def IsHomTS (X : TS P B J) (S : TS P' B' J) (f : P → P') (g : B → B') : Prop :=
  ∀ j, ∀ x ∈ X.R j, (f x.1, g x.2) ∈ S.R j

def homCardTS (X : TS P B J) (S : TS P' B' J) : ℕ :=
  Fintype.card {fg : (P → P') × (B → B') // IsHomTS X S fg.1 fg.2}

def injCardTS (X : TS P B J) (S : TS P' B' J) : ℕ :=
  Fintype.card {fg : (P → P') × (B → B') //
    Injective fg.1 ∧ Injective fg.2 ∧ IsHomTS X S fg.1 fg.2}

/-- Isomorphism of two-sorted structures. -/
def IsoTS (S : TS P B J) (T : TS P' B' J) : Prop :=
  ∃ (f : P ≃ P') (g : B ≃ B'), ∀ j (x : P × B), x ∈ S.R j ↔ (f x.1, g x.2) ∈ T.R j

/-- Sortwise product. -/
def prodTS (S : TS P B J) (T : TS P' B' J) : TS (P × P') (B × B') J :=
  ⟨fun j => univ.filter fun x => (x.1.1, x.2.1) ∈ S.R j ∧ (x.1.2, x.2.2) ∈ T.R j⟩

lemma mem_prodTS {S : TS P B J} {T : TS P' B' J} {j : J} {x : (P × P') × (B × B')} :
    x ∈ (prodTS S T).R j ↔ (x.1.1, x.2.1) ∈ S.R j ∧ (x.1.2, x.2.2) ∈ T.R j := by
  simp only [prodTS, mem_filter, mem_univ, true_and]

lemma homCardTS_prod (X : TS P B J) (S : TS P' B' J) (T : TS P'' B'' J) :
    homCardTS X (prodTS S T) = homCardTS X S * homCardTS X T := by
  unfold homCardTS
  rw [← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun h =>
        (⟨(Prod.fst ∘ h.1.1, Prod.fst ∘ h.1.2), fun j x hx => (mem_prodTS.1 (h.2 j x hx)).1⟩,
         ⟨(Prod.snd ∘ h.1.1, Prod.snd ∘ h.1.2), fun j x hx => (mem_prodTS.1 (h.2 j x hx)).2⟩)
      invFun := fun p => ⟨(fun a => (p.1.1.1 a, p.2.1.1 a), fun b => (p.1.1.2 b, p.2.1.2 b)),
        fun j x hx => mem_prodTS.2 ⟨p.1.2 j x hx, p.2.2 j x hx⟩⟩
      left_inv := fun h => rfl
      right_inv := fun p => rfl }

lemma homCardTS_congr (X : TS P B J) {S : TS P' B' J} {T : TS P'' B'' J} (h : IsoTS S T) :
    homCardTS X S = homCardTS X T := by
  obtain ⟨f, g, hfg⟩ := h
  unfold homCardTS
  exact Fintype.card_congr
    { toFun := fun h => ⟨(f ∘ h.1.1, g ∘ h.1.2), fun j x hx => (hfg j _).1 (h.2 j x hx)⟩
      invFun := fun h => ⟨(f.symm ∘ h.1.1, g.symm ∘ h.1.2), fun j x hx => by
        rw [hfg]; simpa using h.2 j x hx⟩
      left_inv := fun h => Subtype.ext (Prod.ext (funext fun _ => by simp)
        (funext fun _ => by simp))
      right_inv := fun h => Subtype.ext (Prod.ext (funext fun _ => by simp)
        (funext fun _ => by simp)) }

/-! ## Counting through kernels -/

/-- Quotient of a two-sorted structure by a pair of setoids. -/
def quotTS (X : TS P B J) (s1 : Setoid P) (s2 : Setoid B) :
    TS (Quotient s1) (Quotient s2) J :=
  ⟨fun j => (X.R j).image fun x => (Quotient.mk s1 x.1, Quotient.mk s2 x.2)⟩

def fibTS (X : TS P B J) (S : TS P' B' J) (s1 : Setoid P) (s2 : Setoid B) : ℕ :=
  Fintype.card {h : {fg : (P → P') × (B → B') // IsHomTS X S fg.1 fg.2} //
    Setoid.ker h.1.1 = s1 ∧ Setoid.ker h.1.2 = s2}

def fiberEquivTS (X : TS P B J) (S : TS P' B' J) (s1 : Setoid P) (s2 : Setoid B) :
    {h : {fg : (P → P') × (B → B') // IsHomTS X S fg.1 fg.2} //
      Setoid.ker h.1.1 = s1 ∧ Setoid.ker h.1.2 = s2} ≃
    {gh : (Quotient s1 → P') × (Quotient s2 → B') //
      Injective gh.1 ∧ Injective gh.2 ∧ IsHomTS (quotTS X s1 s2) S gh.1 gh.2} where
  toFun h := ⟨(Quotient.lift h.1.1.1 (fun a b hab => by
                  have hk : Setoid.ker h.1.1.1 a b := by rw [h.2.1]; exact hab
                  exact hk),
               Quotient.lift h.1.1.2 (fun a b hab => by
                  have hk : Setoid.ker h.1.1.2 a b := by rw [h.2.2]; exact hab
                  exact hk)),
              by
                intro x y
                refine Quotient.inductionOn₂ x y fun a b hab => Quotient.sound ?_
                have hk : Setoid.ker h.1.1.1 a b := hab
                rw [h.2.1] at hk
                exact hk,
              by
                intro x y
                refine Quotient.inductionOn₂ x y fun a b hab => Quotient.sound ?_
                have hk : Setoid.ker h.1.1.2 a b := hab
                rw [h.2.2] at hk
                exact hk,
              by
                intro j x' hx'
                obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
                exact h.1.2 j x hx⟩
  invFun g := ⟨⟨(g.1.1 ∘ Quotient.mk s1, g.1.2 ∘ Quotient.mk s2), fun j x hx =>
      g.2.2.2 j _ (mem_image_of_mem _ hx)⟩,
    Setoid.ext fun a b =>
      ⟨fun h => Quotient.exact (g.2.1 h), fun h => congrArg g.1.1 (Quotient.sound h)⟩,
    Setoid.ext fun a b =>
      ⟨fun h => Quotient.exact (g.2.2.1 h), fun h => congrArg g.1.2 (Quotient.sound h)⟩⟩
  left_inv h := Subtype.ext (Subtype.ext rfl)
  right_inv g := Subtype.ext (Prod.ext (funext fun x => Quotient.inductionOn x fun _ => rfl)
    (funext fun x => Quotient.inductionOn x fun _ => rfl))

lemma homCardTS_eq_sum_fib (X : TS P B J) (S : TS P' B' J) :
    homCardTS X S = ∑ p : Setoid P × Setoid B, fibTS X S p.1 p.2 := by
  unfold homCardTS fibTS
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun h : {fg : (P → P') × (B → B') // IsHomTS X S fg.1 fg.2} =>
      (Setoid.ker h.1.1, Setoid.ker h.1.2))), Fintype.card_sigma]
  refine sum_congr rfl fun p _ => Fintype.card_congr (Equiv.subtypeEquivRight fun h => ?_)
  exact Prod.ext_iff

lemma fibTS_bot (X : TS P B J) (S : TS P' B' J) : fibTS X S ⊥ ⊥ = injCardTS X S := by
  unfold fibTS injCardTS
  exact Fintype.card_congr
    { toFun := fun h => ⟨h.1.1, Setoid.ker_eq_bot_iff.1 h.2.1, Setoid.ker_eq_bot_iff.1 h.2.2,
        h.1.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.2.2⟩, Setoid.ker_eq_bot_iff.2 g.2.1,
        Setoid.ker_eq_bot_iff.2 g.2.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma fibTS_eq (X : TS P B J) (S : TS P' B' J) (s1 : Setoid P) (s2 : Setoid B) :
    fibTS X S s1 s2 = injCardTS (quotTS X s1 s2) S := by
  unfold fibTS injCardTS
  convert Fintype.card_congr (fiberEquivTS X S s1 s2)

/-- Equal homomorphism counts from every structure give equal injective counts. -/
theorem injCardTS_eq (S : TS P' B' J) (T : TS P'' B'' J)
    (h : ∀ (P B : Type) [Fintype P] [Fintype B] (X : TS P B J), homCardTS X S = homCardTS X T) :
    ∀ (n : ℕ) (P B : Type) [Fintype P] [Fintype B], Fintype.card P + Fintype.card B = n →
      ∀ X : TS P B J, injCardTS X S = injCardTS X T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P B _ _ hn X
    have hS := homCardTS_eq_sum_fib X S
    have hT := homCardTS_eq_sum_fib X T
    rw [← add_sum_erase _ _ (mem_univ (⊥, ⊥))] at hS hT
    have hrest : ∑ p ∈ univ.erase (⊥, ⊥), fibTS X S p.1 p.2 =
        ∑ p ∈ univ.erase (⊥, ⊥), fibTS X T p.1 p.2 := by
      refine sum_congr rfl fun p hp => ?_
      rw [fibTS_eq, fibTS_eq]
      have hne : p ≠ (⊥, ⊥) := ne_of_mem_erase hp
      have hlt : Fintype.card (Quotient p.1) + Fintype.card (Quotient p.2) < n := by
        have l1 : Fintype.card (Quotient p.1) ≤ Fintype.card P :=
          Fintype.card_le_of_surjective _ Quotient.mk_surjective
        have l2 : Fintype.card (Quotient p.2) ≤ Fintype.card B :=
          Fintype.card_le_of_surjective _ Quotient.mk_surjective
        by_cases h1 : p.1 = ⊥
        · have h2 : p.2 ≠ ⊥ := fun h2 => hne (Prod.ext h1 h2)
          have := card_quotient_lt h2
          omega
        · have := card_quotient_lt h1
          omega
      exact ih _ hlt _ _ rfl _
    have := h P B X
    rw [fibTS_bot] at hS
    rw [fibTS_bot] at hT
    omega

/-- **Lovász-type theorem** for two-sorted structures. -/
theorem lovaszTS {S : TS P' B' J} {T : TS P'' B'' J}
    (h : ∀ (P B : Type) [Fintype P] [Fintype B] (X : TS P B J), homCardTS X S = homCardTS X T) :
    IsoTS S T := by
  have hinj := injCardTS_eq S T h
  have pos : ∀ {Q C : Type} [Fintype Q] [Fintype C] (U : TS Q C J), 0 < injCardTS U U := by
      intro Q C _ _ U
      have : Nonempty {fg : (Q → Q) × (C → C) //
          Injective fg.1 ∧ Injective fg.2 ∧ IsHomTS U U fg.1 fg.2} :=
        ⟨⟨(id, id), injective_id, injective_id, fun j x hx => by simpa using hx⟩⟩
      exact Fintype.card_pos
  have hST := pos S
  have hTS := pos T
  rw [hinj _ P' B' rfl S] at hST
  rw [← hinj _ P'' B'' rfl T] at hTS
  obtain ⟨⟨⟨f, g⟩, hf, hg, hfg⟩⟩ := Fintype.card_pos_iff.1 hST
  obtain ⟨⟨⟨f', g'⟩, hf', hg', hfg'⟩⟩ := Fintype.card_pos_iff.1 hTS
  have c1 : Fintype.card P' = Fintype.card P'' :=
    le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective f' hf')
  have c2 : Fintype.card B' = Fintype.card B'' :=
    le_antisymm (Fintype.card_le_of_injective g hg) (Fintype.card_le_of_injective g' hg')
  have bf : Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, c1⟩
  have bg : Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, c2⟩
  have hm : Injective fun x : P' × B' => (f x.1, g x.2) :=
    fun x y hxy => Prod.ext (hf (congrArg Prod.fst hxy)) (hg (congrArg Prod.snd hxy))
  have hm' : Injective fun x : P'' × B'' => (f' x.1, g' x.2) :=
    fun x y hxy => Prod.ext (hf' (congrArg Prod.fst hxy)) (hg' (congrArg Prod.snd hxy))
  refine ⟨Equiv.ofBijective f bf, Equiv.ofBijective g bg, fun j x => ?_⟩
  have sub : (S.R j).image (fun x : P' × B' => (f x.1, g x.2)) ⊆ T.R j := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hfg j x hx
  have sub' : (T.R j).image (fun x : P'' × B'' => (f' x.1, g' x.2)) ⊆ S.R j := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hfg' j x hx
  have k1 := card_le_card sub
  have k2 := card_le_card sub'
  rw [card_image_of_injective _ hm] at k1
  rw [card_image_of_injective _ hm'] at k2
  have heq : (S.R j).image (fun x : P' × B' => (f x.1, g x.2)) = T.R j :=
    eq_of_subset_of_card_le sub (by rw [card_image_of_injective _ hm]; omega)
  simp only [Equiv.ofBijective_apply]
  constructor
  · exact fun hx => hfg j x hx
  · intro hx
    have hx' : (f x.1, g x.2) ∈ (S.R j).image (fun x : P' × B' => (f x.1, g x.2)) := by
      rw [heq]; exact hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 hx'
    rwa [← hm hyx]

/-- **Lemma 4.3 / PDF 4.4**: square roots of two-sorted structures are unique. -/
theorem sqrtTS {S : TS P' B' J} {T : TS P'' B'' J} (h : IsoTS (prodTS S S) (prodTS T T)) :
    IsoTS S T := by
  refine lovaszTS fun P B _ _ X => ?_
  have e := homCardTS_congr X h
  rw [homCardTS_prod, homCardTS_prod] at e
  exact Nat.pow_left_injective two_ne_zero
    (show homCardTS X S ^ 2 = homCardTS X T ^ 2 by rw [sq, sq]; exact e)

end HypProd
