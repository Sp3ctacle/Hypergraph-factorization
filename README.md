# Lean formalization: hypergraph products

Lean `v4.37.0-rc1`, Mathlib master (Lake project `hg`, library `Hg`). Build: `lake new hg math`,
put the files under `Hg/`, `lake exe cache get`, `lake build`.

Numbering: the paper's current numbers (as used in `paper/algorithm.tex`) first, the uploaded PDF's in brackets.

| File | Contents |
|---|---|
| `HypergraphCancellation3.lean` | Strong/costrong cancellation and square roots, `cat_square`, `lovasz` |
| `Skeleton.lean` | skeleton [PDF Def 3.3], Lemma 3.3 [3.4] `skeleton` (binary) |
| `Iterated.lean` | `strongPi`; Lemma 2.2 (`mem_strong_uniform`, `iso_strongPi_sum`, `iso_strongPi_unique`, `iso_strong_assoc`, `iso_strong_comm`); Lemma 3.1 uniformity (`uniform_left_of_iso`, `uniform_right_of_iso`); Lemma 3.2 (`mem_strong_box`, `mem_strong_layer`); `normal_eq_strong` |
| `UPF.lean` | **Theorem 3.5 [3.6]** `unique_prime_factorization`; `skeleton_pi`; Steps 1–3 (`decomp_of_factorization`, `decomp_inf`, `decomp_coarsen`, `not_prime_of_split`) |
| `TwoSorted.lean` | Lemma 4.3 [4.4] `sqrtTS` (two-sorted Lovász, proved directly) |
| `Tilde.lean` | Prop 4.4 [4.5] (ii) `rdirect_square`, `maxDirect_eq`, `minDirect_eq`, (iii) `sq_square`; Lemmas 7.1–7.3, Props 7.4/7.5, flag lemma [PDF 7.7]; **Theorem 7.7 [7.8]** `tdp_square` |
| `LooseEnds.lean` | Cor 3.6 `sk_eq_of_linear`; Thm 6.2 normal clause `normal_cancel` and powers clause `strong_power` |

**Only axiom:** `cartesian_coordinatization` (UPF.lean), used only by
`unique_prime_factorization`. Packaged form of Sabidussi–Vizing + Imrich–Miller unique
coordinatization: a connected finite graph has a coordinatization `V ≃ Π k, U k` (all `U k`
nontrivial) of which every Cartesian factorization into nontrivial factors is a coarsening.

Conventions: iterated products are `strongPi` (Lemma 2.2's description), identified with any
bracketing of binary products by `iso_strongPi_sum` / `iso_strongPi_unique`. `HGPrime` uses the
binary survey strong product with nonempty-edge factors. Lemma 3.1's connectivity part and
the class 𝒫 clause of Theorem 7.7 are not formalized.
