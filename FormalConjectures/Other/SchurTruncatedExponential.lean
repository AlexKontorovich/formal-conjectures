/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Schur's theorem on Galois groups of truncated exponential polynomials

*Reference:* (https://math.stackexchange.com/questions/2814220/)

*Reference* (https://mathoverflow.net/questions/477077)
-/

/-
Note: This was asked by Nick Katz. Claude 4.0 Sonnet quasi-autoformalization is here:

-/

open Polynomial
open Classical

-- Define the truncated exponential polynomial
def truncatedExp (n : ℕ) : ℚ[X] :=
  ∑ j in Finset.range n, (1 / j.factorial : ℚ) • X ^ j

-- State Schur's theorem
theorem schur_theorem (n : ℕ) (hn : n ≥ 2) :
  let f := truncatedExp n
  let K := f.SplittingField
  if n % 4 = 0 then
    -- When n ≡ 0 (mod 4), Galois group is A_n
    ∃ φ : K ≃ₐ[ℚ] K, Equiv.Perm.IsAlt (Equiv.refl (Fin n)) ∧
    IsGalois ℚ K ∧
    ∃ (iso : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (f.roots K.toField)),
      ∀ σ : K ≃ₐ[ℚ] K, Equiv.Perm.IsAlt (iso σ)
  else
    -- When n ≢ 0 (mod 4), Galois group is S_n
    IsGalois ℚ K ∧
    ∃ (iso : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (f.roots K.toField)),
      Function.Surjective iso := by
  sorry

-- Alternative formulation using Galois group cardinality
theorem schur_theorem_card (n : ℕ) (hn : n ≥ 2) :
  let f := truncatedExp n
  let K := f.SplittingField
  IsGalois ℚ K ∧
  Irreducible f ∧
  if n % 4 = 0 then
    finrank ℚ K = n.factorial / 2
  else
    finrank ℚ K = n.factorial := by
  sorry

-- The polynomial is irreducible (part of Schur's result)
theorem truncatedExp_irreducible (n : ℕ) (hn : n ≥ 2) :
  Irreducible (truncatedExp n) := by
  sorry

-- The splitting field is Galois
theorem truncatedExp_isGalois (n : ℕ) (hn : n ≥ 2) :
  IsGalois ℚ (truncatedExp n).SplittingField := by
  sorry

-- More precise statement using the discriminant
theorem schur_discriminant_characterization (n : ℕ) (hn : n ≥ 2) :
  let f := truncatedExp n
  let disc := f.discriminant
  (n % 4 = 0) ↔ IsSquare disc := by
  sorry

-- Version that directly constructs the isomorphism to symmetric/alternating group
theorem schur_galois_group_iso (n : ℕ) (hn : n ≥ 2) :
  let f := truncatedExp n
  let K := f.SplittingField
  let roots := f.roots K.toField
  ∃ (iso : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm roots),
    if n % 4 = 0 then
      -- Image is alternating group
      ∀ σ : K ≃ₐ[ℚ] K, Equiv.Perm.IsAlt (iso σ) ∧
      ∀ τ : Equiv.Perm roots, Equiv.Perm.IsAlt τ → ∃ σ : K ≃ₐ[ℚ] K, iso σ = τ
    else
      -- Image is full symmetric group
      Function.Surjective iso := by
  sorry
