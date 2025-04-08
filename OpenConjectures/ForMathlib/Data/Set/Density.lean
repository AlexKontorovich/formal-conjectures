/-
Copyright 2025 Google LLC

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

import Mathlib.Analysis.SpecificLimits.Basic
import OpenConjectures.ForMathlib.Algebra.Order.Group.Pointwise.Interval
import OpenConjectures.ForMathlib.Order.Interval.Finset.Basic
import OpenConjectures.ForMathlib.Order.Interval.Finset.Nat

open Filter

open scoped Topology

namespace Set

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => ((S ∩ A ∩ Set.Iio b).ncard : ℝ) / (A ∩ Set.Iio b).ncard)
    atTop (𝓝 α)

/-- In a directed non-trivial partial order with a least element, the set of all
elements has density one. -/
@[simp]
theorem hasDensity_univ {β : Type*} [PartialOrder β] [LocallyFiniteOrder β]
    [OrderBot β] [Nontrivial β] [IsDirected β fun x1 x2 ↦ x1 ≤ x2] :
    (@Set.univ β).HasDensity 1 := by
  simp [HasDensity]
  let ⟨b, hb⟩ := Set.Iio_eventually_ncard_ne_zero β
  exact Tendsto.congr'
    (eventually_atTop.2
      ⟨b, fun n hn => (div_self <| Nat.cast_ne_zero.2 (hb n hn)).symm⟩)
    tendsto_const_nhds

example : (@Set.univ ℕ).HasDensity 1 := hasDensity_univ

end Set

namespace Nat

open Set

/--
The natural density of the set of even numbers is `1 / 2`.
-/
theorem hasDensity_even : {n : ℕ | Even n}.HasDensity (1 / 2) := by
  simp [HasDensity]
  have h {n : ℕ} (hn : 1 ≤ n) : (({n : ℕ | Even n} ∩ Iio n).ncard : ℝ) / n =
      if Even n then 2⁻¹ else (n + 1 : ℝ) /  n * 2⁻¹ := by
    split_ifs with h
    · rw [← image_mul_two_Iio_even h, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), ncard_Iio,
        cast_div_charZero (even_iff_two_dvd.mp h), cast_ofNat,
        div_div_cancel_left' <| cast_ne_zero.2 (by linarith)]
    · replace h : Even (n + 1) := by simpa [Nat.even_add', ← Nat.not_even_iff_odd]
      rw [← image_mul_two_Iio n, ncard_image_of_injective _
          (mul_right_injective₀ (by simp)), ncard_Iio,
        cast_div (even_iff_two_dvd.mp h) (by norm_num), cast_add]; ring
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (h hn).symm⟩)
    (Tendsto.if' tendsto_const_nhds ?_)
  replace h : Tendsto (fun (k : ℕ) => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using Tendsto.const_add _ tendsto_one_div_atTop_nhds_zero_nat
  simpa using Tendsto.mul_const _ <|
    Tendsto.congr' (eventually_atTop.2 ⟨1, fun k hk => by field_simp⟩) h

/-- A finite set has natural density zero. -/
theorem hasDensity_zero_of_finite {S : Set ℕ} (h : S.Finite) :
    S.HasDensity 0 := by
  simp [HasDensity]
  have (n : ℕ) : ((S ∩ Set.Iio n).ncard : ℝ) / n ≤ S.ncard / n := by
    by_cases h₀ : n = 0; simp [← Ico_bot, h₀]
    exact div_le_div₀ (by simp) (by simpa using Set.ncard_inter_le_ncard_left _ _ h)
      (by simpa using n.pos_of_ne_zero h₀) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat S.ncard)
    (fun _ => div_nonneg (cast_nonneg _) (cast_nonneg _)) this

end Nat
