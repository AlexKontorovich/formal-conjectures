/-
Copyright 2026 The Formal Conjectures Authors.

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

import Mathlib

/-!
# Mandelbrot Local Connectivity Conjecture

The Mandelbrot local connectivity conjecture states
that the Mandelbrot set is locally connected.

More precisely, let
$$M = \{ c \in \mathbb{C} \mid \text{the orbit of } 0 \text{ under }
z \mapsto z^2 + c \text{ remains bounded} \}.$$
The conjecture asserts that `M` is locally connected as a topological space.

This conjecture is one of the central open problems in complex dynamics.
It has deep connections with the structure of Julia sets, renormalization,
and the density of hyperbolicity.

*References:*
* [Wikipedia: Mandelbrot set](https://en.wikipedia.org/wiki/Mandelbrot_set)
* Adrien Douady and John H. Hubbard, *Étude dynamique des polynômes complexes*
-/

open Set Complex Topology Metric Bornology

noncomputable section

/-- The quadratic map with parameter `c`. -/
def quadraticMap (c : ℂ) (z : ℂ) : ℂ :=
  z^2 + c

/--
The Mandelbrot set: the set of parameters `c : ℂ` for which the orbit of `0`
under iteration of `z ↦ z^2 + c` remains bounded.
-/
def mandelbrotSet : Set ℂ :=
  { c : ℂ |
      IsBounded
        (Set.range fun n : ℕ => (quadraticMap c)^[n] 0) }

lemma quadraticMap_ineq {c : ℂ} (hc : 2 ≤ ‖c‖) (n : ℕ) : ‖c‖ * (‖c‖ - 1) ^ n ≤ ‖(quadraticMap c)^[n + 1] 0‖ := by
    induction n with
    | zero => simp [quadraticMap]
    | succ n ih =>
      set z := (quadraticMap c)^[n + 1] 0 with hz_def
      rw [show (quadraticMap c)^[n + 1 + 1] 0 = (quadraticMap c z) by
        simp [Function.iterate_succ_apply', hz_def, quadraticMap]]
      unfold quadraticMap
      have key : ‖z‖ ^ 2 - ‖c‖ ≤ ‖z ^ 2 + c‖ := by
        have h := norm_sub_norm_le (z ^ 2) (-c)
        simp only [norm_pow, norm_neg, sub_neg_eq_add, tsub_le_iff_right] at h
        linarith
      rw [show (‖c‖ - 1) ^ (n + 1) = (‖c‖ - 1) ^ n * (‖c‖ - 1) by ring]
      have hpow : 1 ≤ (‖c‖ - 1) ^ n := one_le_pow₀ (by linarith : 1 ≤ ‖c‖ - 1)
      have hz : ‖c‖ ≤ ‖z‖ :=
        calc _ = ‖c‖ * 1 := (mul_one _).symm
             _ ≤ ‖c‖ * (‖c‖ - 1) ^ n := by apply mul_le_mul_of_nonneg_left hpow; simp
             _ ≤ _ := ih
      calc
        _ = ‖c‖ * (‖c‖ - 1) ^ n * (‖c‖ - 1) := by ring
        _ ≤ ‖z‖ * (‖c‖ - 1) := by
            apply mul_le_mul_of_nonneg_right ih; linarith
        _ ≤ ‖z‖ * (‖z‖ - 1) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg z); linarith
        _ = ‖z‖ ^ 2 - ‖z‖ := by ring
        _ ≤ ‖z‖ ^ 2 - ‖c‖ := by linarith
        _ ≤ _ := key

lemma not_isBounded_of_norm_gt_two {c : ℂ} (hc : 2 < ‖c‖) :
    ¬IsBounded (Set.range fun n : ℕ => (quadraticMap c)^[n] 0) := by
  have hc_pos : (0 : ℝ) < ‖c‖ := by linarith
  have hc1 : 1 < ‖c‖ - 1 := by linarith
  -- Key: ‖fⁿ⁺¹(0)‖ ≥ ‖c‖ · (‖c‖ − 1)ⁿ

  -- The orbit is unbounded: ‖c‖·(‖c‖−1)ⁿ → ∞ contradicts any finite bound
  intro hbdd
  rw [Metric.isBounded_iff] at hbdd
  obtain ⟨r, hr⟩ := hbdd
  have hr0 : (0 : ℂ) ∈ Set.range fun n : ℕ => (quadraticMap c)^[n] 0 := ⟨0, rfl⟩
  have hbound : ∀ n : ℕ, ‖(quadraticMap c)^[n + 1] 0‖ ≤ r := fun n => by
    have h := hr ⟨n + 1, rfl⟩ hr0
    simpa [dist_zero_right] using h
  have htend : Filter.Tendsto (fun n : ℕ => ‖c‖ * (‖c‖ - 1) ^ n) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).const_mul_atTop hc_pos
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop_atTop.mp htend (r + 1)).exists
  linarith [lb n, hbound n]


/-- If ‖c‖ > 2, the orbit of 0 is unbounded. -/
lemma not_isBounded_of_norm_gt_two {c : ℂ} (hc : 2 < ‖c‖) :
    ¬IsBounded (Set.range fun n : ℕ => (quadraticMap c)^[n] 0) := by
  sorry -- inductive argument: ‖fⁿ(0)‖ → ∞

theorem isBounded_mandelbrotSet : IsBounded mandelbrotSet := by
  apply (isBounded_closedBall (r := 2)).subset
  intro c hc
  simp only [mem_closedBall, dist_zero_right]
  by_contra h
  push_neg at h
  exact not_isBounded_of_norm_gt_two h hc

#exit

theorem isBounded_mandelbrotSet : IsBounded mandelbrotSet := by
  have : mandelbrotSet ⊆ Metric.closedBall 0 2 := by
    rintro c hc
    obtain ⟨R, hR⟩ := hc
    simp only [mem_closedBall, dist_zero_right]
    simp only [compl_compl, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hR

    sorry
  apply isBounded_closedBall.subset this

theorem mandelbrotSet_eq : mandelbrotSet =
  ⋂ n : ℕ, {c | ‖(quadraticMap c)^[n] 0‖ ≤ 2} := by
    sorry

theorem isClosed_mandelbrotSet : IsClosed mandelbrotSet := by
  sorry


theorem isCompact_mandelbrotSet :
    IsCompact mandelbrotSet := by
  rw [isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_mandelbrotSet, isBounded_mandelbrotSet⟩

/--
A subset `s` of a topological space is locally connected if every point has a
basis of connected neighborhoods in the subspace topology on `s`.
-/
def IsLocallyConnected {α : Type*} [TopologicalSpace α] (s : Set α) : Prop :=
  ∀ x : s, ∀ U : Set s,
    IsOpen U →
    x ∈ U →
    ∃ V : Set s,
      V ⊆ U ∧
      IsOpen V ∧
      x ∈ V ∧
      IsPreconnected V

/--
The Mandelbrot Local Connectivity Conjecture:
the Mandelbrot set is locally connected.
-/
theorem MandelbrotLocalConnectivity :
    IsLocallyConnected mandelbrotSet := by
  sorry
