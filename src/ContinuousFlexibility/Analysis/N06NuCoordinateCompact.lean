module

public import ContinuousFlexibility.Analysis.N06NuStateSegments

/-!
# Uniform finite packets of actual nu-coordinate jets

For each fixed angular order the actual coordinate jets are uniformly
bounded on one ball in the original state seminorm. Their differences
retain a linear factor in that same seminorm and in the actual q change.
The radial coefficients are bounded on the fixed compact radial interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n06NuZeroCoordinates (D : ReferenceData) (r : ℝ) : N06NuJetCoordinates :=
  ![r, D.w r, deriv D.w r, D.chi r, deriv D.chi r, 0, 0, 0, 0, 0, 0, 0]

theorem n06_actualNuJetCoordinates_zero (S : PhysicalSpacesData)
    (D : ReferenceData) (r θ : ℝ) :
    n06ActualNuJetCoordinates D S (0, 0) (r, θ) = n06NuZeroCoordinates D r := by
  have hzero : stateU S (0 : AnnularState S) = (fun _ : PolarPoint => 0) := by
    change (heightPairFieldLinear S) (0 : HeightPair S) = _
    exact (heightPairFieldLinear S).map_zero
  have hrzero : radialPartial (fun _ : PolarPoint => 0) = (fun _ => 0) :=
    funext fun _ => radialPartial_const 0
  have htzero : heightAngular (fun _ : PolarPoint => 0) = (fun _ => 0) := by
    funext p
    simp only [heightAngular, angularPartial_const, zero_div]
  simp only [n06ActualNuJetCoordinates, n06NuZeroCoordinates, hzero,
    hrzero, htzero, angularPartial_const,
    Prod.fst_zero, Prod.snd_zero]

theorem n06NuZeroCoordinates_continuous
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi) :
    Continuous (n06NuZeroCoordinates D) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [n06NuZeroCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    first | exact continuous_id | exact hw.continuous | exact hχ.continuous |
      exact hw.continuous_deriv (by simp) | exact hχ.continuous_deriv (by simp) |
      exact continuous_const

def N06NuCoordinatesZeroAngularBound (D : ReferenceData) (S : PhysicalSpacesData)
    (B : ℝ) : Prop :=
  ∀ (j : ℕ) r, r ∈ radialCore D → ∀ θ,
    ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (0, 0) (r, t)) θ‖ ≤ B

/-- The zero state's coordinate curve is constant in the angle, with a
uniform radial bound for every angular derivative. -/
theorem n06_actualNuJetCoordinates_zero_angular_bound
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi) :
    ∃ B : ℝ, 0 ≤ B ∧ N06NuCoordinatesZeroAngularBound D S B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image
    (n06NuZeroCoordinates_continuous hw hχ).norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro j r hr θ
  have he : (fun t => n06ActualNuJetCoordinates D S (0, 0) (r, t)) =
      (fun _ : ℝ => n06NuZeroCoordinates D r) :=
    funext fun t => n06_actualNuJetCoordinates_zero S D r t
  rw [he, iteratedDeriv_const]
  split_ifs
  · exact (hB ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩).trans (le_max_left _ _)
  · simpa only [norm_zero] using le_max_right B 0

def N06NuCoordinateFiniteDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (L : ℝ) : Prop :=
  ∀ j, j ≤ n → ∀ (z w : AnnularState S × ℝ) r,
      r ∈ radialCore D → ∀ θ,
        ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ -
          iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S w (r, t)) θ‖ ≤
            L * (stateGrading S (n + 4) (z.1 - w.1) + |z.2 - w.2|)

/-- A common constant handles all actual angular jets through order n. -/
theorem n06_actualNuJetCoordinates_finite_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ N06NuCoordinateFiniteDifferenceBound D S n L := by
  classical
  have hchoices (i : Fin (n + 1)) :=
    n06_actualNuJetCoordinates_angular_difference_bound hD hT hS i.val
  choose c hc hbound using hchoices
  let L : ℝ := 1 + ∑ i : Fin (n + 1), c i
  have hc₀ (i : Fin (n + 1)) : 0 ≤ c i := zero_le_one.trans (hc i)
  have hsum : 0 ≤ ∑ i : Fin (n + 1), c i := Finset.sum_nonneg fun i _ => hc₀ i
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro j hj z w r hr θ
  let i : Fin (n + 1) := ⟨j, by omega⟩
  have hi : c i ≤ L := (Finset.single_le_sum (fun k _ => hc₀ k)
    (Finset.mem_univ i)).trans (by dsimp only [L]; linarith)
  have hgrade : stateGrading S (j + 4) (z.1 - w.1) ≤
      stateGrading S (n + 4) (z.1 - w.1) :=
    solve_stateGrading_monotone S (by omega) (z.1 - w.1)
  calc
    _ ≤ c i * (stateGrading S (j + 4) (z.1 - w.1) + |z.2 - w.2|) :=
      hbound i z w r hr θ
    _ ≤ c i * (stateGrading S (n + 4) (z.1 - w.1) + |z.2 - w.2|) :=
      mul_le_mul_of_nonneg_left (add_le_add hgrade (le_refl |z.2 - w.2|)) (hc₀ i)
    _ ≤ _ := mul_le_mul_of_nonneg_right hi
      (add_nonneg (apply_nonneg _ _) (abs_nonneg _))

def N06NuCoordinatesNearFixedState (D : ReferenceData) (S : PhysicalSpacesData)
    (x₀ : AnnularState S) (n : ℕ) (L M : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
        stateGrading S (n + 4) (z.1 - x₀) + |z.2| ≤ 1 →
        ∀ j, j ≤ n → ∀ r, r ∈ radialCore D → ∀ θ,
          ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ‖ ≤ M ∧
          ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ ≤ M ∧
          ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ -
            iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ ≤
              L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|)

/-- Uniform values and differences for the genuine coordinate curves on
a unit ball about any fixed original state. The constants precede z. -/
theorem n06_actualNuJetCoordinates_near_fixed_state
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hχ : ContDiff ℝ ∞ D.chi)
    (x₀ : AnnularState S) (n : ℕ) :
    ∃ L M : ℝ, 1 ≤ L ∧ 0 ≤ M ∧ N06NuCoordinatesNearFixedState D S x₀ n L M := by
  obtain ⟨L, hL, hdiff⟩ := n06_actualNuJetCoordinates_finite_difference_bound
    (D := D) (T := T) (S := S) hD hT hS n
  obtain ⟨B, hB, hzero⟩ := n06_actualNuJetCoordinates_zero_angular_bound
    (D := D) (S := S) hD.choose_spec.1.2.2.1.1 hχ
  let R : ℝ := B + L * stateGrading S (n + 4) x₀
  let M : ℝ := R + L
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hR : 0 ≤ R := add_nonneg hB (mul_nonneg hL₀ (apply_nonneg _ _))
  have hRM : R ≤ M := le_add_of_nonneg_right hL₀
  refine ⟨L, M, hL, add_nonneg hR hL₀, ?_⟩
  intro z hz j hj r hr θ
  have hrefdiff : ‖iteratedDeriv j
      (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ -
      iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (0, 0) (r, t)) θ‖ ≤
        L * stateGrading S (n + 4) x₀ := by
    simpa only [sub_zero, sub_self, abs_zero, add_zero] using
      hdiff j hj (x₀, 0) (0, 0) r hr θ
  have href : ‖iteratedDeriv j
      (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ ≤ R := by
    calc
      _ ≤ ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (0, 0) (r, t)) θ‖ +
          ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ -
            iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (0, 0) (r, t)) θ‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ ≤ R := add_le_add (hzero j r hr θ) hrefdiff
  have hzdiff : ‖iteratedDeriv j
      (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ -
      iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ ≤
        L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|) := by
    simpa only [sub_zero] using hdiff j hj z (x₀, 0) r hr θ
  have hscale : L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|) ≤ L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hL₀
  refine ⟨?_, href.trans hRM, hzdiff⟩
  calc
    _ ≤ ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ +
        ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ -
          iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S (x₀, 0) (r, t)) θ‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ R + L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|) := add_le_add href hzdiff
    _ ≤ M := add_le_add (le_refl R) hscale

end ContinuousFlexibility.Statements
