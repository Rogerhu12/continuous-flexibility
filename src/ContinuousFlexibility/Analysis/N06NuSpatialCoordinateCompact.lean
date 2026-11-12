import ContinuousFlexibility.Analysis.N06NuSpatialCoordinateBounds
import ContinuousFlexibility.Analysis.N06NuCoordinateCompact

/-!
# Uniform physical spatial packets near a fixed state

The zero-state packet is a fixed smooth radial field. The actual spatial
packet difference bound then gives simultaneous value and derivative
bounds on one ball in the original order n+4 state seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n06NuZeroCoordinates_contDiff
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi) :
    ContDiff ℝ ∞ (n06NuZeroCoordinates D) := by
  have hwr := (contDiff_infty_iff_deriv.mp hw).2
  have hχr := (contDiff_infty_iff_deriv.mp hχ).2
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp only [n06NuZeroCoordinates, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
  | exact contDiff_id
  | exact hw
  | exact hwr
  | exact hχ
  | exact hχr
  | exact contDiff_const

theorem n06_actualNuJetCoordinates_zero_spatial_bound
    (hD : IsAccumulatingProfile D) (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (0, 0)) p‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := n06_radialLift_finite_frechet_bound (b := D.b)
    hD.choose_spec.1.1
    (n06NuZeroCoordinates_contDiff hD.choose_spec.1.2.2.1.1 hχ).contDiffOn n
  have he : n06ActualNuJetCoordinates D S (0, 0) =
      (fun p : PolarPoint => n06NuZeroCoordinates D p.1) :=
    funext fun p => n06_actualNuJetCoordinates_zero S D p.1 p.2
  refine ⟨B, hB, ?_⟩
  intro k hk p hp
  exact (congrArg (fun f : PolarPoint → N06NuJetCoordinates =>
    ‖iteratedFDeriv ℝ k f p‖) he).trans_le (hbound k hk p ⟨hp.1.1.le, hp.1.2.le⟩)

def N06NuSpatialCoordinatesNearFixedState (D : ReferenceData) (S : PhysicalSpacesData)
    (x₀ : AnnularState S) (n : ℕ) (L M : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    stateGrading S (n + 4) (z.1 - x₀) + |z.2| ≤ 1 →
    ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S z) p‖ ≤ M ∧
      ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (x₀, 0)) p‖ ≤ M ∧
      ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S z) p -
        iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (x₀, 0)) p‖ ≤
          L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|)

/-- Both constants precede the current state. The full physical packet
retains a linear difference factor, uniformly at every angle. -/
theorem n06_actualNuJetCoordinates_spatial_near_fixed_state
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hχ : ContDiff ℝ ∞ D.chi)
    (x₀ : AnnularState S) (n : ℕ) :
    ∃ L M : ℝ, 1 ≤ L ∧ 0 ≤ M ∧
      N06NuSpatialCoordinatesNearFixedState D S x₀ n L M := by
  obtain ⟨L, hL, hdiff⟩ := n06_actualNuJetCoordinates_spatial_difference_bound hD hT hS hχ n
  obtain ⟨B, hB, hzero⟩ := n06_actualNuJetCoordinates_zero_spatial_bound
    (S := S) hD hχ n
  let R : ℝ := B + L * stateGrading S (n + 4) x₀
  let M : ℝ := R + L
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hR : 0 ≤ R := add_nonneg hB (mul_nonneg hL₀ (apply_nonneg _ _))
  have hRM : R ≤ M := le_add_of_nonneg_right hL₀
  refine ⟨L, M, hL, add_nonneg hR hL₀, ?_⟩
  intro z hz k hk p hp
  have hrefdiff : ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (x₀, 0)) p -
      iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (0, 0)) p‖ ≤
        L * stateGrading S (n + 4) x₀ := by
    simpa only [sub_zero, sub_self, abs_zero, add_zero] using hdiff (x₀, 0) (0, 0) k hk p hp
  have href : ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (x₀, 0)) p‖ ≤ R :=
    (norm_le_norm_add_norm_sub' _ _).trans (add_le_add (hzero k hk p hp) hrefdiff)
  have hzdiff : ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S z) p -
      iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S (x₀, 0)) p‖ ≤
        L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|) := by
    simpa only [sub_zero] using hdiff z (x₀, 0) k hk p hp
  have hscale : L * (stateGrading S (n + 4) (z.1 - x₀) + |z.2|) ≤ L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hL₀
  refine ⟨?_, href.trans hRM, hzdiff⟩
  exact (norm_le_norm_add_norm_sub' _ _).trans
    ((add_le_add href hzdiff).trans (add_le_add le_rfl hscale))

end ContinuousFlexibility.Statements
