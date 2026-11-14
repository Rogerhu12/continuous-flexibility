module

public import ContinuousFlexibility.Analysis.N01aReferenceNormalization
public import ContinuousFlexibility.Analysis.N01aNegativeComponentGeometry
public import ContinuousFlexibility.Blueprint.Statements

/-!
# Assembly of the reference and optical-control geometry

The supplied enumeration and actual controls determine the endpoint and
travel fields. Their cell map is the identity. The reference height comes
from the existing normalized Sobolev representation. The three ordinary
flow candidates have no conditions in Part A and are set to zero here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n01aGeometryOfControls {D : ReferenceData} (S : PhysicalSpacesData)
    (e : ℕ ≃ N01aNegativeComponent D) (χ : ℕ → ℝ → ℝ) (x : AnnularState S) :
    NonlinearGeometryData S where
  control := χ
  cell := id
  left := fun m => (e m).left
  right := fun m => (e m).right
  travel := fun m => radialTravel D (e m).left (e m).right
  referenceState := x
  minusFlow := fun _ _ _ _ => 0
  minusReturnInverse := fun _ _ _ => 0
  rightChartInverse := fun _ _ _ => 0

theorem n01aGeometryOfControls_controlGeometry {D : ReferenceData} {S : PhysicalSpacesData}
    (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D)
    (e : ℕ ≃ N01aNegativeComponent D) (χ : ℕ → ℝ → ℝ) (x : AnnularState S)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧
      tsupport (χ m) ⊆ (e m).interval)
    (hderiv : ∀ m, HasDerivAt
      (fun t : ℝ => ∫ r in (e m).left..(e m).right,
        Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * χ m s)) r /
          (r * (D.w r * Real.exp (t * χ m r))))) 1 0) :
    controlGeometryConditions D S (n01aGeometryOfControls S e χ x) := by
  have hsupp : ∀ m, Function.support (χ m) ⊆ (e m).interval :=
    fun m => (subset_tsupport (χ m)).trans (hχ m).2.2
  dsimp only [controlGeometryConditions, n01aGeometryOfControls]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hderiv⟩
  · intro m
    exact ⟨(e m).property.1, (e m).left_lt_right, (e m).property.2.2.1⟩
  · intro m
    exact ⟨(e m).left_zero, (e m).right_zero, (e m).simple_endpoints hD⟩
  · intro m n hmn
    exact N01aNegativeComponent.pairwise_disjoint (fun he => hmn (e.injective he))
  · intro m r hr
    exact (e m).negative hr
  · intro r hr hneg
    obtain ⟨l, h, hcomp, hrcomp⟩ := hR.1 r hr hneg
    let J : N01aNegativeComponent D := ⟨(l, h), hcomp⟩
    refine ⟨e.symm J, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hrcomp
  · intro m
    exact hχ m
  · exact n01aNegativeComponent_supports_locallyFinite hD e χ hsupp
  · intro m
    rfl

/-- Assembly preserves the supplied actual material and Sobolev models and
proves every conjunct of the frozen Part A statement. -/
theorem exists_n01a_controlGeometry {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hphi : HeightMember D T referenceBeta
      (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2))
    (e : ℕ ≃ N01aNegativeComponent D) (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧
      tsupport (χ m) ⊆ (e m).interval)
    (hderiv : ∀ m, HasDerivAt
      (fun t : ℝ => ∫ r in (e m).left..(e m).right,
        Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * χ m s)) r /
          (r * (D.w r * Real.exp (t * χ m r))))) 1 0)
    (hjets : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
      |iteratedDeriv s (χ m) r| ≤ B * T.E0 (T.sample m) ^ B) :
    ∃ C : NonlinearGeometryData S,
      IsMaterialData D T ∧ IsPhysicalSpaces D T S ∧ Blueprint.N01PartA D T S C := by
  obtain ⟨x, hx⟩ := exists_referenceState_of_heightMember hS hD.2.2.2.1 hphi
  obtain ⟨A, hprofile⟩ := hD.1
  refine ⟨n01aGeometryOfControls S e χ x, hT, hS, hD, ?_,
    n01aGeometryOfControls_controlGeometry hprofile.1 hD.2.2.1 e χ x hχ hderiv, ?_, ?_⟩
  · simpa only [referenceStateConditions, n01aGeometryOfControls] using hx
  · refine ⟨1, zero_lt_one, fun m => ?_⟩
    simp only [n01aGeometryOfControls, id_eq, sub_self, abs_zero]
    exact zero_le_one
  · intro s
    obtain ⟨B, hB, hb⟩ := hjets s
    refine ⟨B, hB, fun m r hr => ?_⟩
    simpa only [n01aGeometryOfControls, id_eq] using hb m r

end ContinuousFlexibility.Statements
