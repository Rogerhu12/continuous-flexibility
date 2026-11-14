module

public import ContinuousFlexibility.Analysis.N01aControlGeometryAssembly
public import ContinuousFlexibility.Analysis.N01cPrimitiveGeometry
public import ContinuousFlexibility.Analysis.N01cCoefficientRadialPowerInputs

/-!
# N01a controls with their actual containing cells

The same normalized optical controls and reference state are assembled
with the containing host map. The index comparison is a proved input
about that map; no identity-cell replacement is made.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem exists_n01c_controlGeometry_with_hosts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hphi : HeightMember D T referenceBeta
      (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2))
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hprimitive : N01RadialPrimitiveGeometry D)
    (host : N01aNegativeComponent D → ℕ)
    (hhost : ∀ J, J.interval ⊆ D.cells (host J))
    (e : ℕ ≃ N01aNegativeComponent D)
    (hshift : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(D.cellIndex (host (e m)) : ℝ) - D.cellIndex m| ≤ B)
    (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧
      tsupport (χ m) ⊆ (e m).interval)
    (hderiv : ∀ m, HasDerivAt
      (fun t : ℝ => ∫ r in (e m).left..(e m).right,
        Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * χ m s)) r /
          (r * (D.w r * Real.exp (t * χ m r))))) 1 0)
    (hjets : ∀ s, ∃ B : ℝ, 0 < B ∧ ∀ m r,
      |iteratedDeriv s (χ m) r| ≤ B * radialE (D.cellIndex (host (e m))) ^ B) :
    ∃ C : NonlinearGeometryData S,
      IsMaterialData D T ∧ IsPhysicalSpaces D T S ∧ N01PartA D T S C ∧
      N01PrimitiveGeometry D T S C := by
  obtain ⟨x, hx⟩ := exists_referenceState_of_heightMember hS hD.2.2.2.1 hphi
  let C : NonlinearGeometryData S :=
    { n01aGeometryOfControls S e χ x with cell := fun m => host (e m) }
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  have hpart : RadialPartition D := hD.1.choose_spec.2.1
  have hA : N01PartA D T S C := by
    refine ⟨hD, ?_, ?_, hshift, ?_⟩
    · simpa only [C, referenceStateConditions, n01aGeometryOfControls] using hx
    · exact n01aGeometryOfControls_controlGeometry hD.1.choose_spec.1 hD.2.2.1
        e χ x hχ hderiv
    · intro s
      obtain ⟨B, hB, hb⟩ := hjets s
      obtain ⟨A, K, hA, hK, hweight⟩ :=
        radialE_cell_rpow_le_E0 hT hD.1 hE B hB.le
      let J : ℝ := max (B * A) (max K 1)
      have hJ : 0 < J := zero_lt_one.trans_le
        ((le_max_right K 1).trans (le_max_right _ _))
      have hBA : B * A ≤ J := le_max_left _ _
      have hKJ : K ≤ J := (le_max_left K 1).trans (le_max_right _ _)
      refine ⟨J, hJ, fun m r _ => ?_⟩
      have hEone : 1 ≤ T.E0 (T.sample (host (e m))) :=
        hE _ (hpart.2.2.2.1 _ (hsample _))
      calc
        |iteratedDeriv s (χ m) r| ≤
            B * radialE (D.cellIndex (host (e m))) ^ B := hb m r
        _ ≤ B * (A * T.E0 (T.sample (host (e m))) ^ K) :=
          mul_le_mul_of_nonneg_left (hweight _ _ (hsample _)) hB.le
        _ = (B * A) * T.E0 (T.sample (host (e m))) ^ K := (mul_assoc _ _ _).symm
        _ ≤ J * T.E0 (T.sample (host (e m))) ^ J :=
          mul_le_mul hBA (Real.rpow_le_rpow_of_exponent_le hEone hKJ)
            (Real.rpow_nonneg (zero_le_one.trans hEone) K) hJ.le
  exact ⟨C, hT, hS, hA,
    n01PrimitiveGeometry_of_radialConstruction hT hA hE hprimitive (fun m => hhost (e m))⟩

end ContinuousFlexibility.Statements
