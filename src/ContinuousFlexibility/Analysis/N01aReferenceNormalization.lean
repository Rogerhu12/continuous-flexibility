module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Normalization of the reference height

The positive cosine modes are normalized for the actual angular average in
the radial statement.  Consequently the true border already normalizes the
reference height; there is no second choice of a scalar normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem radialAngularMean_cosineMode (j : ℕ) (hj : 0 < j) :
    radialAngularMean (Radial.cosineMode j) = 0 := by
  simpa only [radialAngularMean, Radial.angularAverage, one_div] using
    Radial.angularAverage_cosineMode j hj

theorem radialAngularMean_cosineMode_product (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    radialAngularMean (fun θ => Radial.cosineMode j θ * Radial.cosineMode k θ) =
      if j = k then 1 else 0 := by
  simpa only [radialAngularMean, Radial.angularPairing, Radial.angularAverage, one_div] using
    Radial.angularPairing_cosineMode j k hj hk

/-- The positive-mode coefficient of an actual separated cosine field. -/
theorem referenceMode_cosine_field (f : ℝ → ℝ) (j k : ℕ)
    (hj : 0 < j) (hk : 0 < k) (r : ℝ) :
    referenceMode (fun p : PolarPoint => f p.1 * Radial.cosineMode j p.2) k r =
      f r * (if j = k then 1 else 0) := by
  unfold referenceMode
  simp only [mul_assoc]
  rw [radialAngularMean_const_mul, radialAngularMean_cosineMode_product j k hj hk]

/-- The normalized true border gives exactly the required reference row. -/
theorem referenceRow_phi_cosineMode {D : ReferenceData} (hborder : RadialTrueBorder D) :
    referenceRow D (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) = 1 := by
  have hmode (r : ℝ) :
      referenceMode (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) 2 r =
        D.phi r := by
    simpa using referenceMode_cosine_field D.phi 2 2 (by decide) (by decide) r
  unfold referenceRow
  simp_rw [hmode]
  exact hborder.2.2.2.1

/-- Once its actual weighted jets are known, the reference field is represented
by the height model with all the auxiliary state coordinates equal to zero. -/
private theorem n01a_exists_height_representation {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {H : SobolevModelData} (hH : IsSobolevModel D T γ H)
    {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) :
    ∃ u : H.Space, H.decode u = f :=
  hH.2.2.2.2.1 f hf

private def n01aReferenceStateOfHeight (S : PhysicalSpacesData)
    (u : (S.height (3 / 4 : ℝ)).Space) : AnnularState S :=
  ((u, 0), 0, 0, 0)

private theorem n01aReferenceStateOfHeight_field (S : PhysicalSpacesData)
    (u : (S.height (3 / 4 : ℝ)).Space) :
    stateU S (n01aReferenceStateOfHeight S u) = (S.height (3 / 4 : ℝ)).decode u := by
  funext p
  simp only [stateU, heightPairField, n01aReferenceStateOfHeight, zero_mul, add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem exists_referenceState_of_heightMember {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D)
    (hphi : HeightMember D T (3 / 4 : ℝ)
      (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2)) :
    ∃ x : AnnularState S,
      (∀ p, stateU S x p = D.phi p.1 * Radial.cosineMode 2 p.2) ∧
      x.1.2 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.2.2.2 = 0 ∧
      referenceRow D (stateU S x) = 1 := by
  have hrepr : ∃ u : (S.height (3 / 4 : ℝ)).Space,
      (S.height (3 / 4 : ℝ)).decode u =
        (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) :=
    n01a_exists_height_representation (H := S.height (3 / 4 : ℝ))
      (hS.1 (3 / 4 : ℝ)) hphi
  obtain ⟨u, hu⟩ := hrepr
  have hx : stateU S (n01aReferenceStateOfHeight S u) =
      (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) :=
    (n01aReferenceStateOfHeight_field S u).trans hu
  refine ⟨n01aReferenceStateOfHeight S u, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro p
    exact congrFun hx p
  · rw [hx]
    exact referenceRow_phi_cosineMode hborder

end ContinuousFlexibility.Statements
