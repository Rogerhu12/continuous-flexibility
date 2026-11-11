import ContinuousFlexibility.Analysis.N07bSourceBoundSummation
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedPointwise

/-!
# A uniform actual source lift from a geometric coefficient estimate

The geometric estimate below is a separately named, source-independent
condition. This module does not claim that frozen `N04PartA` or `N04Properties`
provides it. Under that condition, the actual finite source expansion,
material energy, atlas summation, and prescribed weak-jet model prove the
uniform source-lift bound needed in the Banach bridge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The exact geometric condition used by the analytic source estimate.
The constants are chosen before the state, piece, path, and source. This
condition is not a field of the frozen canonical geometry statement. -/
def N07bSourceCoefficientBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base : ℕ) (ε : ℝ) (b loss : ℕ) : Prop :=
  ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K m →
        ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
          n07bSourceGeometricWeight T K z m x *
            n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
              B * T.E0 x.1 ^ A *
                (1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|) ^ 2

/-- For positive actual heights, the coefficient multiplier is precisely
the physical Jacobian weight with height ratio exponent `3/2`. -/
theorem n07bSourceGeometricWeight_eq
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint)
    (hx : 0 < T.H x.1) (hm : 0 < T.H (T.sample (K.cell m))) :
    n07bSourceGeometricWeight T K z m x =
      T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
  have hfactor : n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m =
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) := by
    simp only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero, one_mul]
  have hp : (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 =
      (T.H x.1 / T.H (T.sample (K.cell m))) ^ (3 / 2 : ℝ) := by
    rw [← Real.div_rpow hx.le hm.le, ← Real.rpow_natCast,
      ← Real.rpow_mul (div_nonneg hx.le hm.le)]
    norm_num
  calc
    _ = T.ell x.1 * |planeJacobian (K.chart z m) x| *
        (T.H x.1 ^ (3 / 4 : ℝ) / T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) ^ 2 := by
      change T.ell x.1 * ((n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
        |planeJacobian (K.chart z m) x| * (T.H x.1 ^ (3 / 4 : ℝ)) ^ 2) = _
      rw [hfactor]
      simp only [div_eq_mul_inv, mul_pow]
      ring
    _ = _ := by rw [hp]

/-- Scalar square-root arithmetic is checked before a concrete weak-jet
space is supplied, so the norm comparison does not unfold that space. -/
private theorem norm_le_sqrt_mul_of_square_bound
    {E : Type*} [SeminormedAddCommGroup E] {u : E} {A Q p q : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hp : 0 ≤ p) (hpq : p ≤ q)
    (h : ‖u‖ ^ 2 ≤ A * Q ^ 2 * p ^ 2) :
    ‖u‖ ≤ Real.sqrt A * Q * q := by
  have hq : 0 ≤ q := hp.trans hpq
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hQ) hq)).mp
  calc
    ‖u‖ ^ 2 ≤ A * Q ^ 2 * p ^ 2 := h
    _ ≤ A * Q ^ 2 * q ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpq 2) (mul_nonneg hA (sq_nonneg _))
    _ = (Real.sqrt A * Q * q) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA]

/-- The geometric coefficient estimate implies the actual uniform source
bound with source order `b+1` and final common index `b+loss+1`.
Only the explicitly displayed geometric hypothesis remains conditional. -/
theorem n07b_sourceLift_uniform_bound_of_coefficients
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (b loss : ℕ)
    (hgeom : N07bSourceCoefficientBound T S C K base ε b loss) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ≤ C₀ * (1 + stateGrading S (b + loss + 1) (z.1 - C.referenceState) + |z.2|) *
            S.sourceGrading (b + loss + 1) f ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  obtain ⟨B, A, hB, _, hcoeff⟩ := hgeom
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := hdata
  obtain ⟨CA, hCA, hEA⟩ := hE A
  let K₀ : ℝ := B * CA * n07bSourcePathConstant b
  have hK₀ : 0 ≤ K₀ :=
    mul_nonneg (mul_nonneg hB hCA.le) (n07bSourcePathConstant_nonneg b)
  let C₀ : ℝ := Real.sqrt K₀ + 1
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; linarith [Real.sqrt_nonneg K₀]
  refine ⟨C₀, hC₀, ?_⟩
  intro z hz hs f
  let Q : ℝ := 1 + stateGrading S (b + loss) (z.1 - C.referenceState) + |z.2|
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  let A₀ : ℝ := B * CA * Q ^ 2
  have hA₀ : 0 ≤ A₀ := mul_nonneg (mul_nonneg hB hCA.le) (sq_nonneg _)
  have hMbound : ∀ m x, x ∈ physicalPieceOpen S K m →
      ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
        n07bSourceGeometricWeight T K z m x *
          n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
            A₀ * T.M x.1 ^ 2 := by
    intro m x hx j i
    have hxcore : x.1 ∈ Ioo D.a D.b := (hK.2.2.2.1 m).2.2 hx.1
    have hM : 1 ≤ T.M x.1 := (hT.2.1 x.1 hxcore).2.2.2
    have hMM : T.M x.1 ≤ T.M x.1 ^ 2 := by nlinarith
    have hEM : T.E0 x.1 ^ A ≤ CA * T.M x.1 ^ 2 :=
      (hEA x.1 hxcore).trans (mul_le_mul_of_nonneg_left hMM hCA.le)
    calc
      _ ≤ B * T.E0 x.1 ^ A * Q ^ 2 := hcoeff z hz hs m x hx j i
      _ ≤ B * (CA * T.M x.1 ^ 2) * Q ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEM hB) (sq_nonneg _)
      _ = A₀ * T.M x.1 ^ 2 := by dsimp only [A₀]; ring
  obtain ⟨F, hF, hforget⟩ := n07b_exists_sourceLift_of_M_bound hD hT hS hV hK hz hs f b hA₀ hMbound
  have hsource : physicalNorm T (3 / 4 : ℝ) (b + 1)
      ((S.height (3 / 4 : ℝ)).decode f.val) ≤ S.sourceGrading (b + loss + 1) f := by
    change physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ≤
      (S.height (3 / 4 : ℝ)).grading (b + loss + 1) f.val
    apply (physicalNorm_decode_le_grading (hS.1 (3 / 4 : ℝ)) f.val (b + 1)).trans
    exact gradedSeminorm_monotone _ _ (by omega) f.val
  have hp : 0 ≤ S.sourceGrading (b + loss + 1) f := apply_nonneg _ _
  have hFsq : ‖F‖ ^ 2 ≤ K₀ * Q ^ 2 *
      physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2 := by
    apply hF.trans_eq
    dsimp only [A₀, K₀]
    ring
  have hn : ‖F‖ ≤ Real.sqrt K₀ * Q * S.sourceGrading (b + loss + 1) f :=
    norm_le_sqrt_mul_of_square_bound (E := V.level (3 / 4 : ℝ) 0 b)
      hK₀ hQ (Real.sqrt_nonneg _) hsource hFsq
  have hQle : Q ≤ 1 + stateGrading S (b + loss + 1) (z.1 - C.referenceState) + |z.2| :=
    add_le_add (add_le_add le_rfl
      (solve_stateGrading_monotone S (by omega) (z.1 - C.referenceState))) le_rfl
  have hsqrt : Real.sqrt K₀ ≤ C₀ := by dsimp only [C₀]; linarith
  exact ⟨F, hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hsqrt hQle hQ hC₀.le) hp), hforget⟩

end ContinuousFlexibility.Analysis
