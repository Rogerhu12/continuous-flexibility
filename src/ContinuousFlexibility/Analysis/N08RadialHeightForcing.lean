module

public import ContinuousFlexibility.Analysis.N08FlowHeightVariation
public import ContinuousFlexibility.Scalar.WeightedProductTower

/-!
# The positive radial forcing detected by N01's mixed flow jet

A height direction only has to be radial on the negative component under
consideration. Its normalization can be corrected elsewhere. Equality of
actual germs identifies the mixed jet with the optical forcing integral,
and N01 bounds that same jet in its original cell and fixed input grades.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff Interval BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n08RadialSpeedVariation_congr_germ {w : ℝ → ℝ}
    {u v : PolarPoint → ℝ} {p : PolarPoint} (huv : u =ᶠ[𝓝 p] v) :
    n08RadialSpeedVariation w u p = n08RadialSpeedVariation w v p := by
  have hang : heightAngular u =ᶠ[𝓝 p] heightAngular v := by
    filter_upwards [huv.fderiv (𝕜 := ℝ)] with z hz
    simp only [heightAngular, angularPartial, hz]
  have hrad : heightRadial u p = heightRadial v p := by
    rw [heightRadial, heightRadial, radialPartial, radialPartial, huv.fderiv_eq (𝕜 := ℝ)]
  have hpr : radialPartial (heightAngular u) p = radialPartial (heightAngular v) p := by
    rw [radialPartial, radialPartial, hang.fderiv_eq (𝕜 := ℝ)]
  have hpt : angularPartial (heightAngular u) p = angularPartial (heightAngular v) p := by
    rw [angularPartial, angularPartial, hang.fderiv_eq (𝕜 := ℝ)]
  simp only [n08RadialSpeedVariation, hrad, hpr, hpt]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Radiality is local to this negative component. The two derivatives
and the optical speed are all those of the actual fields. -/
theorem n08_minusFlow_parameter_radialHeight_jet
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (η : HeightPair S) (m : ℕ) {h g : ℝ → ℝ}
    (hhg : ∀ s, HasDerivAt h (g s) s)
    (hη : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ θ,
      heightPairField S η (s, θ) = h s)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ))) :
    J.D 2 (C.referenceState, 0)
      (Fin.cons ((η, (0, (0, 0))), (0 : ℝ))
        (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)) =
      ∫ s in C.left m..r, opticalSpeed D.w s * (1 + D.w s ^ 2) / D.w s * g s := by
  rw [n08_minusFlow_parameter_height_jet hT hS hN η m θ hr J]
  apply intervalIntegral.integral_congr_Ioo_of_le hr.1.le
  intro s hs
  have hi : s ∈ Ioo (C.left m) (C.right m) := ⟨hs.1, hs.2.trans hr.2⟩
  let p : PolarPoint := (s, C.minusFlow (C.referenceState, 0) m s θ)
  have hgerm : heightPairField S η =ᶠ[𝓝 p] Radial.radialHeightField h := by
    have hnear := (continuous_fst.tendsto p).eventually (isOpen_Ioo.mem_nhds hi)
    filter_upwards [hnear] with q hq
    exact hη q.1 hq q.2
  exact (n08RadialSpeedVariation_congr_germ hgerm).trans
    (n08RadialSpeedVariation_radial D.w hhg p)

private theorem n08_oneHigh_mixed_height_parameter
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight (pairGrading p realGrading) base high (0 : E × ℝ)
      (Fin.cons (v, (0 : ℝ)) (Fin.cons ((0 : E), (1 : ℝ)) Fin.elim0)) =
      2 * p base v + p high v := by
  have hvector : Fin.cons (v, (0 : ℝ)) (Fin.cons ((0 : E), (1 : ℝ)) Fin.elim0) =
      ![(v, (0 : ℝ)), ((0 : E), (1 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [hvector]
  rw [oneHighVariationWeight, oneHigh_fin_two]
  simp [Fin.prod_univ_two, pairGrading, realGrading] <;> ring

private theorem n08_first_injection_grading
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ) (v : E) :
    pairGrading p q s (v, (0 : F)) = p s v := by
  change p s v + q s 0 = p s v
  rw [map_zero, add_zero]

theorem n08_heightDirection_grading (S : PhysicalSpacesData) (s : ℕ) (η : HeightPair S) :
    stateGrading S s (η, (0, (0, 0))) = heightPairGrading S s η := by
  simpa only [stateGrading, Prod.zero_eq_mk] using
    n08_first_injection_grading (heightPairGrading S)
      (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading)) s η

private theorem n08_center_seminorm_lt {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) : p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

/-- The second parameter order chooses its additional loss and constant
before the component, height direction and target radius. The material
sample is exactly `C.cell m`, as in N01. -/
theorem n08_radialHeight_forcing_integral_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m (η : HeightPair S) (h g : ℝ → ℝ),
      (∀ s, HasDerivAt h (g s) s) →
      (∀ s ∈ Ioo (C.left m) (C.right m), ∀ θ, heightPairField S η (s, θ) = h s) →
      ∀ r ∈ Ioo (C.left m) (C.right m),
        |∫ s in C.left m..r, opticalSpeed D.w s * (1 + D.w s ^ 2) / D.w s * g s| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (2 * heightPairGrading S base η + heightPairGrading S (loss + parameterLoss) η) := by
  have hdata := hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩ := hdata
  obtain ⟨parameterLoss, hparameter⟩ := hflow 2
  obtain ⟨B, hB, hBj⟩ := hparameter 0
  refine ⟨parameterLoss, B, hB, ?_⟩
  intro m η h g hhg hη r hr
  obtain ⟨J, hJ⟩ := hBj m 0 0 (r, (0 : ℝ)) (by simp) hr
  have hzero : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    ⟨n08_center_seminorm_lt (stateGrading S base) C.referenceState hN.2.1,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1⟩
  have hvalue := n08_minusFlow_parameter_radialHeight_jet hT hS hN η m hhg hη 0 hr J
  have hbound := hJ (C.referenceState, 0) hzero
    (Fin.cons ((η, (0, (0, 0))), (0 : ℝ))
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0))
  simpa only [pow_zero, one_mul, Nat.zero_add, hvalue, sub_self,
    n08_oneHigh_mixed_height_parameter, n08_heightDirection_grading] using hbound

end ContinuousFlexibility.Statements
