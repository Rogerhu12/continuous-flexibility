import ContinuousFlexibility.Analysis.ReturnCorrectionAlgebra
import ContinuousFlexibility.Analysis.ReturnChartDifferentiation

/-!
# The actual cutoff-corrected characteristic flow

The initial-point correction and the new flow are defined directly from
the nonlinear geometry data. N01 supplies the initial identity, both
exact charted returns, and strict monotonicity of the initial-point
correction. The velocity uses the actual inverses of the two injective
maps involved, chosen by `Function.invFun`.

The interior differential statement requires joint differentiability
of the given ordinary flow. This regularity premise is stated explicitly;
it is not silently inferred from pointwise derivatives of a totalized
derivative operator. The scalar smoothness and continuity composition
lemmas below use the same actual flow formula.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The actual map `K = f⁻¹ ∘ hR⁻¹ ∘ R₋T ∘ hL`. -/
def returnCorrectionInitialMap (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  C.minusReturnInverse z m
    (C.rightChartInverse z m (stateLeftChart S z.1 m θ - C.travel m))

theorem returnCorrectionInitialMap_apply (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) :
    returnCorrectionInitialMap S C z m θ = C.minusReturnInverse z m
      (C.rightChartInverse z m (stateLeftChart S z.1 m θ - C.travel m)) := rfl

/-- The corrected flow `Φ̂ᵣ = Φᵣ ∘ (id + χ(r)(K-id))`. -/
def returnCorrectedMinusFlow (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ) : ℝ :=
  C.minusFlow z m r (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ)

theorem returnCorrectedMinusFlow_apply (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ) :
    returnCorrectedMinusFlow S C χ z m r θ =
      C.minusFlow z m r (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ) := rfl

/-- The scalar velocity in the manuscript, with actual inverse maps
of the old flow slice and of its initial-point interpolation. -/
def returnCorrectedMinusSpeed (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) : ℝ :=
  let α : ℝ := Function.invFun (C.minusFlow z m p.1) p.2
  let θ : ℝ := Function.invFun
    (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) α
  minusCharacteristicSpeed (originalCoefficients D S C z) p +
    deriv (C.minusFlow z m p.1) α * deriv (χ m) p.1 *
      (returnCorrectionInitialMap S C z m θ - θ)

theorem N01Properties.returnCorrectionInitialMap_strictMono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    StrictMono (returnCorrectionInitialMap S C z m) := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  rcases hN01 with ⟨_, _, _, hcontrol, _, _, hflow, hleft, _, _⟩
  have hf : StrictMono (C.minusFlow z m (C.right m)) := by
    apply strictMono_of_deriv_pos
    intro θ
    exact ((hflow z hz m θ).2.2.2 (C.right m)
      ⟨(hcontrol.1 m).2.1.le, le_rfl⟩).1
  have hh : StrictMono (rightChartCandidate S C z m) :=
    strictMono_of_deriv_pos fun θ => (hI θ).2.2.2.2
  have hfi : StrictMono (C.minusReturnInverse z m) := by
    intro x y hxy
    apply hf.lt_iff_lt.mp
    simpa only [(hI x).1, (hI y).1] using hxy
  have hhi : StrictMono (C.rightChartInverse z m) := by
    intro x y hxy
    apply hh.lt_iff_lt.mp
    simpa only [(hI x).2.2.1, (hI y).2.2.1] using hxy
  have hL : StrictMono (stateLeftChart S z.1 m) := by
    apply strictMono_of_deriv_pos
    intro θ
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (hleft z hz hsector m θ).1
  intro x y hxy
  rw [returnCorrectionInitialMap_apply, returnCorrectionInitialMap_apply]
  exact hfi (hhi (sub_lt_sub_right (hL hxy) _))

/-- The initial value and both exact return identities are consequences
of N01 and the two endpoint values of the cutoff. -/
theorem N01Properties.returnCorrectedMinusFlow_endpoints
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (hχleft : χ m (C.left m) = 0) (hχright : χ m (C.right m) = 1) (θ : ℝ) :
    returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ ∧
    rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m (-returnCorrectedMinusFlow S C χ z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  rcases hN01 with ⟨_, _, _, _, _, _, hflow, hleft, _, _⟩
  have hinitial : returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ := by
    rw [returnCorrectedMinusFlow_apply, hχleft, returnInterpolation_zero]
    exact (hflow z hz m θ).1
  have hminus (t : ℝ) :
      rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) t) =
        stateLeftChart S z.1 m t - C.travel m := by
    rw [returnCorrectedMinusFlow_apply, hχright, returnInterpolation_one,
      returnCorrectionInitialMap_apply,
      (hI (C.rightChartInverse z m (stateLeftChart S z.1 m t - C.travel m))).1,
      (hI (stateLeftChart S z.1 m t - C.travel m)).2.2.1]
  refine ⟨hinitial, hminus θ, ?_⟩
  exact returnCorrection_reflected_return
    (returnCorrectedMinusFlow S C χ z m (C.right m))
    (stateLeftChart S z.1 m) (rightChartCandidate S C z m) (C.travel m)
    (fun t => (hleft z hz hsector m t).2.2.2)
    (rightChartCandidate_odd S C z m) hminus θ

/-- The actual initial-point map is the conjugated residual correction. -/
theorem N01Properties.returnCorrectionInitialMap_conjugation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    returnCorrectionInitialMap S C z m θ =
      C.minusReturnInverse z m (C.rightChartInverse z m
        (rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) +
          returnResidualField S C z m
            (rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)))) := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  have he := returnResidualField_return_identity S C z m
    (fun t => (hI t).2.1) (fun t => (hI t).2.2.2.1) θ
  rw [returnCorrectionInitialMap_apply, he]

/-! ## Recovering the two-variable differential from the ordinary ODE -/

theorem returnFlow_linearMap_coordinates (A : (ℝ × ℝ) →L[ℝ] ℝ) :
    A = A (1, 0) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      A (0, 1) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  have hxy : (x, y) = x • (1, 0) + y • (0, 1) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  calc A (x, y) = A (x • (1, 0) + y • (0, 1)) := congrArg A hxy
    _ = x * A (1, 0) + y * A (0, 1) := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
    _ = _ := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      ring

/-- Joint differentiability and the ordinary radial equation determine
the full differential needed by the corrected-flow chain rule. -/
theorem returnFlow_hasFDerivAt_of_radial
    {F : ℝ × ℝ → ℝ} {r θ c : ℝ} (hF : DifferentiableAt ℝ F (r, θ))
    (hFr : HasDerivAt (fun t => F (t, θ)) c r) :
    HasFDerivAt F
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun t => F (r, t)) θ • ContinuousLinearMap.snd ℝ ℝ ℝ) (r, θ) := by
  let A : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ F (r, θ)
  have hr : HasDerivAt (fun t => F (t, θ)) (A (1, 0)) r := by
    simpa only [Function.comp_def, id_eq] using
      hF.hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have ht : HasDerivAt (fun t => F (r, t)) (A (0, 1)) θ := by
    simpa only [Function.comp_def, id_eq] using
      hF.hasFDerivAt.comp_hasDerivAt θ
        ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  have he := returnFlow_linearMap_coordinates A
  rw [hr.unique hFr, ← ht.deriv] at he
  rw [← he]
  exact hF.hasFDerivAt

theorem returnCorrectedMinusSpeed_on_flow
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (hΦ : Function.Injective (C.minusFlow z m r))
    (hJ : Function.Injective (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m))) :
    returnCorrectedMinusSpeed D S C χ z m (r, returnCorrectedMinusFlow S C χ z m r θ) =
      minusCharacteristicSpeed (originalCoefficients D S C z)
        (r, returnCorrectedMinusFlow S C χ z m r θ) +
      deriv (C.minusFlow z m r)
        (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ) * deriv (χ m) r *
          (returnCorrectionInitialMap S C z m θ - θ) := by
  simp only [returnCorrectedMinusSpeed, returnCorrectedMinusFlow_apply,
    Function.leftInverse_invFun hΦ, Function.leftInverse_invFun hJ]

/-- The actual corrected flow solves the explicitly computed corrected
velocity equation. Only joint differentiability of the old flow and
differentiability/range of the cutoff supplement N01 here. -/
theorem N01Properties.returnCorrectedMinusFlow_hasDerivAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (r θ : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m))
    (hχ : DifferentiableAt ℝ (χ m) r) (hχrange : χ m r ∈ Icc (0 : ℝ) 1)
    (hΦ : DifferentiableAt ℝ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (r, returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ)) :
    HasDerivAt (fun s => returnCorrectedMinusFlow S C χ z m s θ)
      (returnCorrectedMinusSpeed D S C χ z m (r, returnCorrectedMinusFlow S C χ z m r θ)) r := by
  have hK := hN01.returnCorrectionInitialMap_strictMono hz hsector m
  obtain ⟨_, _, _, _, _, _, hflow, _⟩ := hN01
  have hΦmono : StrictMono (C.minusFlow z m r) := by
    apply strictMono_of_deriv_pos
    intro t
    exact ((hflow z hz m t).2.2.2 r ⟨hr.1.le, hr.2.le⟩).1
  have hJmono := returnInterpolation_strictMono hχrange.1 hχrange.2 hK
  rw [returnCorrectedMinusSpeed_on_flow D S C χ z m r θ hΦmono.injective hJmono.injective]
  have hrad := (hflow z hz m
    (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ)).2.2.1 r hr
  have hFderiv := returnFlow_hasFDerivAt_of_radial hΦ hrad
  simpa only [returnCorrectedMinusFlow_apply] using
    returnCorrection_flow_hasDerivAt (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (χ m) (returnCorrectionInitialMap S C z m) r θ (deriv (χ m) r)
      (minusCharacteristicSpeed (originalCoefficients D S C z)
        (r, returnCorrectedMinusFlow S C χ z m r θ))
      (deriv (C.minusFlow z m r)
        (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ))
      hχ.hasDerivAt hFderiv

/-! ## Interior smoothness and continuity up to both endpoints -/

/-- For a fixed material point, smoothness of the corrected flow in
the radius follows from the joint smoothness of the actual old flow.
No smoothness of a newly chosen inverse is needed in this composition. -/
theorem returnCorrectedMinusFlow_contDiffOn
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ)
    (hχ : ContDiffOn ℝ ∞ (χ m) (Ioo (C.left m) (C.right m)))
    (hΦ : ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (C.left m) (C.right m) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun r => returnCorrectedMinusFlow S C χ z m r θ)
      (Ioo (C.left m) (C.right m)) := by
  have hJ : ContDiffOn ℝ ∞
      (fun r => returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ)
      (Ioo (C.left m) (C.right m)) := by
    simpa only [returnInterpolation_apply, Pi.add_apply, Pi.mul_apply] using
      (contDiffOn_const.add (hχ.mul
        (contDiffOn_const : ContDiffOn ℝ ∞
          (fun _ : ℝ => returnCorrectionInitialMap S C z m θ - θ)
          (Ioo (C.left m) (C.right m)))))
  have hpath : ContDiffOn ℝ ∞
      (fun r => (r, returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m) θ))
      (Ioo (C.left m) (C.right m)) := contDiffOn_id.prodMk hJ
  simpa only [Function.comp_def, returnCorrectedMinusFlow_apply] using
    hΦ.comp hpath (fun r hr => ⟨hr, mem_univ _⟩)

/-- The cutoff is constant near each endpoint, so the corrected curve
agrees there with one fixed old-flow curve. Thus the endpoint
continuity already in N01 is sufficient, even though the ordinary
characteristic velocity need not be smooth at a turning point. -/
theorem N01Properties.returnCorrectedMinusFlow_continuousOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) (θ : ℝ)
    (hχ : ContDiff ℝ ∞ (χ m))
    (hχleft : χ m =ᶠ[𝓝 (C.left m)] fun _ => 0)
    (hχright : χ m =ᶠ[𝓝 (C.right m)] fun _ => 1)
    (hΦ : ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (C.left m) (C.right m) ×ˢ univ)) :
    ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
      (Icc (C.left m) (C.right m)) := by
  have hmiddle := returnCorrectedMinusFlow_contDiffOn S C χ z m θ hχ.contDiffOn hΦ
  obtain ⟨_, _, _, _, _, _, hflow, _⟩ := hN01
  intro r hr
  by_cases hl : r = C.left m
  · subst r
    have heq : (fun s => returnCorrectedMinusFlow S C χ z m s θ) =ᶠ[𝓝 (C.left m)]
        fun s => C.minusFlow z m s θ := by
      filter_upwards [hχleft] with s hs
      rw [returnCorrectedMinusFlow_apply, hs, returnInterpolation_zero]
    exact ((hflow z hz m θ).2.1 (C.left m) hr).congr_of_eventuallyEq_of_mem
      (heq.filter_mono nhdsWithin_le_nhds) hr
  by_cases hr' : r = C.right m
  · subst r
    have heq : (fun s => returnCorrectedMinusFlow S C χ z m s θ) =ᶠ[𝓝 (C.right m)]
        fun s => C.minusFlow z m s (returnCorrectionInitialMap S C z m θ) := by
      filter_upwards [hχright] with s hs
      rw [returnCorrectedMinusFlow_apply, hs, returnInterpolation_one]
    exact ((hflow z hz m (returnCorrectionInitialMap S C z m θ)).2.1
      (C.right m) hr).congr_of_eventuallyEq_of_mem
        (heq.filter_mono nhdsWithin_le_nhds) hr
  have hleft : C.left m < r := lt_of_le_of_ne hr.1 (Ne.symm hl)
  have hright : r < C.right m := lt_of_le_of_ne hr.2 hr'
  exact (hmiddle.contDiffAt (Ioo_mem_nhds hleft hright)).continuousAt.continuousWithinAt

/-- Assemble all the flow assertions from the same actual corrected
curve. The only remaining scalar analytic input, in addition to the
cutoff, is joint interior smoothness of the old flow. -/
theorem N01Properties.returnCorrectedMinusFlow_properties
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) (m : ℕ)
    (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (hχleft : χ m =ᶠ[𝓝 (C.left m)] fun _ => 0)
    (hχright : χ m =ᶠ[𝓝 (C.right m)] fun _ => 1)
    (hΦ : ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (C.left m) (C.right m) ×ˢ univ)) (θ : ℝ) :
    returnCorrectedMinusFlow S C χ z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => returnCorrectedMinusFlow S C χ z m r θ)
      (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m),
      HasDerivAt (fun s => returnCorrectedMinusFlow S C χ z m s θ)
        (returnCorrectedMinusSpeed D S C χ z m (r, returnCorrectedMinusFlow S C χ z m r θ)) r) ∧
    rightChartCandidate S C z m (returnCorrectedMinusFlow S C χ z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m (-returnCorrectedMinusFlow S C χ z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m := by
  have hends := hN01.returnCorrectedMinusFlow_endpoints χ hz hsector m
    hχleft.eq_of_nhds hχright.eq_of_nhds θ
  refine ⟨hends.1,
    hN01.returnCorrectedMinusFlow_continuousOn χ hz m θ hχ hχleft hχright hΦ,
    ?_, hends.2.1, hends.2.2⟩
  intro r hr
  apply hN01.returnCorrectedMinusFlow_hasDerivAt χ hz hsector m r θ hr
    (hχ.differentiable (by simp) r) (hχrange r ⟨hr.1.le, hr.2.le⟩)
  exact (hΦ.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)

end ContinuousFlexibility.Statements
