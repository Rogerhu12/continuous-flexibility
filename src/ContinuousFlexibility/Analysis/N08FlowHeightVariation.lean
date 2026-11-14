module

public import ContinuousFlexibility.Analysis.N08ReferenceFlowVariation
public import ContinuousFlexibility.Analysis.N08Neighborhoods
public import ContinuousFlexibility.Analysis.N08StateLinearOperations

/-!
# The genuine mixed height and parameter jet of the ordinary flow

The zero-parameter flow is fixed along a height line. Its already proved
parameter derivative is therefore exactly affine in that line parameter.
Uniqueness of the real derivative identifies every supplied N01 second
jet, with the height direction first and the construction parameter last.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff Interval BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem heightLine_pair_eq {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (x : E × F) (η : E) (t : ℝ) : x + t • (η, (0 : F)) = (x.1 + t • η, x.2) := by
  rcases x with ⟨e, f⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

private theorem heightLine_eventually_mem
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set (E × ℝ)} (hU : IsOpen U) {x : E} {q : ℝ}
    (hx : (x, q) ∈ U) (v : E) :
    ∀ᶠ t : ℝ in 𝓝 0, (x + n08RealSMul t v, q) ∈ U := by
  have hc : Continuous (fun t : ℝ => (x + n08RealSMul t v, q)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ => (x + n08RealSMul t v, q))
      (𝓝 0) (𝓝 (x, q)) := by
    simpa only [n08RealSMul, zero_smul, add_zero] using hc.tendsto 0
  exact ht.eventually (hU.mem_nhds hx)

private theorem heightField_affine {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (χ : PolarPoint → ℝ) (x η : E × ℝ) (t : ℝ) :
    (fun p => L (x + t • η).1 p + (x + t • η).2 * χ p) =
      heightFamily (fun p => L x.1 p + x.2 * χ p) (fun p => L η.1 p + η.2 * χ p) t := by
  funext p
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, heightFamily]
  ring

private theorem fixedParameter_hasDerivAt {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : E × ℝ → ℝ} {x v : E} {q d : ℝ}
    (hd : HasProjectiveLineDerivAt F d (x, q) (v, (0 : ℝ))) :
    HasDerivAt (fun t : ℝ => F (x + t • v, q)) d 0 := by
  have h : HasDerivAt (fun t : ℝ => F ((x, q) + t • (v, (0 : ℝ)))) d 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hd
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using h

private theorem seminorm_center_lt {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) : p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08HeightLine (S : PhysicalSpacesData) (x : AnnularState S) (η : HeightPair S)
    (t : ℝ) : AnnularState S := x + n08StateSMul S t (η, (0, (0, 0)))

theorem n08HeightLine_eq (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    n08HeightLine S x η t = (x.1 + n08RealSMul t η, x.2) := by
  simpa only [n08HeightLine, n08StateSMul, n08RealSMul, Prod.zero_eq_mk] using
    heightLine_pair_eq x η t

theorem n08HeightLine_sector {x : AnnularState S} (hx : stateSector S x)
    (η : HeightPair S) (t : ℝ) : stateSector S (n08HeightLine S x η t) := by
  rw [n08HeightLine_eq]
  exact hx

theorem n08HeightLine_profile (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (n08HeightLine S x η t) = stateProfile D S C x := by
  rw [n08HeightLine_eq]
  rfl

theorem n08HeightLine_stateU (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateU S (n08HeightLine S x η t) = heightFamily (stateU S x) (heightPairField S η) t := by
  rw [n08HeightLine_eq]
  exact heightField_affine (S.height (3 / 4 : ℝ)).decode (fun p => S.chiLeft p.1) x.1 η t

/-- The reference-centered height line changes no zero-parameter ordinary
trajectory, including its left and right endpoint values. -/
theorem n08_minusFlow_reference_heightLine_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (η : HeightPair S) (t : ℝ)
    (ht : (n08HeightLine S C.referenceState η t, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (n08HeightLine S C.referenceState η t, 0) m r θ =
      C.minusFlow (C.referenceState, 0) m r θ := by
  rw [n08_minusFlow_zero_parameter_rotation hS hT hN _ ht m θ r hr,
    n08_minusFlow_reference_rotation hN m θ r hr, n08HeightLine_profile,
    n08_stateProfile_reference hN.2.2.1]

/-- The conclusion holds for any genuine tower of the actual normalized
flow family. No symmetry or independently chosen second jet is used. -/
theorem n08_minusFlow_parameter_height_jet
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (η : HeightPair S) (m : ℕ) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (ordinaryFlowFamily S C m 0 0 (r, θ))) :
    J.D 2 (C.referenceState, 0)
      (Fin.cons ((η, (0, (0, 0))), (0 : ℝ))
        (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)) =
      ∫ s in C.left m..r, n08RadialSpeedVariation D.w (heightPairField S η)
        (s, C.minusFlow (C.referenceState, 0) m s θ) := by
  let x : ℝ → AnnularState S := n08HeightLine S C.referenceState η
  let ϕ : ℝ → ℝ := fun s => C.minusFlow (C.referenceState, 0) m s θ
  let W0 : ℝ → ℝ := fun s => n08RadialSpeedVariation D.w (stateU S C.referenceState) (s, ϕ s)
  let Wη : ℝ → ℝ := fun s => n08RadialSpeedVariation D.w (heightPairField S η) (s, ϕ s)
  have href := hN.2.2.1
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hcell := hN.2.2.2.1.1 m
  have hzero : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    ⟨seminorm_center_lt (stateGrading S base) C.referenceState hN.2.1,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (x t, 0) ∈ stateNeighborhood S C base ε := by
    simpa only [x, n08HeightLine, n08StateSMul] using
      heightLine_eventually_mem (n08_isOpen_stateNeighborhood S C base ε)
        hzero (η, (0, (0, 0)))
  have hcore (s : ℝ) (hs : s ∈ Icc (C.left m) r) : s ∈ radialCore D :=
    ⟨hcell.1.trans_le hs.1, hs.2.trans_lt (hr.2.trans hcell.2.2)⟩
  have hflow := hN.2.2.2.2.2.2.1
  have hϕ : ContinuousOn ϕ (Icc (C.left m) r) :=
    (hflow (C.referenceState, 0) hzero m θ).2.1.mono (Icc_subset_Icc le_rfl hr.2.le)
  have hu0 := n08_stateU_contDiff hT hS C.referenceState
  have huη : ContDiff ℝ ∞ (heightPairField S η) :=
    n08_stateU_contDiff hT hS (η, (0, (0, 0)))
  have hint (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
      IntervalIntegrable (fun s => n08RadialSpeedVariation D.w u (s, ϕ s)) volume (C.left m) r :=
    ((n08RadialSpeedVariation_continuousOn hg.2.2.1.1 hu (hg.1.trans hcell.1)
      (fun s hs => hg.2.2.2.2.1 s (hcore s hs))).comp
        (continuousOn_id.prodMk hϕ) (fun s hs => ⟨hs, mem_univ _⟩)).intervalIntegrable_of_Icc hr.1.le
  have heq : (fun t : ℝ => J.D 1 (x t, 0)
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)) =ᶠ[𝓝 0]
      (fun t : ℝ => (∫ s in C.left m..r, W0 s) + t * ∫ s in C.left m..r, Wη s) := by
    filter_upwards [hnear] with t ht
    have hchosen := n08_minusFlow_parameter_hasDerivAt J ht
    have hactual := n08_minusFlow_parameter_zero hT hS hN (x t) ht
      (n08HeightLine_sector href.stateSector η t) m θ hr
    calc
      _ = ∫ s in C.left m..r,
          n08RadialSpeedVariation (stateProfile D S C (x t)) (stateU S (x t))
            (s, C.minusFlow (x t, 0) m s θ) := hchosen.unique hactual
      _ = ∫ s in C.left m..r, W0 s + t * Wη s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hscc : s ∈ Icc (C.left m) r := by simpa only [uIcc_of_le hr.1.le] using hs
        have hsfull : s ∈ Icc (C.left m) (C.right m) := ⟨hscc.1, hscc.2.trans hr.2.le⟩
        dsimp only [x]
        rw [n08_minusFlow_reference_heightLine_zero hT hS hN η t ht m θ s hsfull,
          n08HeightLine_profile, n08_stateProfile_reference href, n08HeightLine_stateU]
        exact n08RadialSpeedVariation_heightFamily D.w hu0 huη (hg.1.trans (hcore s hscc).1).ne' t
      _ = _ := by
        rw [intervalIntegral.integral_add (hint _ hu0) ((hint _ huη).const_mul t),
          intervalIntegral.integral_const_mul]
  have hformula : HasDerivAt
      (fun t : ℝ => (∫ s in C.left m..r, W0 s) + t * ∫ s in C.left m..r, Wη s)
      (∫ s in C.left m..r, Wη s) 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (∫ s in C.left m..r, Wη s)).const_add
        (∫ s in C.left m..r, W0 s)
  have hsecond : HasDerivAt (fun t : ℝ => J.D 1 (x t, 0)
      (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0))
      (J.D 2 (C.referenceState, 0)
        (Fin.cons ((η, (0, (0, 0))), (0 : ℝ))
          (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0))) 0 := by
    simpa only [x, n08HeightLine, n08StateSMul, n08RealSMul] using
      fixedParameter_hasDerivAt (J.derivative 1 (C.referenceState, 0) hzero
        (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0) ((η, (0, (0, 0))), (0 : ℝ)))
  exact hsecond.unique (hformula.congr_of_eventuallyEq heq)

end ContinuousFlexibility.Statements
