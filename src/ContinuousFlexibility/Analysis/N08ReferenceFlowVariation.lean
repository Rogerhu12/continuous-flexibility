import ContinuousFlexibility.Analysis.N08FlowParameterBounds
import ContinuousFlexibility.Analysis.N08FlowSpeedBounds

/-!
# The actual parameter variation of the ordinary flow at zero

N01 supplies a uniform first-parameter bound on the given flow. The
factored speed is uniformly Lipschitz on a compact box containing those
trajectories. Differentiating the original integral equation therefore
identifies its parameter derivative with the explicit radial-speed
variation, without assuming a variational differential equation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped NNReal Topology ContDiff Interval

set_option backward.isDefEq.respectTransparency false

theorem n08RadialSpeedVariation_continuousOn
    {w : ℝ → ℝ} {u : PolarPoint → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (ha : 0 < a)
    (hpos : ∀ r ∈ Icc a b, 0 < w r) :
    ContinuousOn (n08RadialSpeedVariation w u) (Icc a b ×ˢ (univ : Set ℝ)) := by
  have hrad : ContinuousOn (heightRadial u) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p _ => (contDiffAt_heightRadial hu.contDiffAt (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hang (p : PolarPoint) (hp : p ∈ Icc a b ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ (heightAngular u) p :=
    contDiffAt_heightAngular hu.contDiffAt (m := ∞) (by simp) (ha.trans_le hp.1.1).ne'
  have hpr : ContinuousOn (radialPartial (heightAngular u)) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (contDiffAt_radialPartial (hang p hp) (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hpt : ContinuousOn (angularPartial (heightAngular u)) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (contDiffAt_angularPartial (hang p hp) (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hwr : ContinuousOn (fun p : PolarPoint => w p.1) (Icc a b ×ˢ (univ : Set ℝ)) :=
    (hw.continuous.comp continuous_fst).continuousOn
  have hfactor : ContinuousOn (fun p : PolarPoint => (1 + w p.1 ^ 2) / w p.1)
      (Icc a b ×ˢ (univ : Set ℝ)) :=
    (continuousOn_const.add (hwr.pow 2)).div hwr (fun p hp => (hpos p.1 hp.1).ne')
  have hwd : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hv : ContinuousOn (opticalSpeed w) (Icc a b) :=
    (hwd.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => mul_ne_zero (ha.trans_le hr.1).ne' (hpos r hr).ne')).sqrt
  exact hfactor.mul (hpr.neg.add
    ((hv.comp continuous_fst.continuousOn (fun _ hp => hp.1)).mul (hrad.add hpt)))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The derivative is of N01's specified flow. Only the target radius is
interior; the integral starts at its actual continuous left endpoint. -/
theorem n08_minusFlow_parameter_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x) (m : ℕ) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m r θ)
      (∫ s in C.left m..r,
        n08RadialSpeedVariation (stateProfile D S C x) (stateU S x)
          (s, C.minusFlow (x, 0) m s θ)) 0 := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hdata := hN
  obtain ⟨_, _, _, hcontrol, _, _, hflow, _, _, hadmiss, _, _, hjet⟩ := hdata
  have hcell := hcontrol.1 m
  have hcore (s : ℝ) (hs' : s ∈ Icc (C.left m) r) : s ∈ radialCore D :=
    ⟨hcell.1.trans_le hs'.1, hs'.2.trans_lt (hr.2.trans hcell.2.2)⟩
  have ha : 0 < C.left m := hg.1.trans hcell.1
  let O : Set ℝ := Icc (-(ε / 2)) (ε / 2)
  have hO : O ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith [hN.2.1]) (half_pos hN.2.1)
  have hzero : (0 : ℝ) ∈ O := mem_of_mem_nhds hO
  have hmem (q : ℝ) (hq : q ∈ O) : (x, q) ∈ stateNeighborhood S C base ε :=
    ⟨hx.1, (abs_le.mpr hq).trans_lt (by linarith [hN.2.1])⟩
  let f : ℝ → ℝ → ℝ := fun q s => C.minusFlow (x, q) m s θ
  have hcont (q : ℝ) (hq : q ∈ O) : ContinuousOn (f q) (Icc (C.left m) r) :=
    (hflow (x, q) (hmem q hq) m θ).2.1.mono (Icc_subset_Icc le_rfl hr.2.le)
  obtain ⟨KF, hKF⟩ := n08_minusFlow_parameter_lipschitz hN x hx m θ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont 0 hzero)
  let L : ℝ := M + (KF : ℝ) * (ε / 2)
  have hbox (q : ℝ) (hq : q ∈ O) (s : ℝ) (hs' : s ∈ Icc (C.left m) r) :
      f q s ∈ Icc (-L) L := by
    have hbase : |f 0 s| ≤ M := by simpa only [Real.norm_eq_abs] using hM s hs'
    have hdiff : |f q s - f 0 s| ≤ (KF : ℝ) * (ε / 2) := by
      by_cases he : s = C.left m
      · rw [he, show f q (C.left m) = θ from (hflow (x, q) (hmem q hq) m θ).1,
          show f 0 (C.left m) = θ from (hflow (x, 0) hx m θ).1, sub_self, abs_zero]
        exact mul_nonneg (NNReal.coe_nonneg _) (half_pos hN.2.1).le
      · have hi : s ∈ Ioo (C.left m) (C.right m) :=
          ⟨lt_of_le_of_ne hs'.1 (Ne.symm he), hs'.2.trans_lt hr.2⟩
        have hd := (hKF s hi).dist_le_mul q hq 0 hzero
        have hd' : |f q s - f 0 s| ≤ (KF : ℝ) * |q| := by
          simpa only [Real.dist_eq, sub_zero] using hd
        exact hd'.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hq) (NNReal.coe_nonneg _))
    apply abs_le.mp
    calc
      |f q s| = |(f q s - f 0 s) + f 0 s| := by rw [sub_add_cancel]
      _ ≤ |f q s - f 0 s| + |f 0 s| := abs_add_le _ _
      _ ≤ (KF : ℝ) * (ε / 2) + M := add_le_add hdiff hbase
      _ = L := by dsimp only [L]; ring
  let w : ℝ → ℝ := stateProfile D S C x
  let Z : ℝ × PolarPoint → ℝ := fun z => stateHeight D S C (x, z.1) z.2
  have hw : ContDiff ℝ ∞ w := contDiff_stateProfile_of_n01 hS hT hN x
  have hZ : ContDiff ℝ ∞ Z :=
    ((n08_stateRadialHeight_contDiff hT hS hN x).comp contDiff_snd.fst).add
      (contDiff_fst.mul ((n08_stateU_contDiff hT hS x).comp contDiff_snd))
  have hpos (q : ℝ) (hq : q ∈ O) (s : ℝ) (hs' : s ∈ Icc (C.left m) r) (η : ℝ) :
      0 < polarDiscriminant w (fun p => Z (q, p)) (s, η) ∧
      0 < heightQ (profileEnergy w (s, η)) (heightRadial (fun p => Z (q, p)) (s, η))
        (angularPartial (heightAngular (fun p => Z (q, p))) (s, η)) := by
    obtain ⟨_, _, hQlo, _, hDlo, _⟩ :=
      hadmiss (x, q) (hmem q hq) hs (s, η) ⟨hcore s hs', mem_univ η⟩
    have hwp : 0 < w s := n08_stateProfile_pos hg x (hcore s hs')
    exact ⟨lt_of_lt_of_le (by norm_num) hDlo,
      (div_pos_iff_of_pos_right hwp).mp (lt_of_lt_of_le (by norm_num) hQlo)⟩
  obtain ⟨hvc, KV, hKV⟩ := n08_parameterSpeed_box hw hZ ha
    (c := -(ε / 2)) (d := ε / 2) (e := -L) (f := L)
    (fun z hz => (hpos z.1 hz.1 z.2.1 hz.2.1 z.2.2).1)
    (fun z hz => (hpos z.1 hz.1 z.2.1 hz.2.1 z.2.2).2)
  let V : ℝ → ℝ → ℝ := fun q s => n08JacobiMinusSpeed w (fun p => Z (q, p)) (s, f q s)
  let W : ℝ → ℝ := fun s => n08RadialSpeedVariation w (stateU S x) (s, f 0 s)
  have hVint (q : ℝ) (hq : q ∈ O) : IntervalIntegrable (V q) volume (C.left m) r := by
    have hc := hvc.comp (continuousOn_const.prodMk (continuousOn_id.prodMk (hcont q hq)))
      (fun s hs' => ⟨hq, hs', hbox q hq s hs'⟩)
    exact hc.intervalIntegrable_of_Icc hr.1.le
  have hWc : ContinuousOn W (Icc (C.left m) r) :=
    (n08RadialSpeedVariation_continuousOn hw (n08_stateU_contDiff hT hS x) ha
      (fun s hs' => n08_stateProfile_pos hg x (hcore s hs'))).comp
        (continuousOn_id.prodMk (hcont 0 hzero)) (fun s hs' => ⟨hs', mem_univ _⟩)
  have hVL (s : ℝ) (hs' : s ∈ Ioc (C.left m) r) :
      LipschitzOnWith (KV * max 1 KF) (fun q => V q s) O := by
    have hi : s ∈ Ioo (C.left m) (C.right m) := ⟨hs'.1, hs'.2.trans_lt hr.2⟩
    have hp : LipschitzOnWith (max 1 KF) (fun q : ℝ => (q, f q s)) O :=
      LipschitzWith.id.lipschitzOnWith.prodMk (hKF s hi)
    simpa only [Function.comp_def] using (hKV s (Ioc_subset_Icc_self hs')).comp hp
      (fun q hq => ⟨hq, hbox q hq s (Ioc_subset_Icc_self hs')⟩)
  have hVd (s : ℝ) (hs' : s ∈ Ioc (C.left m) r) :
      HasDerivAt (fun q => V q s) (W s) 0 := by
    have hi : s ∈ Ioo (C.left m) (C.right m) := ⟨hs'.1, hs'.2.trans_lt hr.2⟩
    obtain ⟨B, _, hBj⟩ := hjet 1 0
    obtain ⟨J, _⟩ := hBj m 0 0 (s, θ) (by simp) hi
    have hc := n08_minusFlow_parameter_hasDerivAt J hx
    have hscc := Ioc_subset_Icc_self hs'
    have hp := hpos 0 hzero s hscc (f 0 s)
    apply n08_hasDerivAt_comp_of_zeroSlice_const
      (n08_parameterAngleSpeed_differentiableAt hw hZ (ha.trans_le hscc.1).ne' hp.1 hp.2) hc
    · intro η
      exact n08_minusCharacteristicSpeed_zero_parameter hg x hw s η (hcore s hscc)
    · exact n08_minusCharacteristicSpeed_parameter_zero hT hS hN x (s, f 0 s) (hcore s hscc)
  exact n08_hasDerivAt_integralTrajectory hr.1.le hO hcont
    (fun q hq => (hflow (x, q) (hmem q hq) m θ).1)
    (fun q hq s hs' => (hflow (x, q) (hmem q hq) m θ).2.2.1 s
      ⟨hs'.1, hs'.2.trans hr.2⟩)
    hVint (hWc.intervalIntegrable_of_Icc hr.1.le) hVL hVd

end ContinuousFlexibility.Statements
