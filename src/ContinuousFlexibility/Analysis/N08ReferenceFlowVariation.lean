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

private theorem n08_halfParameter_mem
    (hε : 0 < ε) {x : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    {q : ℝ} (hq : q ∈ Icc (-(ε / 2)) (ε / 2)) :
    (x, q) ∈ stateNeighborhood S C base ε :=
  ⟨hx.1, (abs_le.mpr hq).trans_lt (by linarith only [hε])⟩

private theorem n08_stateHeight_parameter_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (fun z : ℝ × PolarPoint => stateHeight D S C (x, z.1) z.2) :=
  ((n08_stateRadialHeight_contDiff hT hS hN x).comp contDiff_snd.fst).add
    (contDiff_fst.mul ((n08_stateU_contDiff hT hS x).comp contDiff_snd))

/-- The parameter Lipschitz constant and compact angular box are obtained
before any differentiation of the speed along these trajectories. -/
private theorem n08_minusFlow_parameter_box
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ∃ K : ℝ≥0, ∃ L : ℝ,
      (∀ s ∈ Ioo (C.left m) (C.right m),
        LipschitzOnWith K (fun q : ℝ => C.minusFlow (x, q) m s θ)
          (Icc (-(ε / 2)) (ε / 2))) ∧
      ∀ q ∈ Icc (-(ε / 2)) (ε / 2), ∀ s ∈ Icc (C.left m) r,
        C.minusFlow (x, q) m s θ ∈ Icc (-L) L := by
  have hflow := hN.2.2.2.2.2.2.1
  let O : Set ℝ := Icc (-(ε / 2)) (ε / 2)
  have hzero : (0 : ℝ) ∈ O :=
    ⟨neg_nonpos.mpr (half_pos hN.2.1).le, (half_pos hN.2.1).le⟩
  let f : ℝ → ℝ → ℝ := fun q s => C.minusFlow (x, q) m s θ
  have hcont : ContinuousOn (f 0) (Icc (C.left m) r) :=
    (hflow (x, 0) hx m θ).2.1.mono (Icc_subset_Icc le_rfl hr.2.le)
  obtain ⟨K, hK⟩ := n08_minusFlow_parameter_lipschitz hN x hx m θ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let L : ℝ := M + (K : ℝ) * (ε / 2)
  refine ⟨K, L, hK, ?_⟩
  intro q hq s hs
  have hbase : |f 0 s| ≤ M := by simpa only [Real.norm_eq_abs] using hM s hs
  have hdiff : |f q s - f 0 s| ≤ (K : ℝ) * (ε / 2) := by
    by_cases he : s = C.left m
    · rw [he, show f q (C.left m) = θ from
        (hflow (x, q) (n08_halfParameter_mem hN.2.1 hx hq) m θ).1,
        show f 0 (C.left m) = θ from (hflow (x, 0) hx m θ).1, sub_self, abs_zero]
      exact mul_nonneg (NNReal.coe_nonneg _) (half_pos hN.2.1).le
    · have hi : s ∈ Ioo (C.left m) (C.right m) :=
        ⟨lt_of_le_of_ne hs.1 (Ne.symm he), hs.2.trans_lt hr.2⟩
      have hd' : |f q s - f 0 s| ≤ (K : ℝ) * |q| := by
        simpa only [Real.dist_eq, sub_zero] using (hK s hi).dist_le_mul q hq 0 hzero
      exact hd'.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hq) (NNReal.coe_nonneg _))
  apply abs_le.mp
  calc
    |f q s| = |(f q s - f 0 s) + f 0 s| := by rw [sub_add_cancel]
    _ ≤ |f q s - f 0 s| + |f 0 s| := abs_add_le _ _
    _ ≤ (K : ℝ) * (ε / 2) + M := add_le_add hdiff hbase
    _ = L := by dsimp only [L]; ring

/-- The moving-angle contribution vanishes in the zero-parameter radial
speed. Both derivatives here are those of the actual supplied functions. -/
private theorem n08_minusFlow_rhs_parameter_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x) (m : ℕ) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (fun q : ℝ => minusCharacteristicSpeed (originalCoefficients D S C (x, q))
      (r, C.minusFlow (x, q) m r θ))
      (n08RadialSpeedVariation (stateProfile D S C x) (stateU S x)
        (r, C.minusFlow (x, 0) m r θ)) 0 := by
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hdata := hN
  obtain ⟨_, _, _, hcontrol, _, _, _, _, _, hadmiss, _, _, hjet⟩ := hdata
  have hcell := hcontrol.1 m
  have hcore : r ∈ radialCore D := ⟨hcell.1.trans hr.1, hr.2.trans hcell.2.2⟩
  let w : ℝ → ℝ := stateProfile D S C x
  let Z : ℝ × PolarPoint → ℝ := fun z => stateHeight D S C (x, z.1) z.2
  let f : ℝ → ℝ := fun q => C.minusFlow (x, q) m r θ
  have hw : ContDiff ℝ ∞ w := contDiff_stateProfile_of_n01 hS hT hN x
  have hZ : ContDiff ℝ ∞ Z := n08_stateHeight_parameter_contDiff hT hS hN x
  obtain ⟨_, _, hQlo, _, hDlo, _⟩ :=
    hadmiss (x, 0) hx hs (r, f 0) ⟨hcore, mem_univ _⟩
  have hD : 0 < polarDiscriminant w (fun p => Z (0, p)) (r, f 0) :=
    lt_of_lt_of_le (by norm_num) hDlo
  have hQ : 0 < heightQ (profileEnergy w (r, f 0))
      (heightRadial (fun p => Z (0, p)) (r, f 0))
      (angularPartial (heightAngular (fun p => Z (0, p))) (r, f 0)) :=
    (div_pos_iff_of_pos_right (n08_stateProfile_pos hg x hcore)).mp
      (lt_of_lt_of_le (by norm_num) hQlo)
  obtain ⟨parameterLoss, hparameter⟩ := hjet 1
  obtain ⟨B, _, hBj⟩ := hparameter 0
  obtain ⟨J, _⟩ := hBj m 0 0 (r, θ) (by simp) hr
  have hc : HasDerivAt f
      (J.D 1 (x, 0) (Fin.cons ((0 : AnnularState S), (1 : ℝ)) Fin.elim0)) 0 :=
    n08_minusFlow_parameter_hasDerivAt J hx
  have hfd : DifferentiableAt ℝ
      (fun z : ℝ × ℝ => n08JacobiMinusSpeed w (fun p => Z (z.1, p)) (r, z.2)) (0, f 0) :=
    n08_parameterAngleSpeed_differentiableAt hw hZ (hg.1.trans hcore.1).ne' hD hQ
  simp only [n08_minusCharacteristicSpeed_eq_jacobi]
  apply n08_hasDerivAt_comp_of_zeroSlice_const
    (F := fun z : ℝ × ℝ => n08JacobiMinusSpeed w (fun p => Z (z.1, p)) (r, z.2))
    (c := f) (a := -opticalSpeed w r) hfd hc
  · intro φ
    simpa only [n08_minusCharacteristicSpeed_eq_jacobi] using
      n08_minusCharacteristicSpeed_zero_parameter hg x hw r φ hcore
  · simpa only [n08_minusCharacteristicSpeed_eq_jacobi] using
      n08_minusCharacteristicSpeed_parameter_zero hT hS hN x (r, f 0) hcore

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
  obtain ⟨_, _, _, hcontrol, _, _, hflow, _, _, hadmiss, _, _, _⟩ := hdata
  have hcell := hcontrol.1 m
  have hcore (s : ℝ) (hs' : s ∈ Icc (C.left m) r) : s ∈ radialCore D :=
    ⟨hcell.1.trans_le hs'.1, hs'.2.trans_lt (hr.2.trans hcell.2.2)⟩
  have ha : 0 < C.left m := hg.1.trans hcell.1
  let O : Set ℝ := Icc (-(ε / 2)) (ε / 2)
  have hO : O ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith [hN.2.1]) (half_pos hN.2.1)
  have hzero : (0 : ℝ) ∈ O := mem_of_mem_nhds hO
  have hmem (q : ℝ) (hq : q ∈ O) : (x, q) ∈ stateNeighborhood S C base ε :=
    n08_halfParameter_mem hN.2.1 hx hq
  let f : ℝ → ℝ → ℝ := fun q s => C.minusFlow (x, q) m s θ
  have hcont (q : ℝ) (hq : q ∈ O) : ContinuousOn (f q) (Icc (C.left m) r) :=
    (hflow (x, q) (hmem q hq) m θ).2.1.mono (Icc_subset_Icc le_rfl hr.2.le)
  obtain ⟨KF, L, hKF, hbox⟩ := n08_minusFlow_parameter_box hN x hx m θ hr
  let w : ℝ → ℝ := stateProfile D S C x
  let Z : ℝ × PolarPoint → ℝ := fun z => stateHeight D S C (x, z.1) z.2
  have hw : ContDiff ℝ ∞ w := contDiff_stateProfile_of_n01 hS hT hN x
  have hZ : ContDiff ℝ ∞ Z := n08_stateHeight_parameter_contDiff hT hS hN x
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
    simpa only [n08_minusCharacteristicSpeed_eq_jacobi, V, W, w, Z, f] using
      n08_minusFlow_rhs_parameter_zero hT hS hN x hx hs m θ hi
  have htime (q : ℝ) (hq : q ∈ O) (s : ℝ) (hs' : s ∈ Ioo (C.left m) r) :
      HasDerivAt (f q) (V q s) s := by
    simpa only [n08_minusCharacteristicSpeed_eq_jacobi, f, V, w, Z] using
      (hflow (x, q) (hmem q hq) m θ).2.2.1 s ⟨hs'.1, hs'.2.trans hr.2⟩
  exact n08_hasDerivAt_integralTrajectory (f := f) (V := V) (W := W)
    (K := KV * max 1 KF) hr.1.le hO hcont
    (fun q hq => (hflow (x, q) (hmem q hq) m θ).1)
    htime hVint (hWc.intervalIntegrable_of_Icc hr.1.le) hVL hVd

end ContinuousFlexibility.Statements
