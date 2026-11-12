import ContinuousFlexibility.Analysis.N07aCanonicalMixedPointwise
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Analysis.N07aCanonicalOpenTests
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compatible closed jets from bounded smooth interior jets

Each scalar mixed derivative has a Lipschitz extension. The derivatives of
these extensions agree with the next extended jets relative to the closed
strip. This constructs genuine one-sided jets without asserting that the
chosen extensions are differentiable outside the strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N07aClosedJets

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology NNReal

def openStrip (l r : ℝ) : Set PolarPoint := Ioo l r ×ˢ univ

def closedStrip (l r : ℝ) : Set PolarPoint := Icc l r ×ˢ univ

theorem closure_openStrip {l r : ℝ} (hlr : l < r) :
    closure (openStrip l r) = closedStrip l r := by
  simp only [openStrip, closedStrip, closure_prod_eq, closure_Ioo hlr.ne, closure_univ]

/-- The genuine two-coordinate derivative with the stated scalar entries. -/
def scalarGradient (a b : ℝ) : PolarPoint →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem scalarGradient_apply (a b : ℝ) (v : PolarPoint) :
    scalarGradient a b v = a * v.1 + b * v.2 := by
  simp only [scalarGradient, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem scalarGradient_norm_le (a b : ℝ) :
    ‖scalarGradient a b‖ ≤ |a| + |b| := by
  calc
    ‖scalarGradient a b‖ ≤
        ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ‖ +
          ‖b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
    _ = |a| + |b| := by simp [norm_smul, Real.norm_eq_abs]

theorem scalarCLM_eq_gradient (L : PolarPoint →L[ℝ] ℝ) :
    L = scalarGradient (L (1, 0)) (L (0, 1)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [scalarGradient_apply]
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp [smul_eq_mul]
  calc
    L v = L (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg L hv
    _ = L (1, 0) * v.1 + L (0, 1) * v.2 := by
      simp only [map_add, map_smul, smul_eq_mul, mul_comm]

theorem continuous_scalarGradient {X : Type*} [TopologicalSpace X]
    {A B : X → ℝ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => scalarGradient (A x) (B x)) :=
  (hA.smul continuous_const).add (hB.smul continuous_const)

/-- Interior mixed jets have the two next mixed jets as derivative entries. -/
theorem mixed_hasFDerivAt {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    HasFDerivAt (mixedDerivative a b f)
      (scalarGradient (mixedDerivative (a + 1) b f p)
        (mixedDerivative a (b + 1) f p)) p := by
  have hg := contDiffOn_mixedDerivative hU hf a b
  have hr := n07a_radialPartial_mixedDerivative_on hU hf a b hp
  have ht : angularPartial (mixedDerivative a b f) p =
      mixedDerivative a (b + 1) f p := by
    calc
      angularPartial (mixedDerivative a b f) p =
          mixedDerivative 0 1 (mixedDerivative a b f) p := by
        simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
          n07a_angularPartial_zero_mixedDerivative_on hU hg 0 hp
      _ = mixedDerivative (0 + a) (1 + b) f p :=
        n07a_mixedDerivative_mixedDerivative_on hU hf 0 1 a b hp
      _ = mixedDerivative a (b + 1) f p := by
        simp only [Nat.zero_add, Nat.add_comm 1 b]
  have he : fderiv ℝ (mixedDerivative a b f) p =
      scalarGradient (mixedDerivative (a + 1) b f p)
        (mixedDerivative a (b + 1) f p) := by
    calc
      fderiv ℝ (mixedDerivative a b f) p =
          scalarGradient (radialPartial (mixedDerivative a b f) p)
            (angularPartial (mixedDerivative a b f) p) := scalarCLM_eq_gradient _
      _ = _ := by rw [hr, ht]
  exact ((hg.contDiffAt (hU.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.congr_fderiv he

/-- A bound on the two next jets gives a global Lipschitz estimate on the
entire convex open strip, including its unbounded angular direction. -/
theorem mixed_lipschitzOn {l r : ℝ} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (openStrip l r)) (a b : ℕ)
    (Mr Mθ : ℝ≥0)
    (hr : ∀ p ∈ openStrip l r, |mixedDerivative (a + 1) b f p| ≤ Mr)
    (hθ : ∀ p ∈ openStrip l r, |mixedDerivative a (b + 1) f p| ≤ Mθ) :
    LipschitzOnWith (Mr + Mθ) (mixedDerivative a b f) (openStrip l r) := by
  have hConv : Convex ℝ (openStrip l r) :=
    (convex_Ioo l r).prod (convex_univ : Convex ℝ (univ : Set ℝ))
  refine hConv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun p hp => (mixed_hasFDerivAt (isOpen_Ioo.prod isOpen_univ)
      hf a b hp).hasFDerivWithinAt) ?_
  intro p hp
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_add]
  exact (scalarGradient_norm_le _ _).trans (add_le_add (hr p hp) (hθ p hp))

/-- Only the restriction to `closedStrip` is a compatible jet family.
Global continuity is a convenient consequence of the Lipschitz extension. -/
structure ClosedJetTower (l r : ℝ) (f : PolarPoint → ℝ) where
  value : ℕ → ℕ → PolarPoint → ℝ
  continuous : ∀ a b, Continuous (value a b)
  agrees : ∀ a b, EqOn (value a b) (mixedDerivative a b f) (openStrip l r)
  derivative : ∀ a b p, p ∈ closedStrip l r →
    HasFDerivWithinAt (value a b)
      (scalarGradient (value (a + 1) b p) (value a (b + 1) p)) (closedStrip l r) p

/-- Construction from actual smooth interior jets and finite pointwise
bounds. No values or traces of the original arbitrary total function at
the endpoints are used. -/
theorem closedJetTower_nonempty {l r : ℝ} (hlr : l < r) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (openStrip l r))
    (hbound : ∀ a b, ∃ M : ℝ≥0, ∀ p ∈ openStrip l r,
      |mixedDerivative a b f p| ≤ M) :
    Nonempty (ClosedJetTower l r f) := by
  classical
  choose M hM using hbound
  have hLip (a b : ℕ) :
      LipschitzOnWith (M (a + 1) b + M a (b + 1))
        (mixedDerivative a b f) (openStrip l r) :=
    mixed_lipschitzOn hf a b _ _ (hM (a + 1) b) (hM a (b + 1))
  choose J hJL hJ using fun a b => (hLip a b).extend_real
  have hOpen : IsOpen (openStrip l r) := isOpen_Ioo.prod isOpen_univ
  have hConv : Convex ℝ (openStrip l r) := (convex_Ioo l r).prod convex_univ
  have hInterior (a b : ℕ) (p : PolarPoint) (hp : p ∈ openStrip l r) :
      HasFDerivAt (J a b)
        (scalarGradient (J (a + 1) b p) (J a (b + 1) p)) p := by
    have he : J a b =ᶠ[𝓝 p] mixedDerivative a b f := by
      filter_upwards [hOpen.mem_nhds hp] with q hq
      exact (hJ a b hq).symm
    have hd := (mixed_hasFDerivAt hOpen hf a b hp).congr_of_eventuallyEq he
    rw [hJ (a + 1) b hp, hJ a (b + 1) hp] at hd
    exact hd
  have hClosed (a b : ℕ) (p : PolarPoint) :
      HasFDerivWithinAt (J a b)
        (scalarGradient (J (a + 1) b p) (J a (b + 1) p)) (closedStrip l r) p := by
    have hGrad : Continuous (fun q =>
        scalarGradient (J (a + 1) b q) (J a (b + 1) q)) :=
      continuous_scalarGradient (hJL (a + 1) b).continuous (hJL a (b + 1)).continuous
    have he : (fun q => fderiv ℝ (J a b) q) =ᶠ[𝓝[openStrip l r] p]
        (fun q => scalarGradient (J (a + 1) b q) (J a (b + 1) q)) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hInterior a b q hq).fderiv
    have hlim : Tendsto (fun q => fderiv ℝ (J a b) q) (𝓝[openStrip l r] p)
        (𝓝 (scalarGradient (J (a + 1) b p) (J a (b + 1) p))) :=
      Filter.Tendsto.congr' he.symm hGrad.continuousWithinAt
    have hd := hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hInterior a b q hq).differentiableAt.differentiableWithinAt)
      hConv hOpen (fun q _ => (hJL a b).continuous.continuousWithinAt) hlim
    simpa only [closure_openStrip hlr] using hd
  exact ⟨⟨J, (fun a b => (hJL a b).continuous),
    (fun a b => (hJ a b).symm), (fun a b p _ => hClosed a b p)⟩⟩

namespace ClosedJetTower

variable {l r : ℝ} {f : PolarPoint → ℝ} (J : ClosedJetTower l r f)

/-- The compatible tower proves smoothness relative to the closed strip.
This is within-set smoothness of the extension, with no assertion about
its values on the other side of either endpoint. -/
theorem contDiffOn (hlr : l < r) (a b : ℕ) :
    ContDiffOn ℝ ∞ (J.value a b) (closedStrip l r) := by
  have hunique : UniqueDiffOn ℝ (closedStrip l r) :=
    (uniqueDiffOn_Icc hlr).prod uniqueDiffOn_univ
  have hfinite (n : ℕ) :
      ∀ a b, ContDiffOn ℝ (n : ℕ∞ω) (J.value a b) (closedStrip l r) := by
    induction n with
    | zero =>
        intro a b
        exact contDiffOn_zero.mpr (J.continuous a b).continuousOn
    | succ n ih =>
        intro a b
        rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
          contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hunique]
        refine ⟨by simp, (fun p =>
          scalarGradient (J.value (a + 1) b p) (J.value a (b + 1) p)), ?_, ?_⟩
        · exact ((ih (a + 1) b).smul contDiffOn_const).add
            ((ih a (b + 1)).smul contDiffOn_const)
        · exact J.derivative a b
  exact contDiffOn_infty.mpr fun n => hfinite n a b

/-- Angular slices lie in the closed strip for every nearby parameter, so
the one-sided planar derivative gives an ordinary two-sided trace derivative. -/
theorem hasDerivAt_angular (a b : ℕ) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc l r) (θ : ℝ) :
    HasDerivAt (fun t => J.value a b (r₀, t)) (J.value a (b + 1) (r₀, θ)) θ := by
  have hd := J.derivative a b (r₀, θ) ⟨hr₀, mem_univ θ⟩
  have hslice : HasDerivAt (fun t : ℝ => (r₀, t)) (0, 1) θ :=
    (hasDerivAt_const θ r₀).prodMk (hasDerivAt_id' θ)
  have hmap : ∀ᶠ t in 𝓝 θ, (r₀, t) ∈ closedStrip l r :=
    Eventually.of_forall fun t => ⟨hr₀, mem_univ t⟩
  simpa only [Function.comp_def, scalarGradient_apply, mul_zero, mul_one, zero_add]
    using hd.comp_hasDerivAt θ hslice hmap

/-- Genuine radial derivative relative to the closed interval. -/
theorem hasDerivWithinAt_radial (a b : ℕ) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc l r) (θ : ℝ) :
    HasDerivWithinAt (fun t => J.value a b (t, θ))
      (J.value (a + 1) b (r₀, θ)) (Icc l r) r₀ := by
  have hd := J.derivative a b (r₀, θ) ⟨hr₀, mem_univ θ⟩
  have hslice : HasDerivWithinAt (fun t : ℝ => (t, θ)) (1, 0) (Icc l r) r₀ :=
    ((hasDerivAt_id' r₀).prodMk (hasDerivAt_const r₀ θ)).hasDerivWithinAt
  have hmap : MapsTo (fun t : ℝ => (t, θ)) (Icc l r) (closedStrip l r) :=
    fun t ht => ⟨ht, mem_univ θ⟩
  simpa only [Function.comp_def, scalarGradient_apply, mul_one, mul_zero, add_zero]
    using hd.comp_hasDerivWithinAt r₀ hslice hmap

theorem hasDerivWithinAt_left (hlr : l < r) (a b : ℕ) (θ : ℝ) :
    HasDerivWithinAt (fun t => J.value a b (t, θ))
      (J.value (a + 1) b (l, θ)) (Ici l) l :=
  (J.hasDerivWithinAt_radial a b ⟨le_rfl, hlr.le⟩ θ).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE hlr)

theorem hasDerivWithinAt_right (hlr : l < r) (a b : ℕ) (θ : ℝ) :
    HasDerivWithinAt (fun t => J.value a b (t, θ))
      (J.value (a + 1) b (r, θ)) (Iic r) r :=
  (J.hasDerivWithinAt_radial a b ⟨hlr.le, le_rfl⟩ θ).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE hlr)

theorem iteratedDeriv_angular (a b n : ℕ) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Icc l r) (θ : ℝ) :
    iteratedDeriv n (fun t => J.value a b (r₀, t)) θ = J.value a (b + n) (r₀, θ) := by
  induction n generalizing θ with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun t => J.value a b (r₀, t)) =
        (fun t => J.value a (b + n) (r₀, t)) := funext ih
    rw [iteratedDeriv_succ, he]
    simpa only [Nat.add_assoc] using (J.hasDerivAt_angular a (b + n) hr₀ θ).deriv

/-- Every angular boundary trace is smooth, including traces of radial jets. -/
theorem contDiff_angular (a b : ℕ) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc l r) :
    ContDiff ℝ ∞ (fun θ => J.value a b (r₀, θ)) := by
  have he (n : ℕ) : iteratedDeriv n (fun θ => J.value a b (r₀, θ)) =
      (fun θ => J.value a (b + n) (r₀, θ)) :=
    funext fun θ => J.iteratedDeriv_angular a b n hr₀ θ
  refine contDiff_iff_iteratedDeriv.mpr ⟨?_, ?_⟩
  · intro n _
    rw [he n]
    exact (J.continuous a (b + n)).comp (continuous_const.prodMk continuous_id)
  · intro n _
    rw [he n]
    exact fun θ => (J.hasDerivAt_angular a (b + n) hr₀ θ).differentiableAt

/-- Extension choices cannot change any closed jet. -/
theorem unique_on_closed (hlr : l < r) (J' : ClosedJetTower l r f) (a b : ℕ) :
    EqOn (J.value a b) (J'.value a b) (closedStrip l r) := by
  have he : EqOn (J.value a b) (J'.value a b) (openStrip l r) :=
    fun p hp => (J.agrees a b hp).trans (J'.agrees a b hp).symm
  simpa only [closure_openStrip hlr] using
    he.closure (J.continuous a b) (J'.continuous a b)

/-- A given interior scalar bound passes to the closed jet with the same constant. -/
theorem bound_on_closed (hlr : l < r) (a b : ℕ) {M : ℝ}
    (hM : ∀ p ∈ openStrip l r, |mixedDerivative a b f p| ≤ M) :
    ∀ p ∈ closedStrip l r, |J.value a b p| ≤ M := by
  have hsub : openStrip l r ⊆ {p | |J.value a b p| ≤ M} := by
    intro p hp
    exact (congrArg abs (J.agrees a b hp)).le.trans (hM p hp)
  have hclosed : IsClosed {p | |J.value a b p| ≤ M} :=
    isClosed_le (J.continuous a b).abs continuous_const
  have hclosure := closure_minimal hsub hclosed
  rw [closure_openStrip hlr] at hclosure
  intro p hp
  exact hclosure hp

/-- Periodicity of the interior jets passes to their unique closed traces. -/
theorem periodic_on_closed (hlr : l < r) (P : ℝ)
    (hper : ∀ a b p, p ∈ openStrip l r →
      mixedDerivative a b f (p + (0, P)) = mixedDerivative a b f p)
    (a b : ℕ) : ∀ p ∈ closedStrip l r,
      J.value a b (p + (0, P)) = J.value a b p := by
  have he : EqOn (fun p => J.value a b (p + (0, P))) (J.value a b) (openStrip l r) := by
    intro p hp
    have hp' : p + (0, P) ∈ openStrip l r :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    exact (J.agrees a b hp').trans ((hper a b p hp).trans (J.agrees a b hp).symm)
  have hclosure := he.closure
    ((J.continuous a b).comp (continuous_id.add continuous_const)) (J.continuous a b)
  rw [closure_openStrip hlr] at hclosure
  intro p hp
  exact hclosure hp

end ClosedJetTower

/-- The actual mixed L² estimates already provide every pointwise bound
needed for the compatible closed jet construction. -/
theorem canonical_closedJetTower_nonempty
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hm : K.left m < K.right m) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hper : ∀ x ∈ canonicalOpen S K m, f (x + (0, Real.pi)) = f x)
    (hmem : ∀ a b, MeasureTheory.MemLp (mixedDerivative a b f) 2
      (canonicalMeasure S K m)) :
    Nonempty (ClosedJetTower (K.left m) (K.right m) f) := by
  apply closedJetTower_nonempty hm hf
  intro a b
  let R : ℝ := (1 + 2 * (K.right m - K.left m)⁻¹) *
    Real.sqrt (Real.pi * (K.right m - K.left m)) *
      ((MeasureTheory.eLpNorm (mixedDerivative a b f) 2
          (canonicalMeasure S K m)).toReal +
        (MeasureTheory.eLpNorm (mixedDerivative (a + 1) b f) 2
          (canonicalMeasure S K m)).toReal +
        (MeasureTheory.eLpNorm (mixedDerivative a (b + 1) f) 2
          (canonicalMeasure S K m)).toReal +
        (MeasureTheory.eLpNorm (mixedDerivative (a + 1) (b + 1) f) 2
          (canonicalMeasure S K m)).toReal)
  refine ⟨⟨max R 0, le_max_right R 0⟩, ?_⟩
  intro p hp
  exact (n07a_canonicalOpen_mixed_pointwise_L2 hm hf hper hmem a b hp).trans
    (le_max_left R 0)

end ContinuousFlexibility.Analysis.N07aClosedJets
