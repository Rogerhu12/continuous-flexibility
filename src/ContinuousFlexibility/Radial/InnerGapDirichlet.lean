import ContinuousFlexibility.Radial.InnerGapEnergyCoordinates
import ContinuousFlexibility.Radial.InnerCoerciveGradient
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The actual positive-gap Dirichlet inverse for arbitrary L² forcing

The energy domain is the closure of actual smooth compactly supported
radial functions, with their function, weighted derivative, and weighted
potential coordinates in the physical measure μ_D. Coercivity passes
from the scalar radial integral to this closed Hilbert space.

Lax-Milgram then constructs a single continuous linear inverse for every
physical L² source. The graph equivalence retains the zero-Dirichlet
closed form domain, and its norm bound has the required j⁻² scale.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

abbrev InnerGapEnergyTriple (D : ReferenceData) :=
  WithLp 2 (RadialModeL2 D × InnerGapEnergyPair D)

/-- The physical zero-Dirichlet test core, before closure. -/
def InnerGapEnergyCore (D : ReferenceData) (j a b : ℝ) : Set (InnerGapEnergyTriple D) :=
  {q | ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    tsupport u ⊆ Ioo a b ∧
    q.fst =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u ∧
    q.snd.fst =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator (innerGapGradientField u) ∧
    q.snd.snd =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapPotentialField D.w j u)}

theorem innerGapEnergyCore_zero (D : ReferenceData) (j a b : ℝ) :
    (0 : InnerGapEnergyTriple D) ∈ InnerGapEnergyCore D j a b := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_, ?_⟩
  · simp only [tsupport_zero, empty_subset]
  all_goals
    filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr
    by_cases hmem : r ∈ Ioo a b
    · simpa [indicator_of_mem hmem, innerGapGradientField, innerGapPotentialField,
        WithLp.zero_fst, WithLp.zero_snd] using hr
    · simpa only [indicator_of_notMem hmem, WithLp.zero_fst, WithLp.zero_snd] using hr

theorem innerGapEnergyCore_add {D : ReferenceData} {j a b : ℝ}
    {q r : InnerGapEnergyTriple D}
    (hq : q ∈ InnerGapEnergyCore D j a b) (hr : r ∈ InnerGapEnergyCore D j a b) :
    q + r ∈ InnerGapEnergyCore D j a b := by
  rcases hq with ⟨u, hu, hcu, hsu, hu₀, hu₁, hu₂⟩
  rcases hr with ⟨v, hv, hcv, hsv, hv₀, hv₁, hv₂⟩
  refine ⟨u + v, hu.add hv, hcu.add hcv,
    (tsupport_add u v).trans (union_subset hsu hsv), ?_, ?_, ?_⟩
  · simp only [WithLp.add_fst]
    filter_upwards [hu₀, hv₀, Lp.coeFn_add q.fst r.fst] with x hx hy hadd
    rw [hadd, Pi.add_apply, hx, hy]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, Pi.add_apply]
    · simp only [indicator_of_notMem hmem, zero_add]
  · simp only [WithLp.add_snd, WithLp.add_fst]
    filter_upwards [hu₁, hv₁, Lp.coeFn_add q.snd.fst r.snd.fst] with x hx hy hadd
    rw [hadd, Pi.add_apply, hx, hy]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapGradientField,
        deriv_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
      ring
    · simp only [indicator_of_notMem hmem, zero_add]
  · simp only [WithLp.add_snd]
    filter_upwards [hu₂, hv₂, Lp.coeFn_add q.snd.snd r.snd.snd] with x hx hy hadd
    rw [hadd, Pi.add_apply, hx, hy]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapPotentialField, Pi.add_apply, mul_add]
    · simp only [indicator_of_notMem hmem, zero_add]

theorem innerGapEnergyCore_smul {D : ReferenceData} {j a b : ℝ}
    {q : InnerGapEnergyTriple D} (hq : q ∈ InnerGapEnergyCore D j a b) (c : ℝ) :
    c • q ∈ InnerGapEnergyCore D j a b := by
  rcases hq with ⟨u, hu, hcu, hsu, hu₀, hu₁, hu₂⟩
  refine ⟨fun x => c * u x, contDiff_const.mul hu, hcu.mul_left,
    tsupport_mul_subset_right.trans hsu, ?_, ?_, ?_⟩
  · simp only [WithLp.smul_fst]
    filter_upwards [hu₀, Lp.coeFn_smul c q.fst] with x hx hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hx]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem]
    · simp only [indicator_of_notMem hmem, mul_zero]
  · simp only [WithLp.smul_snd, WithLp.smul_fst]
    filter_upwards [hu₁, Lp.coeFn_smul c q.snd.fst] with x hx hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hx]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapGradientField, deriv_const_mul_field]
      ring
    · simp only [indicator_of_notMem hmem, mul_zero]
  · simp only [WithLp.smul_snd]
    filter_upwards [hu₂, Lp.coeFn_smul c q.snd.snd] with x hx hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hx]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapPotentialField]
      ring
    · simp only [indicator_of_notMem hmem, mul_zero]

def innerGapEnergyCoreSubmodule (D : ReferenceData) (j a b : ℝ) :
    Submodule ℝ (InnerGapEnergyTriple D) where
  carrier := InnerGapEnergyCore D j a b
  zero_mem' := innerGapEnergyCore_zero D j a b
  add_mem' := innerGapEnergyCore_add
  smul_mem' := fun c _ hq => innerGapEnergyCore_smul hq c

/-- One complete Hilbert energy domain, constructed from the physical
zero-Dirichlet core. -/
def innerGapFormSpace (D : ReferenceData) (j a b : ℝ) :
    ClosedSubmodule ℝ (InnerGapEnergyTriple D) :=
  (innerGapEnergyCoreSubmodule D j a b).closure

theorem coe_innerGapFormSpace (D : ReferenceData) (j a b : ℝ) :
    (innerGapFormSpace D j a b : Set (InnerGapEnergyTriple D)) =
      closure (InnerGapEnergyCore D j a b) := by
  calc
    _ = closure (innerGapEnergyCoreSubmodule D j a b : Set (InnerGapEnergyTriple D)) := by
      rw [innerGapFormSpace, Submodule.coe_closure]
    _ = _ := rfl

theorem mem_innerGapFormSpace (D : ReferenceData) (j a b : ℝ) (q : InnerGapEnergyTriple D) :
    q ∈ innerGapFormSpace D j a b ↔ q ∈ closure (InnerGapEnergyCore D j a b) :=
  Set.ext_iff.mp (coe_innerGapFormSpace D j a b) q

theorem innerGapEnergyTriple_mem_core (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (hsupport : tsupport u ⊆ Ioo a b) :
    WithLp.toLp 2
      (innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn,
        innerGapEnergyPair D hw ha hcore hpos j u hu) ∈ InnerGapEnergyCore D j a b := by
  refine ⟨u, hu, hcompact, hsupport, ?_, ?_, ?_⟩
  · simp only [WithLp.toLp_fst]
    exact innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn
  · simp only [WithLp.toLp_snd]
    exact innerGapEnergyPair_fst_ae D hw ha hcore hpos j u hu
  · simp only [WithLp.toLp_snd]
    exact innerGapEnergyPair_snd_ae D hw ha hcore hpos j u hu

theorem innerGapEnergyCore_coercive (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hs : 0 ≤ s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (q : InnerGapEnergyTriple D) (hq : q ∈ InnerGapEnergyCore D j a b) :
    ((s / 12) * j ^ 2) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2 := by
  rcases hq with ⟨u, hu, _, _, hu₀, hu₁, hu₂⟩
  have hvalue : q.fst = innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn :=
    Lp.ext (hu₀.trans (innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn).symm)
  have hgrad : q.snd.fst = (innerGapEnergyPair D hw ha hcore hpos j u hu).fst :=
    Lp.ext (hu₁.trans (innerGapEnergyPair_fst_ae D hw ha hcore hpos j u hu).symm)
  have hpot : q.snd.snd = (innerGapEnergyPair D hw ha hcore hpos j u hu).snd :=
    Lp.ext (hu₂.trans (innerGapEnergyPair_snd_ae D hw ha hcore hpos j u hu).symm)
  have henergy : ‖q.snd‖ ^ 2 = ‖innerGapEnergyPair D hw ha hcore hpos j u hu‖ ^ 2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, hgrad, hpot]
  rw [hvalue, henergy]
  exact innerGapEnergyPair_coercive D hw hab ha hs hcore hpos hslope j u hu

/-- The physical energy inequality passes to the complete form domain
because it is a closed inequality of continuous coordinate norms. -/
theorem innerGapFormSpace_coercive (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hs : 0 ≤ s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    ((s / 12) * j ^ 2) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2 := by
  have hf : Continuous (fun q : InnerGapEnergyTriple D => q.fst) :=
    (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hg : Continuous (fun q : InnerGapEnergyTriple D => q.snd) :=
    (WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hclosed : IsClosed {q : InnerGapEnergyTriple D |
      ((s / 12) * j ^ 2) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2} :=
    isClosed_le (continuous_const.mul (hf.norm.pow 2)) (hg.norm.pow 2)
  apply (closure_minimal ?_ hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  intro z hz
  exact innerGapEnergyCore_coercive D hw hab ha hs hcore hpos hslope j z hz

def innerGapFormFunction (D : ReferenceData) (j a b : ℝ) :
    innerGapFormSpace D j a b →L[ℝ] RadialModeL2 D :=
  WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D) ∘L
    (innerGapFormSpace D j a b).toSubmodule.subtypeL

def innerGapFormEnergy (D : ReferenceData) (j a b : ℝ) :
    innerGapFormSpace D j a b →L[ℝ] InnerGapEnergyPair D :=
  WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D) ∘L
    (innerGapFormSpace D j a b).toSubmodule.subtypeL

theorem innerGapFormFunction_apply (D : ReferenceData) (j a b : ℝ)
    (q : innerGapFormSpace D j a b) :
    innerGapFormFunction D j a b q = (q : InnerGapEnergyTriple D).fst := by
  rw [innerGapFormFunction, ContinuousLinearMap.comp_apply, WithLp.fstL_apply]
  exact congrArg WithLp.fst
    (Submodule.subtypeL_apply (innerGapFormSpace D j a b).toSubmodule q)

theorem innerGapFormEnergy_apply (D : ReferenceData) (j a b : ℝ)
    (q : innerGapFormSpace D j a b) :
    innerGapFormEnergy D j a b q = (q : InnerGapEnergyTriple D).snd := by
  rw [innerGapFormEnergy, ContinuousLinearMap.comp_apply, WithLp.sndL_apply]
  exact congrArg WithLp.snd
    (Submodule.subtypeL_apply (innerGapFormSpace D j a b).toSubmodule q)

theorem innerGapForm_isCoercive (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) :
    IsCoercive (innerGradientForm (E := innerGapFormSpace D j a b)
      (Z := InnerGapEnergyPair D) (innerGapFormEnergy D j a b)) := by
  apply innerGradientForm_isCoercive (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b) (δ := (s / 12) * j ^ 2)
    (mul_pos (div_pos hs (by norm_num)) (sq_pos_of_pos hj))
  · intro q
    rw [innerGapFormFunction_apply, innerGapFormEnergy_apply]
    exact WithLp.prod_norm_sq_eq_of_L2 (q : InnerGapEnergyTriple D)
  · intro q
    rw [innerGapFormFunction_apply, innerGapFormEnergy_apply]
    exact innerGapFormSpace_coercive D hw hab ha hs.le hcore hpos hslope j q q.property

/-- The actual closed zero-Dirichlet radial form graph. -/
def InnerGapFormGraph (D : ReferenceData) (j a b : ℝ) (u f : RadialModeL2 D) : Prop :=
  InnerGradientGraph (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b) u f

theorem innerGapFormGraph_iff (D : ReferenceData) (j a b : ℝ) (u f : RadialModeL2 D) :
    InnerGapFormGraph D j a b u f ↔
      ∃ q : InnerGapEnergyTriple D, q ∈ innerGapFormSpace D j a b ∧ q.fst = u ∧
        ∀ r ∈ innerGapFormSpace D j a b, ⟪f, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ := by
  constructor
  · rintro ⟨q, hq, hform⟩
    refine ⟨q, q.property, ?_, ?_⟩
    · simpa only [innerGapFormFunction_apply] using hq
    · intro r hr
      simpa only [innerGapFormFunction_apply, innerGapFormEnergy_apply] using hform ⟨r, hr⟩
  · rintro ⟨q, hq, hvalue, hform⟩
    refine ⟨⟨q, hq⟩, ?_, ?_⟩
    · simpa only [innerGapFormFunction_apply] using hvalue
    · intro r
      simpa only [innerGapFormFunction_apply, innerGapFormEnergy_apply] using
        hform r r.property

/-- Lax-Milgram constructs the actual inverse for arbitrary physical
L² forcing. No gap inverse or solvability hypothesis is an input. -/
def innerGapDirichletInverse (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  innerCoerciveGradientInverse (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b)
    (innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope)

theorem innerGapDirichletInverse_graph_iff (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) (u f : RadialModeL2 D) :
    InnerGapFormGraph D j a b u f ↔
      innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f = u :=
  innerGradientGraph_iff_inverse (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b)
    (innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope) u f

theorem innerGapDirichletInverse_graph (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) (f : RadialModeL2 D) :
    InnerGapFormGraph D j a b
      (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope f) f :=
  innerCoerciveGradientInverse_graph (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b)
    (innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope) f

theorem innerGapDirichletInverse_isSymmetric (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) :
    (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope).IsSymmetric :=
  innerCoerciveGradientInverse_isSymmetric (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b)
    (innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope)

theorem innerGapDirichletInverse_norm_le (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) :
    ‖innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope‖ ≤ 12 / (s * j ^ 2) := by
  calc
    _ ≤ ((s / 12) * j ^ 2)⁻¹ := by
      apply innerCoerciveGradientInverse_norm_le (E := innerGapFormSpace D j a b)
        (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
        (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b)
        (innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope)
        (δ := (s / 12) * j ^ 2)
        (mul_pos (div_pos hs (by norm_num)) (sq_pos_of_pos hj))
      intro q
      rw [innerGapFormFunction_apply, innerGapFormEnergy_apply]
      exact innerGapFormSpace_coercive D hw hab ha hs.le hcore hpos hslope j q q.property
    _ = _ := by field_simp [hs.ne', hj.ne'] <;> ring

end ContinuousFlexibility.Radial
