import ContinuousFlexibility.Analysis.N05CanonicalSourceLinearity
import ContinuousFlexibility.Analysis.N05PhysicalGraphUniqueness
import ContinuousFlexibility.Analysis.N05ReferenceScalarLinearity
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Continuous linear restrictions of the fixed canonical inverse

Physical graph uniqueness transfers actual source identities to the same
physical inverse. The selected endpoint scalar and the unique canonical L²
sequence then transfer this linearity to the fixed global canonical map.
Its existing square bound makes each stronger volume restriction continuous.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γw γ M0 M1 : ℝ} {G : RadialSource → RadialUnknown}
  (hD : IsRadialReference D) (hT : IsMaterialData D T)
  (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)

/-- Actual source class identities suffice even for canonical sequences
not presented as members of a particular volume level. -/
theorem n05CanonicalGlobalInverse_linear_combination_of_source_ae
    {F H J : CanonicalSequence S K}
    (hF : SourceMember D γw M0 (n05CanonicalNormalizedSource D S C K F))
    (hH : SourceMember D γw M0 (n05CanonicalNormalizedSource D S C K H))
    (hJ : SourceMember D γw M0 (n05CanonicalNormalizedSource D S C K J))
    (c d : ℝ)
    (hsource : (n05CanonicalNormalizedSource D S C K J).1
      =ᵐ[radialPhysicalMeasure D]
        (c • n05CanonicalNormalizedSource D S C K F +
          d • n05CanonicalNormalizedSource D S C K H).1)
    (hscalar : n05CanonicalAuxiliaryScalar D S C K J =
      c * n05CanonicalAuxiliaryScalar D S C K F +
        d * n05CanonicalAuxiliaryScalar D S C K H) :
    n05CanonicalGlobalInverse D S C K G J =
      c • n05CanonicalGlobalInverse D S C K G F +
        d • n05CanonicalGlobalInverse D S C K G H := by
  let N := n05CanonicalNormalizedSource D S C K
  let U : CanonicalSequence S K → RadialUnknown := fun x => G (N x)
  let A : CanonicalSequence S K → ℝ := fun x => n05_referenceLeftConstant D (U x)
  let f : CanonicalSequence S K → PolarPoint → ℝ :=
    fun x p => (U x).1 p - A x * S.chiLeft p.1
  let B : CanonicalSequence S K → CanonicalL2Sequence S K :=
    fun x => n05CanonicalHeightL2Sequence S C K (f x)
  have hsum : SourceMember D γw M0 (c • N F + d • N H) :=
    SourceMember.add hD.1.choose_spec.1.2.1.le hD.1.choose_spec.2.1
      (SourceMember.smul hF c) (SourceMember.smul hH d)
  have hzero : (N J).2 = (c • N F + d • N H).2 := by
    change (0 : ℝ) = c * 0 + d * 0
    ring
  have hsame : RadialRepresentativeEq D (U J) (G (c • N F + d • N H)) :=
    n05_referenceGraph_unique_source_ae hD.1 hγw hG
      (hG.1 _ hJ) (hG.1 _ hsum) hzero hsource
  have hlin : RadialRepresentativeEq D (U J) (c • U F + d • U H) :=
    RadialRepresentativeEq.trans hsame (hG.2.2.1 (N F) (N H) hF hH c d)
  have hA : A J = c * A F + d * A H :=
    (n05_referenceLeftConstant_congr_ae hD.1 hD.2.2.2.1 hγw
      (hG.1 _ hJ).1 (hG.1 _ hsum).1 hsame).trans
      (n05_referenceInverse_leftConstant_linear_combination
        hD.1 hD.2.2.2.1 hγw hG hF hH c d)
  have hf : f J =ᵐ[radialPhysicalMeasure D] (fun p => c * f F p + d * f H p) := by
    filter_upwards [hlin.2] with p hp
    change (U J).1 p = c * (U F).1 p + d * (U H).1 p at hp
    change (U J).1 p - A J * S.chiLeft p.1 =
      c * ((U F).1 p - A F * S.chiLeft p.1) +
        d * ((U H).1 p - A H * S.chiLeft p.1)
    rw [hp, hA]
    ring
  obtain ⟨_, _, houtput⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hγw M1
  have hrep (x : CanonicalSequence S K) (hx : SourceMember D γw M0 (N x)) (m : ℕ) :
      (B x m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (C.referenceState, 0) m (f x) := by
    obtain ⟨a, ha⟩ := (hG.1 _ hx).1
    have hselected : OutputRealization D γw M1 (A x) (U x) := by
      change OutputRealization D γw M1 (n05_referenceLeftConstant D (U x)) (U x)
      rw [n05_referenceLeftConstant_eq hD.1 hD.2.2.2.1 hγw ha]
      exact ha
    exact (houtput (A x) (U x) hselected).1 m
  have hB : B J = c • B F + d • B H := by
    change n05CanonicalHeightL2Sequence S C K (f J) = c • B F + d • B H
    rw [n05CanonicalHeightL2Sequence_congr_ae h hcoordinates hf]
    apply n05CanonicalHeightL2Sequence_eq_of_rep
    intro m
    have hcomb : ((c • B F + d • B H) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] (fun p => c * B F m p + d * B H m p) := by
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply]
      filter_upwards [Lp.coeFn_add (c • B F m) (d • B H m),
        Lp.coeFn_smul c (B F m), Lp.coeFn_smul d (B H m)] with p hp hc hd
      rw [hp]
      simp only [Pi.add_apply, hc, hd, Pi.smul_apply, smul_eq_mul]
    filter_upwards [hcomb, hrep F hF m, hrep H hH m] with p hp hv hw
    rw [hp]
    dsimp only
    rw [hv, hw]
    simp only [canonicalHeight]
    ring
  apply Prod.ext
  · exact hB
  · apply Prod.ext
    · exact hA
    · exact Prod.ext hlin.1 hscalar

variable {V : VolumeModelData S K} (hV : IsVolumeModel T S K V) (hgap : γw < γ)

theorem n05CanonicalGlobalInverse_linear_combination {t : ℝ} {s : ℕ}
    (v w : V.level γ t s) (c d : ℝ) :
    n05CanonicalGlobalInverse D S C K G (V.forget γ t s (c • v + d • w)) =
      c • n05CanonicalGlobalInverse D S C K G (V.forget γ t s v) +
        d • n05CanonicalGlobalInverse D S C K G (V.forget γ t s w) := by
  apply n05CanonicalGlobalInverse_linear_combination_of_source_ae
    hD hT hS h hcoordinates hγw hG
    (n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s v)
    (n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s w)
    (n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s
      (c • v + d • w)) c d
  · exact (n05CanonicalNormalizedSource_linear_combination_ae
      hD.1 hT h hcoordinates hV hγw hgap M0 v w c d).2
  · exact n05CanonicalAuxiliaryScalar_linear_combination
      hD.1 hT h hcoordinates hV hγw hgap M0 v w c d

theorem n05CanonicalGlobalInverse_norm_bound (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : V.level γ t s,
      ‖n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)‖ ≤ B * ‖v‖ := by
  obtain ⟨C0, hC0, hbound⟩ :=
    n05CanonicalGlobalInverse_square_bound hD hT hS h hcoordinates hV hγw hgap hG t s
  refine ⟨Real.sqrt C0, Real.sqrt_pos.2 hC0, fun v => ?_⟩
  let u := n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)
  have hb : ‖u.1‖ ^ 2 + u.2.1 ^ 2 + u.2.2.1 ^ 2 + u.2.2.2 ^ 2 ≤ C0 * ‖v‖ ^ 2 :=
    hbound v
  have hsquare (x : ℝ) (hx : x ^ 2 ≤ C0 * ‖v‖ ^ 2) :
      |x| ≤ Real.sqrt C0 * ‖v‖ := by
    apply abs_le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hC0.le] using hx
  have hn0 := sq_nonneg ‖u.1‖
  have hn1 := sq_nonneg u.2.1
  have hn2 := sq_nonneg u.2.2.1
  have hn3 := sq_nonneg u.2.2.2
  have hfirst := hsquare ‖u.1‖ (by nlinarith only [hb, hn1, hn2, hn3])
  rw [abs_of_nonneg (norm_nonneg _)] at hfirst
  change ‖u‖ ≤ Real.sqrt C0 * ‖v‖
  simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff]
  exact ⟨hfirst, hsquare _ (by nlinarith only [hb, hn0, hn2, hn3]),
    hsquare _ (by nlinarith only [hb, hn0, hn1, hn3]),
    hsquare _ (by nlinarith only [hb, hn0, hn1, hn2])⟩

/-- This linear map has exactly the fixed global inverse as its value. -/
def n05CanonicalInverseLinear (t : ℝ) (s : ℕ) :
    V.level γ t s →ₗ[ℝ] CanonicalUnknown S K where
  toFun v := n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)
  map_add' v w := by
    simpa only [one_smul] using
      n05CanonicalGlobalInverse_linear_combination
        hD hT hS h hcoordinates hγw hG hV hgap v w 1 1
  map_smul' c v := by
    simpa only [zero_smul, add_zero] using
      n05CanonicalGlobalInverse_linear_combination
        hD hT hS h hcoordinates hγw hG hV hgap v v c 0

@[simp] theorem n05CanonicalInverseLinear_apply (t : ℝ) (s : ℕ) (v : V.level γ t s) :
    n05CanonicalInverseLinear hD hT hS h hcoordinates hγw hG hV hgap t s v =
      n05CanonicalGlobalInverse D S C K G (V.forget γ t s v) := rfl

/-- The bounded restriction on every stronger actual volume level. -/
def n05CanonicalInverseCLM (t : ℝ) (s : ℕ) :
    V.level γ t s →L[ℝ] CanonicalUnknown S K :=
  (n05CanonicalInverseLinear hD hT hS h hcoordinates hγw hG hV hgap t s).
    mkContinuousOfExistsBound (by
      obtain ⟨B, _, hB⟩ :=
        n05CanonicalGlobalInverse_norm_bound hD hT hS h hcoordinates hγw hG hV hgap t s
      exact ⟨B, hB⟩)

@[simp] theorem n05CanonicalInverseCLM_apply (t : ℝ) (s : ℕ) (v : V.level γ t s) :
    n05CanonicalInverseCLM hD hT hS h hcoordinates hγw hG hV hgap t s v =
      n05CanonicalGlobalInverse D S C K G (V.forget γ t s v) := by
  rw [n05CanonicalInverseCLM, LinearMap.mkContinuousOfExistsBound_apply,
    n05CanonicalInverseLinear_apply]

/-- The fixed base layer required by the canonical common domain. -/
def n05CanonicalBaseInverse (hbase : γw < (3 / 4 : ℝ)) :
    V.level (3 / 4 : ℝ) 0 2 →L[ℝ] CanonicalUnknown S K :=
  n05CanonicalInverseCLM hD hT hS h hcoordinates hγw hG hV hbase 0 2

@[simp] theorem n05CanonicalBaseInverse_apply (hbase : γw < (3 / 4 : ℝ))
    (v : V.level (3 / 4 : ℝ) 0 2) :
    n05CanonicalBaseInverse hD hT hS h hcoordinates hγw hG hV hbase v =
      n05CanonicalGlobalInverse D S C K G (V.forget (3 / 4 : ℝ) 0 2 v) :=
  n05CanonicalInverseCLM_apply hD hT hS h hcoordinates hγw hG hV hbase 0 2 v

end ContinuousFlexibility.Statements
