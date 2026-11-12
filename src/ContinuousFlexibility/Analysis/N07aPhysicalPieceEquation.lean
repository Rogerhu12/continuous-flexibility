import ContinuousFlexibility.Analysis.N07aCanonicalCutoffColumn
import ContinuousFlexibility.Analysis.N07aCanonicalDifference
import ContinuousFlexibility.Analysis.N07aLocalPullbackEquation
import ContinuousFlexibility.Analysis.N07aClosedPhysicalHeight
import ContinuousFlexibility.Analysis.N07aScalarSourceTerminal
import ContinuousFlexibility.Analysis.N07aAngularNuRegularity

/-!
# The physical equation of the genuine closed negative-piece height

The normalized canonical equation is the one already derived from the
original weak relation. On a negative piece its principal coefficients
are exactly `1, 0, -s`. Local smooth tests apply N04 to the open decoder,
and the positive source factor recovers its actual physical equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open N07aClosedJets
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- N04's global-test identity applies to every smooth periodic open
decoder, because the differential expression depends only on its germ. -/
theorem n07a_physicalHeight_source_operator_on
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hvp : ∀ p ∈ canonicalOpen S K m, v (p + (0, Real.pi)) = v p) :
    EqOn (canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n07aPhysicalHeightRepresentative K z m v)))
      (fun p => divergenceOperator (K.coefficients z m) v p +
        (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p * v p)
      (canonicalOpen S K m) := by
  have hchart := h04.1.charts z hz hs m
  have hopen := (h04.1.domains z hz hs m).1
  intro p hp
  obtain ⟨W, hW, hWv⟩ := n07a_canonicalOpen_germ_test hv hvp hp
  have hx := hchart.2.1 hp
  have hF : Tendsto (K.chart z m) (𝓝 (K.inverseChart z m p)) (𝓝 p) := by
    simpa only [hchart.2.2.2.1 p hp] using
      (hchart.2.2.2.2.1.contDiffAt (hopen.mem_nhds hx)).continuousAt.tendsto
  have hphysical : n07aPhysicalTestPullback S K z m W =ᶠ[𝓝 (K.inverseChart z m p)]
      n07aPhysicalHeightRepresentative K z m v := by
    filter_upwards [n07aPhysicalTestPullback_germ z m W hopen hx,
      hWv.comp_tendsto hF] with q hq he
    change W (K.chart z m q) = v (K.chart z m q) at he
    exact hq.trans (congrArg (K.height z m q * ·) he)
  have hd := n07a_divergenceOperator_unknown_germ (L.coefficients z) hphysical
  have hsource : canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W)) p =
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n07aPhysicalHeightRepresentative K z m v)) p := by
    simp only [canonicalSource, hd]
  have he := n07aPhysicalTestPullback_source_operator h04 hz hs hW hp
  rw [hsource, n07a_divergenceOperator_unknown_germ (K.coefficients z m) hWv,
    hWv.self_of_nhds] at he
  exact he

/-- The negative canonical divergence is its actual two-derivative model. -/
theorem n07a_negative_canonical_divergence_on
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = false) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m)) :
    EqOn (divergenceOperator (K.coefficients z m) v)
      (fun p => mixedDerivative 2 0 v p - p.1 * mixedDerivative 0 2 v p)
      (canonicalOpen S K m) := by
  let A : SymmetricCoefficients := ⟨fun _ => 1, fun _ => 0, fun q => -q.1⟩
  have hopen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hvr := n07a_localPullback_radial_smooth hopen hv
  have hvt := n07a_localPullback_angular_smooth hopen hv
  intro p hp
  have hnear := hopen.mem_nhds hp
  have hsame : divergenceOperator (K.coefficients z m) v p = divergenceOperator A v p := by
    apply n07a_divergenceOperator_eq_of_germs
    · filter_upwards [hnear] with q hq
      exact (h04.2.1.2.2.2.1 z hz hs m hm q hq).1
    · filter_upwards [hnear] with q hq
      exact (h04.2.1.2.2.2.1 z hz hs m hm q hq).2.1
    · filter_upwards [hnear] with q hq
      exact (h04.2.1.2.2.2.1 z hz hs m hm q hq).2.2
  have hrr := (radialPartial_eq_mixedDerivative_on hopen hvr hp).trans
    (mixedDerivative_radialPartial hopen hv 1 0 hp)
  have htt := (angularPartial_eq_mixedDerivative_on hopen hvt hp).trans
    (mixedDerivative_angularPartial hopen hv 0 1 hp)
  have hneg : angularPartial (fun q : PolarPoint => -q.1) p = 0 := by
    simp [angularPartial, fderiv_fun_neg, fderiv_fst]
  rw [hsame]
  change radialPartial (fun q => 1 * radialPartial v q + 0 * angularPartial v q) p +
    angularPartial (fun q => 0 * radialPartial v q + -q.1 * angularPartial v q) p = _
  simp only [one_mul, zero_mul, add_zero, zero_add]
  rw [angularPartial_mul differentiableAt_fst.neg
    ((hvt.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)), hneg, hrr, htt]
  ring

/-- Reverse the already-proved normalized equation on an actual negative
piece. No new equation for the unknown is postulated. -/
theorem n07a_negative_normalEquation_divergence
    {E : Type*} (ζ : E → AnnularState S × ℝ) (e : E)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : ζ e ∈ stateNeighborhood S C base ε) (hs : stateSector S (ζ e).1)
    (m : ℕ) (hm : K.positive m = false) {v f : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (heq : EqOn (mixedDerivative 2 0 v)
      (n07aNormalRhs
        (fun i => n07aNormalCoefficientFamily
          (fun k z m => n07aPrincipalField K (ζ z) m k)
          (fun m => if K.positive m then -1 else 1) i e m) v f)
      (canonicalOpen S K m)) :
    EqOn (fun p => divergenceOperator (K.coefficients (ζ e) m) v p +
      K.potential (ζ e) m p * v p) f (canonicalOpen S K m) := by
  have hopen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  intro p hp
  have hnear := hopen.mem_nhds hp
  have ha : (K.coefficients (ζ e) m).a =ᶠ[𝓝 p] (fun _ => 1) := by
    filter_upwards [hnear] with q hq
    exact (h04.2.1.2.2.2.1 (ζ e) hz hs m hm q hq).1
  have hb : (K.coefficients (ζ e) m).b =ᶠ[𝓝 p] (fun _ => 0) := by
    filter_upwards [hnear] with q hq
    exact (h04.2.1.2.2.2.1 (ζ e) hz hs m hm q hq).2.1
  have hc : (K.coefficients (ζ e) m).c =ᶠ[𝓝 p] (fun q => -q.1) := by
    filter_upwards [hnear] with q hq
    exact (h04.2.1.2.2.2.1 (ζ e) hz hs m hm q hq).2.2
  have hρ : (fun q => ((K.coefficients (ζ e) m).a q)⁻¹) =ᶠ[𝓝 p] (fun _ => 1) := by
    filter_upwards [ha] with q hq
    rw [hq, inv_one]
  have hρr : mixedDerivative 1 0 (fun q => ((K.coefficients (ζ e) m).a q)⁻¹) p = 0 := by
    rw [n07a_mixedDerivative_eventuallyEq hρ 1 0]
    simp [mixedDerivative]
  have hbr : mixedDerivative 1 0 (K.coefficients (ζ e) m).b p = 0 := by
    rw [n07a_mixedDerivative_eventuallyEq hb 1 0]
    simp [mixedDerivative]
  have hbt : mixedDerivative 0 1 (K.coefficients (ζ e) m).b p = 0 := by
    rw [n07a_mixedDerivative_eventuallyEq hb 0 1]
    simp [mixedDerivative]
  have hct : mixedDerivative 0 1 (K.coefficients (ζ e) m).c p = 0 := by
    rw [n07a_mixedDerivative_eventuallyEq hc 0 1]
    simp [mixedDerivative]
  have hcoeff (i : Fin 6) :
      n07aNormalCoefficientFamily
        (fun k z m => n07aPrincipalField K (ζ z) m k)
        (fun m => if K.positive m then -1 else 1) i e m p =
      ![0, p.1, 0, 0, -K.potential (ζ e) m p, 1] i := by
    fin_cases i <;> simp [n07aNormalCoefficientFamily, n07aPrincipalField,
      ha.self_of_nhds, hb.self_of_nhds, hc.self_of_nhds, hρr, hbr, hbt, hct, hm]
  have hn := heq hp
  simp [n07aNormalRhs, hcoeff, n07aNormalShift, Fin.sum_univ_succ,
    spaces_mixedDerivative_zero] at hn
  rw [n07a_negative_canonical_divergence_on h04 hz hs m hm hv hp]
  linarith

/-- The true source factor is injective on the actual physical piece. -/
theorem n07a_canonicalSource_eqOn_physical
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → ℝ}
    (he : EqOn (canonicalSource S K z m f) (canonicalSource S K z m g)
      (canonicalOpen S K m)) :
    EqOn f g (physicalPieceOpen S K z m) := by
  have hchart := h04.1.charts z hz hs m
  intro p hp
  have h := he (hchart.1 hp)
  simp only [canonicalSource, hchart.2.2.1 p hp] at h
  have hpoint := hchart.2.2.2.2.2.2.2 p hp
  exact mul_left_cancel₀ hpoint.1.ne'
    ((div_left_inj' (abs_ne_zero.mpr hpoint.2.1)).mp h)

/-- The physical remainder source is common to all pieces of one unknown. -/
def n07aPhysicalRemainderSource
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ)
    (α : Fin 3 → ℝ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  f p - α 0 * divergenceOperator (L.coefficients z) (fun q => S.chiLeft q.1) p -
    α 1 * nuColumnField D S C z p - α 2 * (S.height (3 / 4 : ℝ)).decode S.psi p

/-- The common remainder source is smooth throughout the physical annulus,
including the artificial moving cuts. -/
theorem n07aPhysicalRemainderSource_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (α : Fin 3 → ℝ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    ContDiffOn ℝ ∞ (n07aPhysicalRemainderSource D S C L z α f) (annularOpen D) := by
  have hc := hcanonical.physicalCoefficients z hz hs
  have hχ : ContDiffOn ℝ ∞ (fun p : PolarPoint => S.chiLeft p.1) (annularOpen D) :=
    (hS.2.2.1.1.comp contDiff_fst).contDiffOn
  have hdiv := n07b_contDiffOn_divergenceOperator (isOpen_Ioo.prod isOpen_univ)
    hc.1 hc.2.1 hc.2.2.1 hχ
  have hν := n07a_nuColumnField_contDiffOn hS hT h01 hz hs
  have hψ : ContDiffOn ℝ ∞ ((S.height (3 / 4 : ℝ)).decode S.psi) (annularOpen D) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).1
  exact ((hf.sub (contDiffOn_const.mul hdiv)).sub
    (contDiffOn_const.mul hν)).sub (contDiffOn_const.mul hψ)

theorem n07a_sourceWithoutColumns_eq_remainderSource
    (α : CanonicalGeometry.Parameter S → S.Source → Fin 3 → ℝ)
    (e : CanonicalGeometry.Parameter S) (f : S.Source) (m : ℕ) :
    n07aCanonicalSourceWithoutColumns D S C L K α e f m =
      canonicalSource S K (liftSectorParameter S C e) m
        (n07aPhysicalRemainderSource D S C L (liftSectorParameter S C e) (α e f)
          ((S.height (3 / 4 : ℝ)).decode f.val)) := by
  funext p
  simp only [n07aCanonicalSourceWithoutColumns, n07aPhysicalRemainderSource,
    Fin.sum_univ_three, n07aScalarColumn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, canonicalSource]
  ring

/-- The closed height satisfies the original physical divergence equation
on its actual open negative piece. The normalized equation is precisely
the one in `N07aActualNormalFamilyData.equation`. -/
theorem n07a_closedPhysicalHeight_negative_equation
    (h04 : N04Properties D T S C L K base loss ε)
    (e : CanonicalGeometry.Parameter S)
    (hz : liftSectorParameter S C e ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C e).1)
    (m : ℕ) (hm : K.positive m = false) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi))
    (α : CanonicalGeometry.Parameter S → S.Source → Fin 3 → ℝ)
    (f : S.Source)
    (heq : EqOn (mixedDerivative 2 0 v)
      (n07aNormalRhs
        (fun i => n07aNormalCoefficientFamily
          (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
          (fun m => if K.positive m then -1 else 1) i e m) v
        (n07aCanonicalSourceWithoutColumns D S C L K α e f m))
      (canonicalOpen S K m))
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    EqOn (divergenceOperator (L.coefficients (liftSectorParameter S C e))
      (n07aClosedPhysicalHeight K (liftSectorParameter S C e) m J))
      (n07aPhysicalRemainderSource D S C L (liftSectorParameter S C e) (α e f)
        ((S.height (3 / 4 : ℝ)).decode f.val))
      (physicalPieceOpen S K (liftSectorParameter S C e) m) := by
  have hcanonical := n07a_negative_normalEquation_divergence
    (liftSectorParameter S C) e h04 hz hs m hm hv heq
  have hsource := n07a_physicalHeight_source_operator_on h04 hz hs m hv
    (fun p _ => hvp p)
  have hsame : EqOn
      (canonicalSource S K (liftSectorParameter S C e) m
        (divergenceOperator (L.coefficients (liftSectorParameter S C e))
          (n07aPhysicalHeightRepresentative K (liftSectorParameter S C e) m v)))
      (canonicalSource S K (liftSectorParameter S C e) m
        (n07aPhysicalRemainderSource D S C L (liftSectorParameter S C e) (α e f)
          ((S.height (3 / 4 : ℝ)).decode f.val))) (canonicalOpen S K m) := by
    intro p hp
    have h := (hsource hp).trans (by
      simpa only [hm, Bool.false_eq_true, ↓reduceIte, one_mul] using hcanonical hp)
    exact h.trans (congrFun (n07a_sourceWithoutColumns_eq_remainderSource α e f m) p)
  have hopen := (h04.1.domains (liftSectorParameter S C e) hz hs m).1
  have hphysical := n07a_canonicalSource_eqOn_physical h04 hz hs m hsame
  have hclosed := n07aClosedPhysicalHeight_eqOn h04 hz hs m J
  intro p hp
  have hnear : n07aClosedPhysicalHeight K (liftSectorParameter S C e) m J =ᶠ[𝓝 p]
      n07aPhysicalHeightRepresentative K (liftSectorParameter S C e) m v := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hclosed hq
  exact (n07a_divergenceOperator_unknown_germ
    (L.coefficients (liftSectorParameter S C e)) hnear).trans (hphysical hp)

end ContinuousFlexibility.Analysis
