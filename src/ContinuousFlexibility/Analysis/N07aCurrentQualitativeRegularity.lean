import ContinuousFlexibility.Analysis.N07aCanonicalSourceOpen
import ContinuousFlexibility.Analysis.N07aCurrentCanonicalEquation
import ContinuousFlexibility.Analysis.N07aCurrentPrincipalPositivity
import ContinuousFlexibility.Analysis.N07aCanonicalCoefficientDifference
import ContinuousFlexibility.Analysis.N07aAngularOpenRegularity
import ContinuousFlexibility.Analysis.N07aOpenClassicalNormal
import ContinuousFlexibility.Analysis.N07aSampleJetAlgebra

/-!
# All genuine canonical weak jets and the actual classical normal equation

The original weak relation, first-normal graph, and original source class
are retained throughout. The three scalar columns are subtracted as their
actual open coefficient representatives. The signed potential stays in
the divergence bootstrap, and the resulting six normal coefficients are
exactly the family used by the quantitative normal recurrence.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem constMul_toLp (c : ℝ) (χ : N07aCanonicalOpenCoefficient S K m) :
    (χ.constMul c).toLp = c • χ.toLp := by
  apply Lp.ext
  filter_upwards [(χ.constMul c).toLp_ae, χ.toLp_ae,
    Lp.coeFn_smul c χ.toLp] with p hc hχ hs
  exact hc.trans ((congrArg (c * ·) hχ.symm).trans hs.symm)

theorem smoothDecode_toLp_eqOn (χ : N07aCanonicalOpenCoefficient S K m)
    (hm : K.left m < K.right m) :
    EqOn (n07aCanonicalSmoothDecode hm ⟨χ.toLp, χ.toLp_normalRegular⟩)
      χ.value (canonicalOpen S K m) := by
  let f : n07aCanonicalSmoothSpace S K m := ⟨χ.toLp, χ.toLp_normalRegular⟩
  have hf := n07aCanonicalSmoothRepresentative_properties hm f
  exact n07a_canonical_periodicOn_eqOn_of_ae_eq hf.1.continuousOn χ.smooth.continuousOn
    (fun p _ => hf.2.1 p) χ.periodic (hf.2.2.1.trans χ.toLp_ae)

end N07aCanonicalOpenCoefficient

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The original source minus the actual cutoff, ν, and auxiliary columns. -/
def n07aCurrentCanonicalSourceValue
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (U : CanonicalUnknown S K) (f : PolarPoint → ℝ)
    (m : ℕ) : PolarPoint → ℝ := fun p =>
  canonicalSource S K z m f p - U.2.1 * n07aScalarColumn D S C L K z m 0 p -
    U.2.2.1 * n07aScalarColumn D S C L K z m 1 p -
      U.2.2.2 * n07aScalarColumn D S C L K z m 2 p

theorem n07aCurrentCanonicalSourceValue_eq_sum
    (z : AnnularState S × ℝ) (U : CanonicalUnknown S K) (f : PolarPoint → ℝ) (m : ℕ) :
    n07aCurrentCanonicalSourceValue D S C L K z U f m = fun p =>
      canonicalSource S K z m f p -
        ∑ i : Fin 3, ![U.2.1, U.2.2.1, U.2.2.2] i *
          n07aScalarColumn D S C L K z m i p := by
  funext p
  simp only [n07aCurrentCanonicalSourceValue, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

def n07aCurrentCanonicalSourceBar
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K)
    (χ : N07aCanonicalOpenCoefficient S K m) : N07aCanonicalOpenCoefficient S K m :=
  let col := n07aCurrentScalarOpenCoefficient href hcur z hz m hm
  ((χ.sub ((col 0).constMul U.2.1)).sub ((col 1).constMul U.2.2.1)).sub
    ((col 2).constMul U.2.2.2)

theorem n07aCurrentCanonicalSourceBar_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K)
    (χ : N07aCanonicalOpenCoefficient S K m) (f : PolarPoint → ℝ)
    (hχ : χ.value = canonicalSource S K (liftSectorParameter S C z) m f) :
    (n07aCurrentCanonicalSourceBar href hcur z hz m hm U χ).value =
      n07aCurrentCanonicalSourceValue D S C L K (liftSectorParameter S C z) U f m := by
  funext p
  exact congrArg (fun v : ℝ =>
    v - U.2.1 * n07aScalarColumn D S C L K (liftSectorParameter S C z) m 0 p -
      U.2.2.1 * n07aScalarColumn D S C L K (liftSectorParameter S C z) m 1 p -
        U.2.2.2 * n07aScalarColumn D S C L K (liftSectorParameter S C z) m 2 p)
    (congrFun hχ p)

theorem n07aCurrentCanonicalSourceBar_toLp
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K)
    (χ : N07aCanonicalOpenCoefficient S K m) :
    (n07aCurrentCanonicalSourceBar href hcur z hz m hm U χ).toLp =
      χ.toLp - U.2.1 • (n07aCurrentScalarOpenCoefficient href hcur z hz m hm 0).toLp -
        U.2.2.1 • (n07aCurrentScalarOpenCoefficient href hcur z hz m hm 1).toLp -
          U.2.2.2 • (n07aCurrentScalarOpenCoefficient href hcur z hz m hm 2).toLp := by
  simp only [n07aCurrentCanonicalSourceBar, N07aCanonicalOpenCoefficient.sub_toLp,
    N07aCanonicalOpenCoefficient.constMul_toLp]

theorem n07a_currentNormalCoefficients_eq
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 6) :
    n07aOpenNormalCoefficients
      (n07aCurrentOpenCoefficient href hcur z hz m hm 0)
      (n07aCurrentOpenCoefficient href hcur z hz m hm 1)
      (n07aCurrentOpenCoefficient href hcur z hz m hm 2)
      (n07aCurrentOpenCoefficient href hcur z hz m hm 3)
      ((n07aCurrentOpenCoefficient href hcur z hz m hm 4).constMul
        (if K.positive m then -1 else 1)) i =
      n07aNormalCoefficientFamily
        (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
        (fun m => if K.positive m then -1 else 1) i z m := by
  fin_cases i <;> rfl

private theorem n07aQualitative_sub_reorder {E : Type*} [AddCommGroup E]
    (f q a b c : E) : f - q - a - b - c = (f - a - b - c) - q := by
  abel

private theorem n07aQualitative_rhs_source_congr
    (A : Fin 6 → PolarPoint → ℝ) (u f g : PolarPoint → ℝ)
    (p : PolarPoint) (h : f p = g p) :
    n07aNormalRhs A u f p = n07aNormalRhs A u g p :=
  congrArg (fun t : ℝ => (∑ i : Fin 5, A i.castSucc p *
    mixedDerivative (n07aNormalShift i).1 (n07aNormalShift i).2 u p) + A 5 p * t) h

/-- The temporary source input is only the equality of its genuine L²
class with the source in the original relation. All higher regularity of
the same unknown is derived from its first-normal graph. -/
theorem n07a_currentCanonical_classical_of_sourceCoefficient
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z) U F)
    (χ : N07aCanonicalOpenCoefficient S K m) (hsource : χ.toLp = F m)
    (hpositive : ∀ p ∈ canonicalOpen S K m,
      0 < (K.coefficients (liftSectorParameter S C z) m).a p)
    (hfirst : N07aCanonicalNormalRegular S K m (U.1 m) 1) :
    ∃ hAll : ∀ n, N07aCanonicalNormalRegular S K m (U.1 m) n,
      EqOn (mixedDerivative 2 0 (n07aCanonicalSmoothDecode hm ⟨U.1 m, hAll⟩))
        (n07aNormalRhs
          (fun i => n07aNormalCoefficientFamily
            (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
            (fun m => if K.positive m then -1 else 1) i z m)
          (n07aCanonicalSmoothDecode hm ⟨U.1 m, hAll⟩)
          (n07aCurrentCanonicalSourceBar href hcur z hz m hm U χ).value)
        (canonicalOpen S K m) := by
  let coeff := n07aCurrentOpenCoefficient href hcur z hz m hm
  let a := coeff 0
  let b := coeff 1
  let c := coeff 2
  let ρ := coeff 3
  let q := (coeff 4).constMul (if K.positive m then -1 else 1)
  let χbar := n07aCurrentCanonicalSourceBar href hcur z hz m hm U χ
  have hinv : ∀ᵐ p ∂canonicalMeasure S K m, ρ.value p * a.value p = 1 := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    change ((K.coefficients (liftSectorParameter S C z) m).a p)⁻¹ *
      (K.coefficients (liftSectorParameter S C z) m).a p = 1
    exact inv_mul_cancel₀ (hpositive p hp).ne'
  let radialJet := hfirst 1 le_rfl 0
  let ur : CanonicalL2 S K m := radialJet.choose
  have hr : N07aWeakCanonicalMixedDerivative S K m (U.1 m) ur 1 0 :=
    radialJet.choose_spec
  let angularJet := hfirst 0 (Nat.zero_le 1) 1
  let uθ : CanonicalL2 S K m := angularJet.choose
  have hθ : N07aWeakCanonicalMixedDerivative S K m (U.1 m) uθ 0 1 :=
    angularJet.choose_spec
  have hur : N07aCanonicalNormalRegular S K m ur 0 :=
    hfirst.derivative (n := 0) (a := 1) (b := 0) hr
  have huθ : N07aCanonicalNormalRegular S K m uθ 0 :=
    (hfirst.mono (Nat.zero_le 1)).derivative (n := 0) (a := 0) (b := 1) hθ
  let radialAngularJet := hur 0 le_rfl 1
  let urθ : CanonicalL2 S K m := radialAngularJet.choose
  have hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1 :=
    radialAngularJet.choose_spec
  let angularSecondJet := huθ 0 le_rfl 1
  let uθθ : CanonicalL2 S K m := angularSecondJet.choose
  have hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1 :=
    angularSecondJet.choose_spec
  let column : Fin 3 → CanonicalL2 S K m :=
    fun i => (n07aCurrentScalarOpenCoefficient href hcur z hz m hm i).toLp
  have hbar : χbar.toLp = F m - U.2.1 • column 0 -
      U.2.2.1 • column 1 - U.2.2.2 • column 2 :=
    (n07aCurrentCanonicalSourceBar_toLp href hcur z hz m hm U χ).trans
      (congrArg (fun g : CanonicalL2 S K m =>
        g - U.2.1 • column 0 - U.2.2.1 • column 1 - U.2.2.2 • column 2) hsource)
  have hrhs : n07aCurrentCanonicalRhs href hcur z hz m hm U F =
      χbar.toLp - q.mul (U.1 m) :=
    (n07aQualitative_sub_reorder (F m) (q.mul (U.1 m)) (U.2.1 • column 0)
      (U.2.2.1 • column 1) (U.2.2.2 • column 2)).trans
        (congrArg (fun g : CanonicalL2 S K m => g - q.mul (U.1 m)) hbar.symm)
  have heq₀ := n07a_currentCanonical_distribution hab hS hrefState h04 href hcur
    z hz m hm hrel
  have heq : N07aCanonicalDistributionEquation S K m
      (K.coefficients (liftSectorParameter S C z) m) (U.1 m)
      (χbar.toLp - q.mul (U.1 m)) :=
    Eq.mp (congrArg (fun g : CanonicalL2 S K m =>
      N07aCanonicalDistributionEquation S K m
        (K.coefficients (liftSectorParameter S C z) m) (U.1 m) g) hrhs) heq₀
  have hflux : N07aCanonicalFluxEquation S K m (χbar.toLp - q.mul (U.1 m))
      (a.mul ur + b.mul uθ) (b.mul ur + c.mul uθ) :=
    n07a_openDistribution_flux a b c hr hθ heq
  have hAll : ∀ n, N07aCanonicalNormalRegular S K m (U.1 m) n :=
    n07a_openWeak_divergenceBootstrap a b c ρ q hinv hr hθ hrθ hθθ hfirst
      χbar.toLp_normalRegular hflux
  let u : n07aCanonicalSmoothSpace S K m := ⟨U.1 m, hAll⟩
  let fbar : n07aCanonicalSmoothSpace S K m := ⟨χbar.toLp, χbar.toLp_normalRegular⟩
  have hc := n07a_openWeak_classicalNormal hm a b c ρ q hinv u fbar
    hr hθ hrθ hθθ hflux
  have hfe := χbar.smoothDecode_toLp_eqOn hm
  let A : Fin 6 → PolarPoint → ℝ := fun i => n07aNormalCoefficientFamily
    (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
    (fun m => if K.positive m then -1 else 1) i z m
  have hcoeff : n07aOpenNormalCoefficients a b c ρ q = A := by
    funext i
    exact n07a_currentNormalCoefficients_eq href hcur z hz m hm i
  refine ⟨hAll, ?_⟩
  intro p hp
  have hcoeffp := congrArg (fun B : Fin 6 → PolarPoint → ℝ =>
    n07aNormalRhs B (n07aCanonicalSmoothDecode hm u)
      (n07aCanonicalSmoothDecode hm fbar) p) hcoeff
  exact (hc hp).trans (hcoeffp.trans (n07aQualitative_rhs_source_congr A
    (n07aCanonicalSmoothDecode hm u) (n07aCanonicalSmoothDecode hm fbar)
    χbar.value p (hfe hp)))

/-- On one justified smaller neighborhood, the only inputs concerning
the solution are its original distribution relation, its original source
class, and its first-normal weak graph. The conclusion retains the same
unknown and all three actual scalar columns. -/
theorem n07a_currentCanonical_qualitative_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ U : CanonicalUnknown S K, ∀ F : CanonicalSequence S K, ∀ f : S.Source,
          PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z) U F →
          (∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K (liftSectorParameter S C z) m
              ((S.height (3 / 4 : ℝ)).decode f.val)) →
          (∀ m, N07aCanonicalNormalRegular S K m (U.1 m) 1) →
          ∀ m, ∃ hAll : ∀ n, N07aCanonicalNormalRegular S K m (U.1 m) n,
            EqOn (mixedDerivative 2 0
              (n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1 ⟨U.1 m, hAll⟩))
              (n07aNormalRhs
                (fun i => n07aNormalCoefficientFamily
                  (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
                  (fun m => if K.positive m then -1 else 1) i z m)
                (n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1 ⟨U.1 m, hAll⟩)
                (n07aCurrentCanonicalSourceValue D S C L K (liftSectorParameter S C z)
                  U ((S.height (3 / 4 : ℝ)).decode f.val) m))
              (canonicalOpen S K m) := by
  have hs := n07a_exists_canonicalSourceOpen_neighborhood hD hT hS hε
    hrefState h04 href hcur
  let bs : ℕ := hs.choose
  let es : ℝ := hs.choose_spec.2.choose
  have hsb := hs.choose_spec.2.choose_spec
  have hp := n07a_currentPrincipal_positive_neighborhood hD hT href hprincipal hcur hε
    (fun m => (h04.1.referenceBounds m).2.1)
  let bp : ℕ := hp.choose
  let ep : ℝ := hp.choose_spec.2.choose
  have hpb := hp.choose_spec.2.choose_spec
  let base' : ℕ := max bs bp
  let ε' : ℝ := min es ep
  have hbase : base ≤ base' := hs.choose_spec.1.trans (le_max_left bs bp)
  have he : ε' ≤ ε := (min_le_left es ep).trans hsb.2.1
  refine ⟨base', hbase, ε', lt_min hsb.1 hpb.1, he, ?_⟩
  intro z hz U F f hrel hF hfirst m
  have hzs : z ∈ sectorNeighborhood S bs es es :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left bs bp) (min_le_left es ep) hz
  have hzp : z ∈ sectorNeighborhood S bp ep ep :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_right bs bp) (min_le_right es ep) hz
  have hz₀ : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) hbase he hz
  let source := hsb.2.2 z hzs f.val m
  let χ : N07aCanonicalOpenCoefficient S K m := source.choose
  have hχ : χ.value = canonicalSource S K (liftSectorParameter S C z) m
      ((S.height (3 / 4 : ℝ)).decode f.val) := source.choose_spec
  have hsource : χ.toLp = F m := by
    apply Lp.ext
    have hχae : χ.value =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode f.val) :=
      Filter.Eventually.of_forall (fun p => congrFun hχ p)
    exact (χ.toLp_ae.trans hχae).trans (hF m).symm
  have hregular := n07a_currentCanonical_classical_of_sourceCoefficient
    hD.choose_spec.1.2.1.le hS hrefState h04 href hcur z hz₀ m
      (h04.1.referenceBounds m).2.1 hrel χ hsource (hpb.2.2 z hzp m) (hfirst m)
  let hAll : ∀ n, N07aCanonicalNormalRegular S K m (U.1 m) n := hregular.choose
  refine ⟨hAll, ?_⟩
  have hvalue := n07aCurrentCanonicalSourceBar_value href hcur z hz₀ m
    (h04.1.referenceBounds m).2.1 U χ _ hχ
  intro p hp
  exact (hregular.choose_spec hp).trans (congrArg (fun g : PolarPoint → ℝ =>
    n07aNormalRhs
      (fun i => n07aNormalCoefficientFamily
        (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
        (fun m => if K.positive m then -1 else 1) i z m)
      (n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1 ⟨U.1 m, hAll⟩) g p) hvalue)

end ContinuousFlexibility.Analysis
