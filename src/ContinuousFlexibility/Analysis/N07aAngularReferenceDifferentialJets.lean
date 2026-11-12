import ContinuousFlexibility.Analysis.N07aAngularFixedJetOperations
import ContinuousFlexibility.Analysis.N07aAngularReferenceSource
import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms
import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# The actual reference differential preserves every sampled decay order

The three radial coefficients have uniformly bounded spatial jets on the
closed physical core. Differentiating the transported remainder and
forming its displayed radial differential therefore retain H^(3/4) and
every chosen material power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem n07a_radialField_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hpieces : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {J : Set ℝ} (hJ : IsOpen J) (hcore : Icc D.a D.b ⊆ J)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f J) :
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) (fun _ => 1)
      (fun _ p => f p.1) := by
  have houter : N07aAngularFixedJetEnvelope T K (fun _ => radialCore D)
      (fun _ => 1) (fun _ => f) := by
    apply N07aAngularFixedJetEnvelope.of_uniform_jets hD hT
    intro n
    have hc := (hf.continuousOn_iteratedFDerivWithin (m := n) (by simp) hJ.uniqueDiffOn)
    obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image (hc.norm.mono hcore)
    refine ⟨max 0 A, le_max_left _ _, fun m r hr => ?_⟩
    have hrJ := hcore (Ioo_subset_Icc_self hr)
    rw [← iteratedFDerivWithin_of_isOpen n hJ hrJ]
    exact (hA ⟨r, Ioo_subset_Icc_self hr, rfl⟩).trans (le_max_right _ _)
  apply houter.comp hD hT (fun _ => zero_le_one)
    (fun m p hp => hpieces m hp.1)
    (fun m p hp => hf.contDiffAt (hJ.mem_nhds (hcore (Ioo_subset_Icc_self (hpieces m hp.1)))))
    (fun _ _ _ => contDiffAt_fst)
  intro n hn
  refine ⟨fun _ => 1, N07aSampleSubpower.const hD hT 1, fun _ => zero_le_one,
    fun m p hp => ?_⟩
  exact (n07a_iteratedFDeriv_linear_norm_le (ContinuousLinearMap.fst ℝ ℝ ℝ) hn p).trans
    (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)

def n07aReferenceRadialDifferentialCoefficient (D : ReferenceData) (i : Fin 3) : ℝ → ℝ :=
  ![deriv D.w, D.w, fun r => deriv D.w r / r] i

theorem n07a_referenceRadialDifferentialCoefficient_smooth
    (hgeom : RadialProfileGeometry D) (i : Fin 3) :
    ContDiffOn ℝ ∞ (n07aReferenceRadialDifferentialCoefficient D i) (Ioi 0) := by
  have hw := hgeom.2.2.1.1
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  fin_cases i
  · exact hdw.contDiffOn
  · exact hw.contDiffOn
  · exact hdw.contDiffOn.div contDiffOn_id (fun r hr => ne_of_gt hr)

theorem n07a_referenceDifferentialCoefficient_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hpieces : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    (i : Fin 3) :
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) (fun _ => 1)
      (fun _ p => n07aReferenceRadialDifferentialCoefficient D i p.1) :=
  n07a_radialField_fixedJetEnvelope hD hT hpieces isOpen_Ioi
    (fun r hr => hD.choose_spec.1.1.trans_le hr.1)
    (n07a_referenceRadialDifferentialCoefficient_smooth hD.choose_spec.1 i)

theorem n07a_referenceDifferential_contDiffOn
    (hgeom : RadialProfileGeometry D) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (n07aReferenceDifferential D f) U := by
  have hrs := scalar_contDiffOn_radialPartial hU hf
  have hrrs := scalar_contDiffOn_radialPartial hU hrs
  have htts := scalar_contDiffOn_angularPartial hU (scalar_contDiffOn_angularPartial hU hf)
  have hcs (i : Fin 3) : ContDiffOn ℝ ∞
      (fun p : PolarPoint => n07aReferenceRadialDifferentialCoefficient D i p.1) U :=
    (n07a_referenceRadialDifferentialCoefficient_smooth hgeom i).comp
      contDiffOn_fst (fun p hp => hgeom.1.trans (hcore hp).1.1)
  exact ((hcs 0 |>.mul hrs).add (hcs 1 |>.mul hrrs)).add (hcs 2 |>.mul htts)

theorem n07a_referenceDifferential_fixedJetEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hpieces : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {f : ℕ → PolarPoint → ℝ}
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (referencePhysicalPieceOpen S K m))
    (hf : N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) w f) :
    N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K) w
      (fun m => n07aReferenceDifferential D (f m)) := by
  let W := referencePhysicalPieceOpen S K
  have hW : ∀ m, IsOpen (W m) := fun _ => isOpen_Ioo.prod isOpen_univ
  have hrs (m : ℕ) := scalar_contDiffOn_radialPartial (hW m) (hfs m)
  have hrrs (m : ℕ) := scalar_contDiffOn_radialPartial (hW m) (hrs m)
  have hts (m : ℕ) := scalar_contDiffOn_angularPartial (hW m) (hfs m)
  have htts (m : ℕ) := scalar_contDiffOn_angularPartial (hW m) (hts m)
  have hr : N07aAngularFixedJetEnvelope T K W w (fun m => radialPartial (f m)) :=
    hf.directional hD hT hW hfs (1, 0)
  have hrr : N07aAngularFixedJetEnvelope T K W w
      (fun m => radialPartial (radialPartial (f m))) :=
    hr.directional hD hT hW hrs (1, 0)
  have ht : N07aAngularFixedJetEnvelope T K W w (fun m => angularPartial (f m)) :=
    hf.directional hD hT hW hfs (0, 1)
  have htt : N07aAngularFixedJetEnvelope T K W w
      (fun m => angularPartial (angularPartial (f m))) :=
    ht.directional hD hT hW hts (0, 1)
  have hcs (i : Fin 3) (m : ℕ) : ContDiffOn ℝ ∞
      (fun p : PolarPoint => n07aReferenceRadialDifferentialCoefficient D i p.1) (W m) :=
    (n07a_referenceRadialDifferentialCoefficient_smooth hD.choose_spec.1 i).comp
      contDiffOn_fst (fun p hp => hD.choose_spec.1.1.trans (hpieces m hp.1).1)
  have hcoef := n07a_referenceDifferentialCoefficient_fixedJetEnvelope hD hT hpieces
  have h₀ : N07aAngularFixedJetEnvelope T K W w
      (fun m p => deriv D.w p.1 * radialPartial (f m) p) := by
    simpa only [one_mul, n07aReferenceRadialDifferentialCoefficient,
      Matrix.cons_val_zero] using
      N07aAngularFixedJetEnvelope.mul hD hT hW (hcs 0) hrs (hcoef 0) hr
        (fun _ => zero_le_one) hw
  have h₁ : N07aAngularFixedJetEnvelope T K W w
      (fun m p => D.w p.1 * radialPartial (radialPartial (f m)) p) := by
    simpa only [one_mul, n07aReferenceRadialDifferentialCoefficient,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      N07aAngularFixedJetEnvelope.mul hD hT hW (hcs 1) hrrs (hcoef 1) hrr
        (fun _ => zero_le_one) hw
  have h₂ : N07aAngularFixedJetEnvelope T K W w
      (fun m p => deriv D.w p.1 / p.1 * angularPartial (angularPartial (f m)) p) := by
    simpa only [one_mul, n07aReferenceRadialDifferentialCoefficient,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
      N07aAngularFixedJetEnvelope.mul hD hT hW (hcs 2) htts (hcoef 2) htt
        (fun _ => zero_le_one) hw
  exact (h₀.add hD hT hW (fun m => (hcs 0 m).mul (hrs m))
    (fun m => (hcs 1 m).mul (hrrs m)) h₁).add hD hT hW
      (fun m => ((hcs 0 m).mul (hrs m)).add ((hcs 1 m).mul (hrrs m)))
      (fun m => (hcs 2 m).mul (htts m)) h₂

end ContinuousFlexibility.Analysis
