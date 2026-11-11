import ContinuousFlexibility.Analysis.N05CanonicalTests

/-!
# Lifting actual canonical source jets into the prescribed volume model

The input consists of actual functions, their L² membership, the reflection
identity of their zeroth coordinate, their distributional angular derivative
identities, and the square summability of their weighted jets. The construction
uses the levels and forget map of the given `IsVolumeModel`; it does not select
a replacement source space or a different completion.

For the N07b application the zeroth coordinate is `canonicalSource S K z m f`
and coordinate `j` is its actual `j`-th angular derivative. Geometry must still
prove their L² membership, reflection and weak derivative identities, and a
uniform bound on the displayed sum of weighted squares. In particular, this
module does not assume those analytic inputs in the final blueprint statement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {γ t : ℝ} {s : ℕ}

/-- The factor prescribed by the actual model's forget map. -/
def n07bCanonicalSourceFactor (T : MaterialData) (K : CanonicalData S)
    (γ t : ℝ) (m : ℕ) : ℝ :=
  T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ

theorem n07bCanonicalSourceFactor_ne_zero
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (γ t : ℝ) (m : ℕ) : n07bCanonicalSourceFactor T K γ t m ≠ 0 :=
  (mul_pos (Real.rpow_pos_of_pos (hM (K.cell m)) (-t))
    (Real.rpow_pos_of_pos (hH (K.cell m)) γ)).ne'

variable {g : ∀ m : ℕ, Fin (s + 1) → PolarPoint → ℝ}
  (hg : ∀ m j, MemLp (g m j) 2 (canonicalMeasure S K m))

/-- The actual weighted L² coordinate, with the inverse of the forget factor. -/
def n07bCanonicalWeightedJet (γ t : ℝ) (m : ℕ) (j : Fin (s + 1)) :
    CanonicalL2 S K m :=
  (n07bCanonicalSourceFactor T K γ t m)⁻¹ • (hg m j).toLp (g m j)

theorem n07bCanonicalWeightedJet_ae (γ t : ℝ) (m : ℕ) (j : Fin (s + 1)) :
    (n07bCanonicalWeightedJet (T := T) hg γ t m j : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        fun p => (n07bCanonicalSourceFactor T K γ t m)⁻¹ * g m j p := by
  filter_upwards [Lp.coeFn_smul (n07bCanonicalSourceFactor T K γ t m)⁻¹
    ((hg m j).toLp (g m j)), MemLp.coeFn_toLp (hg m j)] with p hp hgp
  change n07bCanonicalWeightedJet (T := T) hg γ t m j p = _
  exact hp.trans (congrArg ((n07bCanonicalSourceFactor T K γ t m)⁻¹ * ·) hgp)

/-- One piece's finite Hilbert product of the weighted angular jets. -/
def n07bCanonicalWeightedRow (γ t : ℝ) (m : ℕ) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun j => n07bCanonicalWeightedJet (T := T) hg γ t m j)

theorem n07bCanonicalWeightedRow_apply (γ t : ℝ) (m : ℕ) (j : Fin (s + 1)) :
    n07bCanonicalWeightedRow (T := T) hg γ t m j =
      n07bCanonicalWeightedJet (T := T) hg γ t m j :=
  PiLp.toLp_apply 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)
    (fun k => n07bCanonicalWeightedJet (T := T) hg γ t m k) j

/-- The actual weighted square energy of one canonical piece. -/
def n07bCanonicalJetEnergy (γ t : ℝ) (m : ℕ) : ℝ :=
  ∑ j : Fin (s + 1), ‖n07bCanonicalWeightedJet (T := T) hg γ t m j‖ ^ 2

theorem n07bCanonicalWeightedRow_norm_sq (γ t : ℝ) (m : ℕ) :
    ‖n07bCanonicalWeightedRow (T := T) hg γ t m‖ ^ 2 =
      n07bCanonicalJetEnergy (T := T) hg γ t m := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [n07bCanonicalWeightedRow_apply, n07bCanonicalJetEnergy]

private theorem n07b_rpow_two (x : ℝ) :
    x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by
  norm_cast

/-- The actual square-summable family, before imposing the weak jet equations. -/
def n07bCanonicalSourceJets (γ t : ℝ)
    (hsum : Summable (n07bCanonicalJetEnergy (T := T) hg γ t)) :
    CanonicalVolumeJets S K s :=
  ⟨n07bCanonicalWeightedRow (T := T) hg γ t, memℓp_gen (by
    simpa only [n07b_rpow_two, n07bCanonicalWeightedRow_norm_sq] using hsum)⟩

theorem n07bCanonicalSourceJets_apply (γ t : ℝ)
    (hsum : Summable (n07bCanonicalJetEnergy (T := T) hg γ t))
    (m : ℕ) (j : Fin (s + 1)) :
    n07bCanonicalSourceJets (T := T) hg γ t hsum m j =
      n07bCanonicalWeightedJet (T := T) hg γ t m j :=
  n07bCanonicalWeightedRow_apply hg γ t m j

theorem n07bCanonicalSourceJets_norm_sq (γ t : ℝ)
    (hsum : Summable (n07bCanonicalJetEnergy (T := T) hg γ t)) :
    ‖n07bCanonicalSourceJets (T := T) hg γ t hsum‖ ^ 2 =
      ∑' m, n07bCanonicalJetEnergy (T := T) hg γ t m := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (n07bCanonicalSourceJets (T := T) hg γ t hsum)
  simp only [n07b_rpow_two] at h
  refine h.trans (tsum_congr fun m => ?_)
  exact n07bCanonicalWeightedRow_norm_sq hg γ t m

private theorem n07bCanonicalWeightedJet_reflection (γ t : ℝ) (m : ℕ)
    (href : (fun p : PolarPoint => g m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m 0) :
    (fun p : PolarPoint =>
      n07bCanonicalWeightedJet (T := T) hg γ t m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m]
        (n07bCanonicalWeightedJet (T := T) hg γ t m 0 : PolarPoint → ℝ) := by
  have he := n07bCanonicalWeightedJet_ae (T := T) hg γ t m 0
  have her := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [he, her, href] with p hp hpr hr
  change n07bCanonicalWeightedJet (T := T) hg γ t m 0 (p.1, Real.pi - p.2) =
    (n07bCanonicalSourceFactor T K γ t m)⁻¹ * g m 0 (p.1, Real.pi - p.2) at hpr
  exact hpr.trans ((congrArg ((n07bCanonicalSourceFactor T K γ t m)⁻¹ * ·) hr).trans hp.symm)

private theorem n07bCanonicalWeightedJet_weak (γ t : ℝ) (m : ℕ)
    (j : Fin (s + 1))
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, g m j p * φ p ∂canonicalMeasure S K m) =
        (-1 : ℝ) ^ j.val *
          ∫ p, g m 0 p * mixedDerivative 0 j.val φ p ∂canonicalMeasure S K m) :
    WeakCanonicalAngularDerivative S K m
      (n07bCanonicalWeightedJet (T := T) hg γ t m 0)
      (n07bCanonicalWeightedJet (T := T) hg γ t m j) j.val := by
  intro φ hφ
  have hpair (k : Fin (s + 1)) (ψ : PolarPoint → ℝ) :
      (∫ p, n07bCanonicalWeightedJet (T := T) hg γ t m k p * ψ p
        ∂canonicalMeasure S K m) =
      (n07bCanonicalSourceFactor T K γ t m)⁻¹ *
        ∫ p, g m k p * ψ p ∂canonicalMeasure S K m := by
    calc
      (∫ p, n07bCanonicalWeightedJet (T := T) hg γ t m k p * ψ p
          ∂canonicalMeasure S K m) =
        ∫ p, (n07bCanonicalSourceFactor T K γ t m)⁻¹ * (g m k p * ψ p)
          ∂canonicalMeasure S K m := by
            apply integral_congr_ae
            filter_upwards [n07bCanonicalWeightedJet_ae (T := T) hg γ t m k] with p hp
            rw [hp, mul_assoc]
      _ = _ := by rw [integral_const_mul]
  rw [hpair j φ, hpair 0 (mixedDerivative 0 j.val φ), hweak φ hφ]
  ring

theorem n07bCanonicalSourceJets_mem_graph (γ t : ℝ)
    (href : ∀ m, (fun p : PolarPoint => g m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m 0)
    (hweak : ∀ m j φ, CanonicalTest S K m φ →
      (∫ p, g m j p * φ p ∂canonicalMeasure S K m) =
        (-1 : ℝ) ^ j.val *
          ∫ p, g m 0 p * mixedDerivative 0 j.val φ p ∂canonicalMeasure S K m)
    (hsum : Summable (n07bCanonicalJetEnergy (T := T) hg γ t)) :
    n07bCanonicalSourceJets (T := T) hg γ t hsum ∈ canonicalVolumeGraph S K s := by
  constructor
  · intro m
    simpa only [n07bCanonicalSourceJets_apply] using
      n07bCanonicalWeightedJet_reflection hg γ t m (href m)
  · intro m j
    simpa only [n07bCanonicalSourceJets_apply] using
      n07bCanonicalWeightedJet_weak hg γ t m j (hweak m j)

variable (hV : IsVolumeModel T S K V)
  (href : ∀ m, (fun p : PolarPoint => g m 0 (p.1, Real.pi - p.2))
    =ᵐ[canonicalMeasure S K m] g m 0)
  (hweak : ∀ m j φ, CanonicalTest S K m φ →
    (∫ p, g m j p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j.val *
        ∫ p, g m 0 p * mixedDerivative 0 j.val φ p ∂canonicalMeasure S K m)
  (hsum : Summable (n07bCanonicalJetEnergy (T := T) hg γ t))

/-- Lift the actual weighted jets into the already chosen model level. -/
def n07bCanonicalSourceLift : V.level γ t s :=
  ⟨n07bCanonicalSourceJets (T := T) hg γ t hsum, by
    rw [hV.1 γ t s]
    exact n07bCanonicalSourceJets_mem_graph hg γ t href hweak hsum⟩

theorem n07bCanonicalSourceLift_coordinate (m : ℕ) (j : Fin (s + 1)) :
    (n07bCanonicalSourceLift hg hV href hweak hsum).val m j =
      (n07bCanonicalSourceFactor T K γ t m)⁻¹ • (hg m j).toLp (g m j) :=
  n07bCanonicalSourceJets_apply hg γ t hsum m j

theorem n07bCanonicalSourceLift_forget
    (hw : ∀ m, n07bCanonicalSourceFactor T K γ t m ≠ 0) (m : ℕ) :
    V.forget γ t s (n07bCanonicalSourceLift hg hV href hweak hsum) m =
      (hg m 0).toLp (g m 0) := by
  rw [hV.2.2.2 γ t s, n07bCanonicalSourceLift_coordinate]
  change n07bCanonicalSourceFactor T K γ t m •
    ((n07bCanonicalSourceFactor T K γ t m)⁻¹ • (hg m 0).toLp (g m 0)) = _
  rw [smul_smul, mul_inv_cancel₀ (hw m), one_smul]

theorem n07bCanonicalSourceLift_forget_ae
    (hw : ∀ m, n07bCanonicalSourceFactor T K γ t m ≠ 0) (m : ℕ) :
    (V.forget γ t s (n07bCanonicalSourceLift hg hV href hweak hsum) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] g m 0 := by
  rw [n07bCanonicalSourceLift_forget hg hV href hweak hsum hw m]
  exact MemLp.coeFn_toLp (hg m 0)

theorem n07bCanonicalSourceLift_norm_sq :
    ‖n07bCanonicalSourceLift hg hV href hweak hsum‖ ^ 2 =
      ∑' m, n07bCanonicalJetEnergy (T := T) hg γ t m := by
  calc
    ‖n07bCanonicalSourceLift hg hV href hweak hsum‖ ^ 2 =
        ‖(n07bCanonicalSourceLift hg hV href hweak hsum).val‖ ^ 2 :=
      congrArg (fun r : ℝ => r ^ 2) (Submodule.norm_coe _).symm
    _ = _ := n07bCanonicalSourceJets_norm_sq hg γ t hsum

theorem n07bCanonicalSourceLift_norm_le {R : ℝ} (hR : 0 ≤ R)
    (hbound : (∑' m, n07bCanonicalJetEnergy (T := T) hg γ t m) ≤ R ^ 2) :
    ‖n07bCanonicalSourceLift hg hV href hweak hsum‖ ≤ R := by
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [n07bCanonicalSourceLift_norm_sq hg hV href hweak hsum]
  exact hbound

/-- The source and norm portion of the N07b bridge for actual geometric jets.
The remaining proof obligation is to establish `hg`, `href`, `hweak`, `hsum`
and `hbound` uniformly from the physical geometry. -/
theorem n07b_exists_canonicalSourceLift
    (hw : ∀ m, n07bCanonicalSourceFactor T K γ t m ≠ 0)
    (z : AnnularState S × ℝ) (f : PolarPoint → ℝ)
    (hzero : ∀ m, g m 0 = canonicalSource S K z m f)
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : (∑' m, n07bCanonicalJetEnergy (T := T) hg γ t m) ≤ R ^ 2) :
    ∃ F : V.level γ t s, ‖F‖ ≤ R ∧
      ∀ m, (V.forget γ t s F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m f := by
  refine ⟨n07bCanonicalSourceLift hg hV href hweak hsum,
    n07bCanonicalSourceLift_norm_le hg hV href hweak hsum hR hbound, ?_⟩
  intro m
  rw [← hzero m]
  exact n07bCanonicalSourceLift_forget_ae hg hV href hweak hsum hw m

end ContinuousFlexibility.Statements
