module

public import ContinuousFlexibility.Analysis.N06VolumeFourierCutoff

/-!
# Linearity of the actual canonical Fourier cutoff

The cutoff is linear on the original L2 classes, not merely on selected
representatives. Its action on the original volume level commutes with
forget, including the original material factors. Consequently cutting a
volume member retains membership in the same weighted level.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped BigOperators Topology ENNReal

set_option backward.isDefEq.respectTransparency false

theorem n06CircleFourierCut_add {f g : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (hg : MemLp g 2 angleMeasure)
    (s : Finset ℤ) (θ : ℝ) :
    n06CircleFourierCut s (f + g) θ =
      n06CircleFourierCut s f θ + n06CircleFourierCut s g θ := by
  simp only [n06CircleFourierCut, circleFourierPolynomial,
    circleFourierCoeff_add hf hg, add_mul, Finset.sum_add_distrib, Complex.add_re]

theorem n06CircleFourierCut_smul (f : ℝ → ℝ) (c : ℝ)
    (s : Finset ℤ) (θ : ℝ) :
    n06CircleFourierCut s (c • f) θ = c * n06CircleFourierCut s f θ := by
  simp only [n06CircleFourierCut, circleFourierPolynomial, circleFourierCoeff_smul,
    Complex.real_smul, mul_assoc, ← Finset.mul_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Almost-everywhere equality of the original cylinder fields determines
every finite polynomial almost everywhere in the same product measure. -/
theorem n06CylinderFourierCut_congr_ae {μ : Measure ℝ} [SFinite μ]
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[μ.prod angleMeasure] g) (s : Finset ℤ) :
    n06CylinderFourierCut s f =ᵐ[μ.prod angleMeasure] n06CylinderFourierCut s g := by
  have hc : ∀ᵐ r ∂μ,
      circleFourierCoeff (fun θ => f (r, θ)) =
        circleFourierCoeff (fun θ => g (r, θ)) :=
    (Measure.ae_ae_of_ae_prod hfg).mono (fun _ hr => circleFourierCoeff_congr_ae hr)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hc] with p hp
  simp only [n06CylinderFourierCut, n06CircleFourierCut, hp]

theorem n06CylinderFourierCut_add_ae {μ : Measure ℝ} [SFinite μ]
    {f g : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) (hg : MemLp g 2 (μ.prod angleMeasure))
    (s : Finset ℤ) :
    n06CylinderFourierCut s (f + g) =ᵐ[μ.prod angleMeasure]
      (fun p => n06CylinderFourierCut s f p + n06CylinderFourierCut s g p) := by
  have hs : ∀ᵐ r ∂μ, ∀ θ,
      n06CylinderFourierCut s (f + g) (r, θ) =
        n06CylinderFourierCut s f (r, θ) + n06CylinderFourierCut s g (r, θ) := by
    filter_upwards [r11b_memLp_product_sections hf, r11b_memLp_product_sections hg]
      with r hr hg'
    exact fun θ => n06CircleFourierCut_add hr hg' s θ
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs] with p hp
  exact hp p.2

theorem n06CylinderFourierCut_smul (f : PolarPoint → ℝ) (c : ℝ)
    (s : Finset ℤ) (p : PolarPoint) :
    n06CylinderFourierCut s (c • f) p = c * n06CylinderFourierCut s f p :=
  n06CircleFourierCut_smul (fun θ => f (p.1, θ)) c s p.2

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n06_canonicalFourierCut_congr_ae {m : ℕ}
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[canonicalMeasure S K m] g) (s : Finset ℤ) :
    n06CylinderFourierCut s f =ᵐ[canonicalMeasure S K m] n06CylinderFourierCut s g := by
  rw [n06_canonicalMeasure_eq_radial_prod] at hfg ⊢
  exact n06CylinderFourierCut_congr_ae hfg s

theorem n06CanonicalFourierCutL2_add {m : ℕ}
    (N : ℕ) (U W : CanonicalL2 S K m) :
    n06CanonicalFourierCutL2 N (U + W) =
      n06CanonicalFourierCutL2 N U + n06CanonicalFourierCutL2 N W := by
  have hrep := n06_canonicalFourierCut_congr_ae (S := S) (K := K)
    (Lp.coeFn_add U W) (n06FourierCutoff N)
  have hadd : n06CylinderFourierCut (n06FourierCutoff N)
      ((U : PolarPoint → ℝ) + (W : PolarPoint → ℝ)) =ᵐ[canonicalMeasure S K m]
      (fun p => n06CylinderFourierCut (n06FourierCutoff N) U p +
        n06CylinderFourierCut (n06FourierCutoff N) W p) := by
    exact (congrArg (fun μ : Measure PolarPoint =>
      n06CylinderFourierCut (n06FourierCutoff N)
        ((U : PolarPoint → ℝ) + (W : PolarPoint → ℝ)) =ᵐ[μ]
        (fun p => n06CylinderFourierCut (n06FourierCutoff N) U p +
          n06CylinderFourierCut (n06FourierCutoff N) W p))
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr
        (n06CylinderFourierCut_add_ae (n06_canonicalL2_memLp_prod U)
          (n06_canonicalL2_memLp_prod W) (n06FourierCutoff N))
  apply Lp.ext
  filter_upwards [n06CanonicalFourierCutL2_coe_ae N (U + W),
    n06CanonicalFourierCutL2_coe_ae N U, n06CanonicalFourierCutL2_coe_ae N W,
    Lp.coeFn_add (n06CanonicalFourierCutL2 N U) (n06CanonicalFourierCutL2 N W),
    hrep, hadd] with p hsum hu hw hLp heq ha
  simp only [Pi.add_apply] at hLp
  rw [hsum, heq, ha, hLp, hu, hw]

theorem n06CanonicalFourierCutL2_smul {m : ℕ}
    (N : ℕ) (c : ℝ) (U : CanonicalL2 S K m) :
    n06CanonicalFourierCutL2 N (c • U) = c • n06CanonicalFourierCutL2 N U := by
  have hrep := n06_canonicalFourierCut_congr_ae (S := S) (K := K)
    (Lp.coeFn_smul c U) (n06FourierCutoff N)
  apply Lp.ext
  filter_upwards [n06CanonicalFourierCutL2_coe_ae N (c • U),
    n06CanonicalFourierCutL2_coe_ae N U,
    Lp.coeFn_smul c (n06CanonicalFourierCutL2 N U), hrep]
    with p hcut hu hsm hrep'
  simp only [Pi.smul_apply, smul_eq_mul] at hsm
  rw [hcut, hrep', n06CylinderFourierCut_smul, hsm, hu]

/-- The actual piece cutoff as a contraction on its original Hilbert space. -/
def n06CanonicalFourierCutMap {m : ℕ} (N : ℕ) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  ({ toFun := n06CanonicalFourierCutL2 N
     map_add' := n06CanonicalFourierCutL2_add N
     map_smul' := fun c U => n06CanonicalFourierCutL2_smul N c U } :
      CanonicalL2 S K m →ₗ[ℝ] CanonicalL2 S K m).mkContinuous 1
        (fun U => by
          change ‖n06CanonicalFourierCutL2 N U‖ ≤ 1 * ‖U‖
          simpa only [one_mul] using n06CanonicalFourierCutL2_norm_le N U)

theorem n06CanonicalFourierCutMap_apply {m : ℕ} (N : ℕ) (U : CanonicalL2 S K m) :
    n06CanonicalFourierCutMap N U = n06CanonicalFourierCutL2 N U := rfl

variable {T : MaterialData} {V : VolumeModelData S K}

theorem n06VolumeFourierCut_add (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (u v : V.level γ t b) :
    n06VolumeFourierCut hV γ t b N (u + v) =
      n06VolumeFourierCut hV γ t b N u + n06VolumeFourierCut hV γ t b N v := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro j
  change n06CanonicalFourierCutL2 N (u.val m j + v.val m j) =
    n06CanonicalFourierCutL2 N (u.val m j) + n06CanonicalFourierCutL2 N (v.val m j)
  exact n06CanonicalFourierCutL2_add N _ _

theorem n06VolumeFourierCut_smul (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (c : ℝ) (v : V.level γ t b) :
    n06VolumeFourierCut hV γ t b N (c • v) =
      c • n06VolumeFourierCut hV γ t b N v := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply PiLp.ext
  intro j
  change n06CanonicalFourierCutL2 N (c • v.val m j) =
    c • n06CanonicalFourierCutL2 N (v.val m j)
  exact n06CanonicalFourierCutL2_smul N c _

/-- The same cutoff acts continuously and linearly on every original level. -/
def n06VolumeFourierCutMap (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) : V.level γ t b →L[ℝ] V.level γ t b :=
  ({ toFun := n06VolumeFourierCut hV γ t b N
     map_add' := n06VolumeFourierCut_add hV γ t b N
     map_smul' := fun c v => n06VolumeFourierCut_smul hV γ t b N c v } :
      V.level γ t b →ₗ[ℝ] V.level γ t b).mkContinuous 1
        (fun v => by
          change ‖n06VolumeFourierCut hV γ t b N v‖ ≤ 1 * ‖v‖
          simpa only [one_mul] using n06VolumeFourierCut_norm_le hV γ t b N v)

theorem n06VolumeFourierCutMap_apply (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) :
    n06VolumeFourierCutMap hV γ t b N v = n06VolumeFourierCut hV γ t b N v := rfl

/-- The true material weights in forget commute with the exact cutoff. -/
theorem n06VolumeFourierCut_forget (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) (m : ℕ) :
    V.forget γ t b (n06VolumeFourierCut hV γ t b N v) m =
      n06CanonicalFourierCutL2 N (V.forget γ t b v m) := by
  rw [hV.2.2.2 γ t b (n06VolumeFourierCut hV γ t b N v) m,
    hV.2.2.2 γ t b v m, n06VolumeFourierCut_apply, n06CanonicalFourierCutL2_smul]

theorem n06VolumeMember_fourierCut (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} {F : CanonicalSequence S K}
    (hF : VolumeMember S K V γ t b F) (N : ℕ) :
    VolumeMember S K V γ t b (fun m => n06CanonicalFourierCutL2 N (F m)) := by
  obtain ⟨v, rfl⟩ := hF
  exact ⟨n06VolumeFourierCut hV γ t b N v,
    funext (n06VolumeFourierCut_forget hV γ t b N v)⟩

end ContinuousFlexibility.Statements
