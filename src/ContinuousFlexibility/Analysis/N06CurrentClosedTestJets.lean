import ContinuousFlexibility.Analysis.N06CurrentTestTraces
import ContinuousFlexibility.Analysis.N06RootTransmissionJets

/-!
# Actual closed test jets and the moving canonical cut law

The continuous representatives of the open test jets agree with the
ordinary jets of the genuine stored inverse on the closed canonical tile.
The original N04 transmission law therefore applies directly to these
traces at the common canonical radius, even when its physical image moves.

A smooth affine probe with the same physical first jet also extends that
law to any physical function differentiable at the actual cut point.
No transmission condition for the function is added as an assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Continuity identifies all three genuine closed representatives with
the actual stored canonical function and its ordinary first derivatives. -/
theorem N06CurrentHeightTestTraces.closed_eq
    {m : ℕ} {φ : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) :
    EqOn Q.value (canonicalHeight S K z m φ)
        (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
      EqOn Q.radial (radialPartial (canonicalHeight S K z m φ))
        (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
      EqOn Q.angular (angularPartial (canonicalHeight S K z m φ))
        (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) := by
  let P : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  let R : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
  have hPR : P ⊆ R := Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self
  have hRP : R ⊆ closure P := by
    simpa only [P, R, closure_prod_eq,
      closure_Ioo (h04.1.referenceBounds m).2.1.ne, closure_Ioc Real.pi_pos.ne] using
      (Subset.rfl : R ⊆ R)
  have hW (p : PolarPoint) (hp : p ∈ R) :
      ContDiffAt ℝ ∞ (canonicalHeight S K z m φ) p :=
    n04b_canonicalHeight_contDiffAt_closed h04.1 hz hs m ⟨hp.1, mem_univ _⟩ hφ
  have hvalue : ContinuousOn (canonicalHeight S K z m φ) R :=
    fun p hp => (hW p hp).continuousAt.continuousWithinAt
  have hradial : ContinuousOn (radialPartial (canonicalHeight S K z m φ)) R :=
    fun p hp => (contDiffAt_radialPartial (hW p hp) (m := ∞)
      (by simp)).continuousAt.continuousWithinAt
  have hangular : ContinuousOn (angularPartial (canonicalHeight S K z m φ)) R :=
    fun p hp => (contDiffAt_angularPartial (hW p hp) (m := ∞)
      (by simp)).continuousAt.continuousWithinAt
  exact ⟨Q.value_eq.of_subset_closure Q.value_lipschitz.continuous.continuousOn
      hvalue hPR hRP,
    Q.radial_eq.of_subset_closure Q.radial_lipschitz.continuous.continuousOn
      hradial hPR hRP,
    Q.angular_eq.of_subset_closure Q.angular_lipschitz.continuous.continuousOn
      hangular hPR hRP⟩

/-- The actual current test satisfies the original affine cut law at
the same canonical angle on both halves. No physical radial cut is used. -/
theorem n06_current_closed_test_cut_traces
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (n : ℕ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Ql : N06CurrentHeightTestTraces S K z (K.cutPair n).1 φ)
    (Qr : N06CurrentHeightTestTraces S K z (K.cutPair n).2 φ)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    Ql.value (K.cutRadius n, θ) = Qr.value (K.cutRadius n, θ) ∧
      Ql.radial (K.cutRadius n, θ) + Qr.radial (K.cutRadius n, θ) =
        -(2 * K.cutRadius n)⁻¹ * Ql.value (K.cutRadius n, θ) ∧
      Ql.angular (K.cutRadius n, θ) = Qr.angular (K.cutRadius n, θ) := by
  obtain ⟨_, _, _, _, _, hR, hl, hr, hRl, hRr⟩ := h04.2.1.1.1 n
  have hpl : (K.cutRadius n, θ) ∈
      Icc (K.left (K.cutPair n).1) (K.right (K.cutPair n).1) ×ˢ
        Icc (0 : ℝ) Real.pi := by
    rw [hl, hRl]
    exact ⟨⟨hR.le, le_rfl⟩, hθ⟩
  have hpr : (K.cutRadius n, θ) ∈
      Icc (K.left (K.cutPair n).2) (K.right (K.cutPair n).2) ×ˢ
        Icc (0 : ℝ) Real.pi := by
    rw [hr, hRr]
    exact ⟨⟨hR.le, le_rfl⟩, hθ⟩
  have hQl := Ql.closed_eq h04 hz hs hφ
  have hQr := Qr.closed_eq h04 hz hs hφ
  rw [hQl.1 hpl, hQr.1 hpr, hQl.2.1 hpl, hQr.2.1 hpr,
    hQl.2.2 hpl, hQr.2.2 hpr]
  have hcut := h04.2.1.2.1 z hz hs φ hφ n θ
  refine ⟨hcut.1.symm, ?_, ?_⟩
  · rw [hcut.2]
    simp only [div_eq_mul_inv]
    ring
  · apply n06_angularPartial_eq_of_boundary_values
      ((n04b_canonicalHeight_contDiffAt_closed h04.1 hz hs (K.cutPair n).1
        ⟨hpl.1, mem_univ _⟩ hφ).differentiableAt (by simp))
      ((n04b_canonicalHeight_contDiffAt_closed h04.1 hz hs (K.cutPair n).2
        ⟨hpr.1, mem_univ _⟩ hφ).differentiableAt (by simp))
    intro η
    exact (h04.2.1.2.1 z hz hs φ hφ n η).1.symm

/-- The value and differential of the actual canonical pullback depend
only on the physical first jet at its genuine inverse image. -/
theorem n06_canonicalHeight_firstJet_congr
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalClosed S K m)
    {f g : PolarPoint → ℝ}
    (hf : DifferentiableAt ℝ f (K.inverseChart z m p))
    (hg : DifferentiableAt ℝ g (K.inverseChart z m p))
    (hv : f (K.inverseChart z m p) = g (K.inverseChart z m p))
    (hd : fderiv ℝ f (K.inverseChart z m p) =
      fderiv ℝ g (K.inverseChart z m p)) :
    canonicalHeight S K z m f p = canonicalHeight S K z m g p ∧
      fderiv ℝ (canonicalHeight S K z m f) p =
        fderiv ℝ (canonicalHeight S K z m g) p := by
  have hG := (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hp).differentiableAt
    (by simp)
  have hb := h04.1.boundary z hz hs m
  have hh := hb.2.2.2.2.1 _ (hb.2.1 hp)
  have hH : DifferentiableAt ℝ
      (fun q => K.height z m (K.inverseChart z m q)) p :=
    (hh.2.1.differentiableAt (by simp)).comp p hG
  have hInv : DifferentiableAt ℝ
      (fun q => (K.height z m (K.inverseChart z m q))⁻¹) p := by
    exact hH.fun_inv hh.2.2.2.ne'
  have hF : DifferentiableAt ℝ (fun q => f (K.inverseChart z m q)) p :=
    hf.comp p hG
  have hG' : DifferentiableAt ℝ (fun q => g (K.inverseChart z m q)) p :=
    hg.comp p hG
  constructor
  · change f (K.inverseChart z m p) / K.height z m (K.inverseChart z m p) =
      g (K.inverseChart z m p) / K.height z m (K.inverseChart z m p)
    rw [hv]
  · change fderiv ℝ (fun q => f (K.inverseChart z m q) /
        K.height z m (K.inverseChart z m q)) p =
      fderiv ℝ (fun q => g (K.inverseChart z m q) /
        K.height z m (K.inverseChart z m q)) p
    simp only [div_eq_mul_inv]
    rw [fderiv_fun_mul hF hInv, fderiv_fun_mul hG' hInv]
    have hdf := fderiv_comp p hf hG
    have hdg := fderiv_comp p hg hG
    simp only [Function.comp_def] at hdf hdg
    rw [hdf, hdg, hv, hd]

/-- A physical function differentiable at the actual moving cut point
inherits the original smooth-test transmission law. An affine probe
realizes its exact first jet, so no C-infinity hypothesis on it is needed. -/
theorem n06_canonical_cut_of_differentiableAt
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (n : ℕ) (θ : ℝ) {f : PolarPoint → ℝ}
    (hf : DifferentiableAt ℝ f (canonicalCutPoint S K z n θ)) :
    canonicalHeight S K z (K.cutPair n).2 f (K.cutRadius n, θ) =
        canonicalHeight S K z (K.cutPair n).1 f (K.cutRadius n, θ) ∧
      radialPartial (canonicalHeight S K z (K.cutPair n).2 f) (K.cutRadius n, θ) =
        -radialPartial (canonicalHeight S K z (K.cutPair n).1 f) (K.cutRadius n, θ) -
          canonicalHeight S K z (K.cutPair n).1 f (K.cutRadius n, θ) /
            (2 * K.cutRadius n) := by
  let p : PolarPoint := (K.cutRadius n, θ)
  let x : PolarPoint := canonicalCutPoint S K z n θ
  let A : PolarPoint →L[ℝ] ℝ := fderiv ℝ f x
  let ψ : PolarPoint → ℝ := fun q => f x + (A q - A x)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_const.add (A.contDiff.sub contDiff_const)
  have hψD (q : PolarPoint) : HasFDerivAt ψ A q :=
    (A.hasFDerivAt.sub_const (A x)).const_add (f x)
  have hleft : K.inverseChart z (K.cutPair n).1 p = x := rfl
  have hright : K.inverseChart z (K.cutPair n).2 p = x :=
    (h04.2.1.1.2 z hz hs n).1 θ
  obtain ⟨_, _, _, _, _, hR, hl, hr, hRl, hRr⟩ := h04.2.1.1.1 n
  have hpl : p ∈ canonicalClosed S K (K.cutPair n).1 := by
    change (K.cutRadius n, θ) ∈ Icc (K.left (K.cutPair n).1)
      (K.right (K.cutPair n).1) ×ˢ univ
    rw [hl, hRl]
    exact ⟨⟨hR.le, le_rfl⟩, mem_univ _⟩
  have hpr : p ∈ canonicalClosed S K (K.cutPair n).2 := by
    change (K.cutRadius n, θ) ∈ Icc (K.left (K.cutPair n).2)
      (K.right (K.cutPair n).2) ×ˢ univ
    rw [hr, hRr]
    exact ⟨⟨hR.le, le_rfl⟩, mem_univ _⟩
  have he (m : ℕ) (hp : p ∈ canonicalClosed S K m)
      (hx : K.inverseChart z m p = x) :
      canonicalHeight S K z m f p = canonicalHeight S K z m ψ p ∧
        radialPartial (canonicalHeight S K z m f) p =
          radialPartial (canonicalHeight S K z m ψ) p := by
    have hfm : DifferentiableAt ℝ f (K.inverseChart z m p) := by
      rw [hx]
      exact hf
    have hvm : f (K.inverseChart z m p) = ψ (K.inverseChart z m p) := by
      rw [hx]
      simp only [ψ, sub_self, add_zero]
    have hdm : fderiv ℝ f (K.inverseChart z m p) =
        fderiv ℝ ψ (K.inverseChart z m p) := by
      rw [hx, (hψD x).fderiv]
    have hjet := n06_canonicalHeight_firstJet_congr h04 hz hs m hp hfm
      (hψD _).differentiableAt hvm hdm
    exact ⟨hjet.1, congrArg (fun B : PolarPoint →L[ℝ] ℝ => B (1, 0)) hjet.2⟩
  have hel := he (K.cutPair n).1 hpl hleft
  have her := he (K.cutPair n).2 hpr hright
  have ht := h04.2.1.2.1 z hz hs ψ hψ n θ
  change canonicalHeight S K z (K.cutPair n).2 ψ p =
      canonicalHeight S K z (K.cutPair n).1 ψ p ∧
    radialPartial (canonicalHeight S K z (K.cutPair n).2 ψ) p =
      -radialPartial (canonicalHeight S K z (K.cutPair n).1 ψ) p -
        canonicalHeight S K z (K.cutPair n).1 ψ p / (2 * K.cutRadius n) at ht
  rw [← hel.1, ← her.1, ← hel.2, ← her.2] at ht
  exact ht

/-- In particular, an actual physical radial C1 representative on the
original annulus obeys the reference cut law. The original N01 component
geometry places the common inverse image inside that annulus. -/
theorem n06_reference_cut_scalar_of_contDiffOn_one
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {v : ℝ → ℝ} (hv : ContDiffOn ℝ 1 v (radialCore D)) (n : ℕ) (θ : ℝ) :
    canonicalHeight S K (C.referenceState, 0) (K.cutPair n).2 (fun p => v p.1)
        (K.cutRadius n, θ) =
      canonicalHeight S K (C.referenceState, 0) (K.cutPair n).1 (fun p => v p.1)
        (K.cutRadius n, θ) ∧
    radialPartial (canonicalHeight S K (C.referenceState, 0) (K.cutPair n).2
        (fun p => v p.1)) (K.cutRadius n, θ) =
      -radialPartial (canonicalHeight S K (C.referenceState, 0) (K.cutPair n).1
          (fun p => v p.1)) (K.cutRadius n, θ) -
        canonicalHeight S K (C.referenceState, 0) (K.cutPair n).1 (fun p => v p.1)
          (K.cutRadius n, θ) / (2 * K.cutRadius n) := by
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsref : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hx := (h04.2.1.1.2 (C.referenceState, 0) href hsref n).2.1 ⟨θ, rfl⟩
  have hC := h01.2.2.2.1
  have hxD : (canonicalCutPoint S K (C.referenceState, 0) n θ).1 ∈ radialCore D :=
    ⟨(hC.1 n).1.trans hx.1.1, hx.1.2.trans (hC.1 n).2.2⟩
  apply n06_canonical_cut_of_differentiableAt h04 href hsref n θ
  exact ((hv.contDiffAt (isOpen_Ioo.mem_nhds hxD)).differentiableAt
    (by norm_num)).comp _ differentiableAt_fst

end ContinuousFlexibility.Statements
