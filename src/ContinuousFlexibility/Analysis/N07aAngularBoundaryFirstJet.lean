import ContinuousFlexibility.Analysis.N07aAngularBoundaryPoint
import ContinuousFlexibility.Analysis.N07aAngularBoundaryQuotient
import ContinuousFlexibility.Analysis.N07aAngularInverseGermTransport
import ContinuousFlexibility.Analysis.N07aAngularReferenceTransport

/-!
# Actual transported physical fields have matching interface one-jets

The two smooth branches below are constructed from genuine inverse germs.
Their equality on the closed pieces is proved from the actual open inverse.
Both root and cut matching are consumed through the proved primitive-jet
normal form; no smoothness or matching of a proposed solution is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff NNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {i j : ℕ}

theorem n07a_actual_referenceHeight_interface
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceRadial S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hboundary : K.physicalRight i = K.physicalLeft j)
    (hcore : K.physicalRight i ∈ Ioo D.a D.b)
    (d : N07aInterfaceJetData S C K base ε i j)
    {g : ℕ → PolarPoint → PolarPoint}
    (hg : ∀ m, Continuous (g m) ∧ EqOn (K.inverseChart z m) (g m) (canonicalOpen S K m))
    (hLip : ∀ m, ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart z m) (canonicalOpen S K m))
    (aL : ℝ) {η : PolarPoint → ℝ} (hη : ContDiffOn ℝ ∞ η (annularOpen D))
    (θ : ℝ) :
    let p : PolarPoint := (K.physicalRight i, θ)
    ∃ u v : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ContDiffAt ℝ ∞ v p ∧
      u p = v p ∧ fderiv ℝ u p = fderiv ℝ v p ∧
      (∀ᶠ x in 𝓝 p, x.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) →
        n07aReferencePieceHeight C K z g aL η i x = u x) ∧
      (∀ᶠ x in 𝓝 p, x.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j) →
        n07aReferencePieceHeight C K z g aL η j x = v x) := by
  let p : PolarPoint := (K.physicalRight i, θ)
  obtain ⟨α, hqi, hqj⟩ := n07a_interface_common_preimage h01 h04 href hz hs d θ
  let q : PolarPoint := (K.physicalRight i, α)
  have hii : K.physicalRight i ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    ⟨(h04.2.2.2.1 i).1.le, le_rfl⟩
  have hij : K.physicalRight i ∈ Icc (K.physicalLeft j) (K.physicalRight j) := by
    rw [hboundary]
    exact ⟨le_rfl, (h04.2.2.2.1 j).1.le⟩
  have hrefz := n07a_reference_mem_stateNeighborhood h01
  have hrefs := h01.2.2.1.stateSector
  have hri := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) hrefz hrefs i p hii
  have hrj := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) hrefz hrefs j p hij
  have hci := h04.2.2.2.2.2.2.2.2.1 z hz hs i q hii
  have hcj := h04.2.2.2.2.2.2.2.2.1 z hz hs j q hij
  obtain ⟨Bi, Gi, hBi, hGi, hGiv, hGid, hGie⟩ :=
    n07a_actual_inverse_pullback_germ h01 h04 hz hs i (p := p) (q := q)
      hii hii hqi (hg i).1 (hg i).2 (hLip i)
  obtain ⟨Bj, Gj, hBj, hGj, hGjv, hGjd, hGje⟩ :=
    n07a_actual_inverse_pullback_germ h01 h04 hz hs j (p := p) (q := q)
      hij hij hqj (hg j).1 (hg j).2 (hLip j)
  let Ti : PolarPoint → PolarPoint := Gi ∘ K.chart (C.referenceState, 0) i
  let Tj : PolarPoint → PolarPoint := Gj ∘ K.chart (C.referenceState, 0) j
  let A : PolarPoint →L[ℝ] PolarPoint :=
    (Bi.symm : PolarPoint →L[ℝ] PolarPoint).comp
      (fderiv ℝ (K.chart (C.referenceState, 0) i) p)
  have hTi : ContDiffAt ℝ ∞ Ti p := hGi.comp p hri.1
  have hTj : ContDiffAt ℝ ∞ Tj p := hGj.comp p hrj.1
  have hTiv : Ti p = q := hGiv
  have hTjv : Tj p = q := hGjv
  have hTid : HasFDerivAt Ti A p := hGid.comp p (hri.1.differentiableAt (by simp)).hasFDerivAt
  have hderiv := n07a_aligned_inverse_transport_derivative
    (fderiv ℝ (K.chart z i) q) (fderiv ℝ (K.chart z j) q)
    (fderiv ℝ (K.chart (C.referenceState, 0) i) p)
    (fderiv ℝ (K.chart (C.referenceState, 0) j) p)
    Bi Bj d.orientationLeft_ne hBi.symm hBj.symm
    (n07a_interface_derivative_alignments h04 hz hs hboundary d α)
    (n07a_interface_derivative_alignments h04 hrefz hrefs hboundary d θ)
  have hTjd : HasFDerivAt Tj A p :=
    (hGjd.comp p (hrj.1.differentiableAt (by simp)).hasFDerivAt).congr_fderiv hderiv.symm
  have hcovector :
      (fderiv ℝ (fun x => (K.chart z i x).1) q).comp A =
        fderiv ℝ (fun x => (K.chart (C.referenceState, 0) i x).1) p := by
    rw [((hci.1.differentiableAt (by simp)).hasFDerivAt.fst).fderiv,
      ((hri.1.differentiableAt (by simp)).hasFDerivAt.fst).fderiv]
    simpa only [hBi, A] using n07a_inverse_transport_normal_covector Bi
      (fderiv ℝ (K.chart (C.referenceState, 0) i) p)
  let χ : PolarPoint → ℝ := fun x => aL * S.chiLeft x.1
  let f : PolarPoint → ℝ := fun x => η x - χ x
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  have hf : ContDiffAt ℝ ∞ f q :=
    (hη.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show q ∈ annularOpen D from ⟨hcore, mem_univ _⟩))).sub hχ.contDiffAt
  have hbi : ContDiffAt ℝ ∞ (fun x => K.height z i (Ti x)) p := by
    have h : ContDiffAt ℝ ∞ (K.height z i) (Ti p) := by simpa only [hTiv] using hci.2.1
    exact h.comp p hTi
  have hbj : ContDiffAt ℝ ∞ (fun x => K.height z j (Tj x)) p := by
    have h : ContDiffAt ℝ ∞ (K.height z j) (Tj p) := by simpa only [hTjv] using hcj.2.1
    exact h.comp p hTj
  have hfi : ContDiffAt ℝ ∞ (fun x => f (Ti x)) p := by
    have h : ContDiffAt ℝ ∞ f (Ti p) := by simpa only [hTiv] using hf
    exact h.comp p hTi
  have hfj : ContDiffAt ℝ ∞ (fun x => f (Tj x)) p := by
    have h : ContDiffAt ℝ ∞ f (Tj p) := by simpa only [hTjv] using hf
    exact h.comp p hTj
  let u : PolarPoint → ℝ := fun x =>
    (K.height (C.referenceState, 0) i x / K.height z i (Ti x)) * f (Ti x) + χ x
  let v : PolarPoint → ℝ := fun x =>
    (K.height (C.referenceState, 0) j x / K.height z j (Tj x)) * f (Tj x) + χ x
  have hu : ContDiffAt ℝ ∞ u p := ((hri.2.1.div hbi
    (by simpa only [hTiv] using hci.2.2.2.ne')).mul hfi).add hχ.contDiffAt
  have hv : ContDiffAt ℝ ∞ v p := ((hrj.2.1.div hbj
    (by simpa only [hTjv] using hcj.2.2.2.ne')).mul hfj).add hχ.contDiffAt
  have hcjets := d.jets z (Or.inr ⟨hz, hs⟩) α
  have hrjets := d.jets (C.referenceState, 0) (Or.inl rfl) θ
  have hmatch := n07a_heightTransport_firstJet_match
    (hri.2.1.differentiableAt (by simp)) (hrj.2.1.differentiableAt (by simp))
    (hci.2.1.differentiableAt (by simp)) (hcj.2.1.differentiableAt (by simp))
    (hf.differentiableAt (by simp)) (hχ.differentiable (by simp) p)
    hTid hTjd hTiv hTjv hrjets.2.2.2.1.symm hcjets.2.2.2.1.symm hci.2.2.2.ne'
    hrjets.2.2.2.2 hcjets.2.2.2.2 hcovector
  refine ⟨u, v, hu, hv, hmatch.1.symm, hmatch.2.symm, ?_, ?_⟩
  · filter_upwards [hGie] with x hx hxc
    dsimp only [n07aReferencePieceHeight]
    rw [hx hxc]
    dsimp only [u, Ti, f, χ, Function.comp_apply]
    ring
  · filter_upwards [hGje] with x hx hxc
    dsimp only [n07aReferencePieceHeight]
    rw [hx hxc]
    dsimp only [v, Tj, f, χ, Function.comp_apply]
    ring

end ContinuousFlexibility.Analysis
