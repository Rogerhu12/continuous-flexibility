module

public import ContinuousFlexibility.Analysis.N06FourierCutLinearity
public import ContinuousFlexibility.Analysis.N06ReferenceProjectionRepresentatives
public import ContinuousFlexibility.Analysis.N06MaterialJetRows

/-!
# Projecting the true source while keeping its compatibility column

The projected source is cut(F - omega Psi) + omega Psi in precisely the
original volume level. Its physical representative is the projection of
f - omega psi with the original column added back. Strong convergence
and the alternate three-column formula are consequences of the actual
linear cutoff, without any finite-spectrum assumption on psi.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

/-- The original source forget map retains its actual reflection symmetry. -/
theorem n06Volume_forget_reflection (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (F : V.level γ t b) (m : ℕ) :
    (fun p : PolarPoint => V.forget γ t b F m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (V.forget γ t b F m : PolarPoint → ℝ) := by
  have hF : F.val ∈ canonicalVolumeGraph S K b := by
    rw [← hV.1 γ t b]
    exact F.property
  have he := n06MaterialJetRow_reflection (T := T) γ t F.val hF m
  simpa only [n06MaterialJetRow_zero_eq_forget hV γ t b F m] using he

/-- Addition of a scalar physical column is represented by the same
linear operations in the original source space. -/
theorem n06Volume_forget_source_add_smul_ae
    {γ t : ℝ} {b : ℕ} (F P : V.level γ t b) (c : ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) {f g : PolarPoint → ℝ}
    (hF : (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hP : (V.forget γ t b P m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g) :
    (V.forget γ t b (F + c • P) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m (fun p => f p + c * g p) := by
  have he : V.forget γ t b (F + c • P) m =
      V.forget γ t b F m + c • V.forget γ t b P m := by
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  filter_upwards [Lp.coeFn_add (V.forget γ t b F m) (c • V.forget γ t b P m),
    Lp.coeFn_smul c (V.forget γ t b P m), hF, hP] with p ha hc hf hg
  simp only [Pi.add_apply] at ha
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  rw [he, ha, hc, hf, hg]
  simp only [canonicalSource]
  ring

theorem n06Volume_forget_source_sub_smul_ae
    {γ t : ℝ} {b : ℕ} (F P : V.level γ t b) (c : ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) {f g : PolarPoint → ℝ}
    (hF : (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hP : (V.forget γ t b P m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g) :
    (V.forget γ t b (F - c • P) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m (fun p => f p - c * g p) := by
  have he : F - c • P = F + (-c) • P :=
    (sub_eq_add_neg F (c • P)).trans
      (congrArg (fun X : V.level γ t b => F + X) (_root_.neg_smul c P).symm)
  rw [he]
  have hh := n06Volume_forget_source_add_smul_ae F P (-c) z m hF hP
  simpa only [neg_mul, ← sub_eq_add_neg] using hh

/-- Only the actual compatible forcing is projected. -/
def n06CompatibilityFourierSource (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} (P : V.level γ t b) (omega : ℝ)
    (F : V.level γ t b) (N : ℕ) : V.level γ t b :=
  n06VolumeFourierCut hV γ t b N (F - omega • P) + omega • P

theorem n06CompatibilityFourierSource_eq (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} (P : V.level γ t b) (omega : ℝ)
    (F : V.level γ t b) (N : ℕ) :
    n06CompatibilityFourierSource hV P omega F N =
      n06VolumeFourierCut hV γ t b N F +
        omega • (P - n06VolumeFourierCut hV γ t b N P) := by
  change n06VolumeFourierCutMap hV γ t b N (F - omega • P) + omega • P = _
  rw [map_sub, map_smul, n06VolumeFourierCutMap_apply, n06VolumeFourierCutMap_apply,
    smul_sub]
  abel

theorem n06CompatibilityFourierSource_tendsto (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} (P : V.level γ t b) (omega : ℝ) (F : V.level γ t b) :
    Tendsto (n06CompatibilityFourierSource hV P omega F) atTop (𝓝 F) := by
  change Tendsto (fun N => n06VolumeFourierCut hV γ t b N (F - omega • P) + omega • P)
    atTop (𝓝 F)
  have h := (n06VolumeFourierCut_tendsto hV γ t b (F - omega • P)).add_const (omega • P)
  simpa only [sub_add_cancel] using h

variable {D : ReferenceData} {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- The exact source cutoff has the true projected physical representative. -/
theorem n06VolumeFourierCut_source_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} (F : V.level γ t b) (N m : ℕ)
    {f : PolarPoint → ℝ} (hfp : Function.Periodic f (0, Real.pi))
    (hF : (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f) :
    (V.forget γ t b (n06VolumeFourierCut hV γ t b N F) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (referenceBasisProjection (Finset.range (N + 1)) f) := by
  rw [n06VolumeFourierCut_forget hV γ t b N F m]
  exact n06_controlledReferenceSource_fourierCut_ae h hcoordinates m _
    (n06Volume_forget_reflection hV γ t b F m) hfp hF N

/-- The original compatibility field is restored pointwise after cutting
the physical compatible source, with exactly its original scalar. -/
theorem n06CompatibilityFourierSource_physical
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} (P : V.level γ t b) (omega : ℝ)
    (F : V.level γ t b) (N m : ℕ) {f ψ : PolarPoint → ℝ}
    (hgp : Function.Periodic (fun p => f p - omega * ψ p) (0, Real.pi))
    (hF : (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f)
    (hP : (V.forget γ t b P m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m ψ) :
    (V.forget γ t b (n06CompatibilityFourierSource hV P omega F N) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (fun p => referenceBasisProjection (Finset.range (N + 1))
          (fun q => f q - omega * ψ q) p + omega * ψ p) := by
  have hg := n06Volume_forget_source_sub_smul_ae F P omega (C.referenceState, 0) m hF hP
  have hcut := n06VolumeFourierCut_source_ae h hcoordinates hV (F - omega • P) N m hgp hg
  exact n06Volume_forget_source_add_smul_ae _ P omega (C.referenceState, 0) m hcut hP

end ContinuousFlexibility.Statements
