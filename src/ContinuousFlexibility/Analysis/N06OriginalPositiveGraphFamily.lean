import ContinuousFlexibility.Analysis.N06ControlledPositiveCubic

/-!
# Positive modal families from the same original graph element

The actual reference forcing map and the weighted height lift are
evaluated on the original graph element's source. The N05 left-inverse
identity returns that same graph element. Thus the existing positive
weak graph construction gives its actual modal representatives without
adding a forcing lift or a weak PDE as an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n06N05_exists_original_positiveGraphFamily
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (a c pot q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c pot q κ Cref)
    (hea : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a m p.1) (canonicalOpen S K m))
    (heb : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c m p.1) (canonicalOpen S K m))
    (hepot : ∀ m, K.positive m = true → EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot m p.1) (canonicalOpen S K m))
    (hcd : ∀ m, K.positive m = true → ∀ y ∈ Ioo (K.left m) (K.right m),
      DifferentiableAt ℝ (c m) y)
    (u : B.Space) :
    ∃ F : Vol.level (3 / 4 : ℝ) 0 b,
      ∃ W : Vol.level (3 / 4 : ℝ) (-B.lossMaterial) b,
        ∃ P : N06PositiveWeakGraphFamily T K (3 / 4 : ℝ) B.lossMaterial
          F.val W.val a c pot κ,
          (∀ m, n06MaterialJetRow T K (3 / 4 : ℝ) (-B.lossMaterial) W.val m 0 =
            u.val.1.1 m) ∧
          (∀ m, (n06MaterialJetRow T K (3 / 4 : ℝ) 0 F.val m 0 : PolarPoint → ℝ)
            =ᵐ[canonicalMeasure S K m]
              n06ReferenceCanonicalForcing D S C K u.val.1
                (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hVol : IsVolumeModel T S K Vol := h.2.2.1
  have hB : N04PartB S C L K base ε := (n06_N04_qualitative_parts h04).2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hinverse : B.inverse u.val.2 = u := h.2.2.2.2.2.2.2.2.2.1 u
  obtain ⟨J, hJ, hweakJ⟩ := n06N05_exists_referenceForcingMap
    h01.1.1 hT hS h01.1.2.2.2.1 h hcoordinates
  obtain ⟨_C, _hC, H, _hHnorm, _hHglobal, hH, _hHfield⟩ :=
    n06N05_exists_weightedHeight h.2
  let F : Vol.level (3 / 4 : ℝ) 0 b := J u.val.2
  let W : Vol.level (3 / 4 : ℝ) (-B.lossMaterial) b := H u.val.2
  have hheight (m : ℕ) :
      n06MaterialJetRow T K (3 / 4 : ℝ) (-B.lossMaterial) W.val m 0 = u.val.1.1 m := by
    calc
      _ = Vol.forget (3 / 4 : ℝ) (-B.lossMaterial) b W m :=
        n06MaterialJetRow_zero_eq_forget hVol _ _ b W m
      _ = n06InverseCanonicalHeight B u.val.2 m := congrFun (hH u.val.2) m
      _ = (B.inverse u.val.2).val.1.1 m := n06InverseCanonicalHeight_apply u.val.2 m
      _ = _ := by rw [hinverse]
  have hforcing (m : ℕ) :
      (n06MaterialJetRow T K (3 / 4 : ℝ) 0 F.val m 0 : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06ReferenceCanonicalForcing D S C K u.val.1
            (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m := by
    rw [n06MaterialJetRow_zero_eq_forget hVol _ _ b F m]
    simpa only [hinverse] using hJ u.val.2 m
  have hweak : ∀ m, K.positive m = true → ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, n06MaterialJetRow T K (3 / 4 : ℝ) (-B.lossMaterial) W.val m 0 p *
        n06UnitReferenceTestOperator (a m) (c m) (pot m) ψ p ∂canonicalMeasure S K m) =
      ∫ p, n06MaterialJetRow T K (3 / 4 : ℝ) 0 F.val m 0 p * ψ p
        ∂canonicalMeasure S K m := by
    intro m hm ψ hψ
    rw [hheight m, n06MaterialJetRow_zero_eq_forget hVol _ _ b F m]
    have hpair := n06_canonicalOperator_pairing_eq_unitReference hB href hsector hm
      (hea m hm) (heb m hm) (hec m hm) (hepot m hm) (hcd m hm)
      (u.val.1.1 m) hψ.1
    refine hpair.symm.trans ?_
    simpa only [hinverse] using hweakJ u.val.2 m hm ψ hψ
  obtain ⟨P⟩ := n06_positiveWeakGraphFamily_nonempty hVol (3 / 4 : ℝ) B.lossMaterial b
    a c pot q κ Cref hgeometry F W hweak
  exact ⟨F, W, P, hheight, hforcing⟩

end ContinuousFlexibility.Analysis
