import ContinuousFlexibility.Analysis.N07aTubularCutCoordinates
import ContinuousFlexibility.Analysis.N07aLocalPullbackEquation
import ContinuousFlexibility.Analysis.N07aClosedPDEGluing

/-!
# Physical gluing in genuine smooth tubular coordinates

The two closed physical fields are pulled into a single smooth chart.
Their actual equations have identical normalized coefficients there.
The closed transmission theorem then gives a smooth physical field on
an open neighborhood of the actual cut point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_tubular_physical_gluing
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {z : AnnularState S × ℝ} {k : ℕ} {θ₀ : ℝ}
    (B : N07aTubularCutCoordinates S C K z k θ₀)
    (hcore : Ioo (C.left k) (C.right k) ⊆ Ioo D.a D.b)
    {A : SymmetricCoefficients} {u v f : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ A.a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ A.b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ A.c (annularOpen D))
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hu : ContDiffOn ℝ ∞ u (physicalPieceClosed S K z (K.cutPair k).1))
    (hv : ContDiffOn ℝ ∞ v (physicalPieceClosed S K z (K.cutPair k).2))
    (du dv : PolarPoint → PolarPoint →L[ℝ] ℝ)
    (hdu : ∀ p ∈ physicalPieceClosed S K z (K.cutPair k).1,
      HasFDerivWithinAt u (du p) (physicalPieceClosed S K z (K.cutPair k).1) p)
    (hdv : ∀ p ∈ physicalPieceClosed S K z (K.cutPair k).2,
      HasFDerivWithinAt v (dv p) (physicalPieceClosed S K z (K.cutPair k).2) p)
    (hvalue : ∀ θ, u (canonicalCutPoint S K z k θ) = v (canonicalCutPoint S K z k θ))
    (hfirst : ∀ θ, du (canonicalCutPoint S K z k θ) = dv (canonicalCutPoint S K z k θ))
    (hequ : EqOn (divergenceOperator A u) f (physicalPieceOpen S K z (K.cutPair k).1))
    (heqv : EqOn (divergenceOperator A v) f (physicalPieceOpen S K z (K.cutPair k).2))
    (hne : (n07aPullbackPrincipal A B.e.symm).a (canonicalCutPoint S K z k θ₀) ≠ 0) :
    ∃ O : Set PolarPoint, IsOpen O ∧ canonicalCutPoint S K z k θ₀ ∈ O ∧
      ∃ w : PolarPoint → ℝ, ContDiffOn ℝ ∞ w O ∧
        EqOn w u (O ∩ physicalPieceOpen S K z (K.cutPair k).1) ∧
        EqOn w v (O ∩ physicalPieceOpen S K z (K.cutPair k).2) := by
  let R := K.cutRadius k
  let Q := Ioo B.left B.right ×ˢ Ioo B.lower B.upper
  let P := B.e.target ∩ annularOpen D
  have hQopen : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hQcenter : (R, θ₀) ∈ Q :=
    ⟨⟨B.left_lt, B.lt_right⟩, ⟨B.lower_lt, B.lt_upper⟩⟩
  have hQclosed : Q ⊆ Icc B.left B.right ×ˢ Icc B.lower B.upper :=
    Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hQsource : Q ⊆ B.e.source := hQclosed.trans B.closed_source
  have hQannulus : MapsTo B.e Q (annularOpen D) := by
    intro y hy
    exact ⟨hcore (B.component (hQclosed hy)).1, mem_univ _⟩
  have hPopen : IsOpen P := B.e.open_target.inter (isOpen_Ioo.prod isOpen_univ)
  have hQmap : MapsTo B.e Q P := fun y hy =>
    ⟨B.e.map_source (hQsource hy), hQannulus hy⟩
  have hprincipal := n07a_localPullback_principal_smooth hPopen
    (ha.mono inter_subset_right) (hb.mono inter_subset_right)
    (hc.mono inter_subset_right) (B.inverse_smooth.mono inter_subset_left)
  have hα : ContinuousAt
      (fun y => (n07aPullbackPrincipal A B.e.symm).a (B.e y)) (R, θ₀) :=
    ((hprincipal.1.comp B.map_smooth.contDiffOn hQmap).contDiffAt
      (hQopen.mem_nhds hQcenter)).continuousAt
  have hαne : (n07aPullbackPrincipal A B.e.symm).a (B.e (R, θ₀)) ≠ 0 := by
    simpa only [R, B.cut_eq θ₀] using hne
  have hnear : {y : PolarPoint | y ∈ Q ∧
      (n07aPullbackPrincipal A B.e.symm).a (B.e y) ≠ 0} ∈ 𝓝 (R, θ₀) := by
    filter_upwards [hQopen.mem_nhds hQcenter,
      hα.eventually (isOpen_compl_singleton.mem_nhds hαne)] with y hy hny
    exact ⟨hy, hny⟩
  obtain ⟨l, r, a, b, hlR, hRr, haθ, hθb, hsmall⟩ :=
    n07a_closedRectangle_subset_nhds hnear
  have hlr : l < r := hlR.trans hRr
  have hab : a < b := haθ.trans hθb
  let Y := Ioo l r ×ˢ Ioo a b
  let YL := Ioo l R ×ˢ Ioo a b
  let YR := Ioo R r ×ˢ Ioo a b
  let CL := Icc l R ×ˢ Icc a b
  let CR := Icc R r ×ˢ Icc a b
  have hYopen : IsOpen Y := isOpen_Ioo.prod isOpen_Ioo
  have hYLopen : IsOpen YL := isOpen_Ioo.prod isOpen_Ioo
  have hYRopen : IsOpen YR := isOpen_Ioo.prod isOpen_Ioo
  have hYsmall : Y ⊆ Icc l r ×ˢ Icc a b :=
    Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hCLsmall : CL ⊆ Icc l r ×ˢ Icc a b :=
    fun y hy => ⟨⟨hy.1.1, hy.1.2.trans hRr.le⟩, hy.2⟩
  have hCRsmall : CR ⊆ Icc l r ×ˢ Icc a b :=
    fun y hy => ⟨⟨hlR.le.trans hy.1.1, hy.1.2⟩, hy.2⟩
  have hYsub : Y ⊆ Q := fun y hy => (hsmall (hYsmall hy)).1
  have hYLsub : YL ⊆ Y := fun y hy => ⟨⟨hy.1.1, hy.1.2.trans hRr⟩, hy.2⟩
  have hYRsub : YR ⊆ Y := fun y hy => ⟨⟨hlR.trans hy.1.1, hy.1.2⟩, hy.2⟩
  have hYsource : Y ⊆ B.e.source := hYsub.trans hQsource
  have hYmap : MapsTo B.e Y P := fun _ hy => hQmap (hYsub hy)
  have hYne : ∀ y ∈ Y, (n07aPullbackPrincipal A B.e.symm).a (B.e y) ≠ 0 :=
    fun _ hy => (hsmall (hYsmall hy)).2
  have hLmap : MapsTo B.e YL (physicalPieceOpen S K z (K.cutPair k).1) := by
    intro y hy
    have hq := hYsub (hYLsub hy)
    exact B.left_open ⟨⟨hq.1.1, hy.1.2⟩, hq.2⟩
  have hRmap : MapsTo B.e YR (physicalPieceOpen S K z (K.cutPair k).2) := by
    intro y hy
    have hq := hYsub (hYRsub hy)
    exact B.right_open ⟨⟨hy.1.1, hq.1.2⟩, hq.2⟩
  have hLCmap : MapsTo B.e CL (physicalPieceClosed S K z (K.cutPair k).1) := by
    intro y hy
    have hq := (hsmall (hCLsmall hy)).1
    exact B.left_closed ⟨⟨hq.1.1.le, hy.1.2⟩, Ioo_subset_Icc_self hq.2⟩
  have hRCmap : MapsTo B.e CR (physicalPieceClosed S K z (K.cutPair k).2) := by
    intro y hy
    have hq := (hsmall (hCRsmall hy)).1
    exact B.right_closed ⟨⟨hy.1.1, hq.1.2.le⟩, Ioo_subset_Icc_self hq.2⟩
  let N := n07aPullbackNormalCoefficients A B.e.symm B.e
  have hN : ∀ i, ContDiffOn ℝ ∞ (N i) Y :=
    n07a_localPullback_normalCoefficients_smooth hPopen
      (ha.mono inter_subset_right) (hb.mono inter_subset_right)
      (hc.mono inter_subset_right) (B.inverse_smooth.mono inter_subset_left)
      B.map_smooth.contDiffOn hYmap hYne
  have hsource : ContDiffOn ℝ ∞ (f ∘ B.e) Y :=
    hf.comp B.map_smooth.contDiffOn (fun _ hy => (hYmap hy).2)
  have htransport {W : Set PolarPoint} (hW : IsOpen W) (hWY : W ⊆ Y)
      {s : Set PolarPoint} {g : PolarPoint → ℝ}
      (hg : ContDiffOn ℝ ∞ g (closure s)) (hmap : MapsTo B.e W s)
      (heq : EqOn (divergenceOperator A g) f s) :
      EqOn (mixedDerivative 2 0 (g ∘ B.e))
        (n07aNormalRhs N (g ∘ B.e) (f ∘ B.e)) W := by
    let X := B.e.target ∩ B.e.symm ⁻¹' W
    have hX : IsOpen X := B.e.isOpen_inter_preimage_symm hW
    have hXs : X ⊆ s := by
      intro x hx
      have he := hmap hx.2
      simpa only [B.e.right_inv hx.1] using he
    have hXP : X ⊆ P := by
      intro x hx
      have he := hYmap (hWY hx.2)
      rw [B.e.right_inv hx.1] at he
      exact he
    have hGW : MapsTo B.e W X := by
      intro y hy
      have hys := hYsource (hWY hy)
      exact ⟨B.e.map_source hys, by simpa only [B.e.left_inv hys] using hy⟩
    exact n07a_localPullback_normal_equation hX hW
      (ha.mono (hXP.trans inter_subset_right))
      (hb.mono (hXP.trans inter_subset_right))
      (hc.mono (hXP.trans inter_subset_right))
      (B.inverse_smooth.mono inter_subset_left)
      B.map_smooth.contDiffOn (fun _ hx => hx.2) hGW
      (fun _ hx => B.e.right_inv hx.1)
      (fun _ hy => B.e.left_inv (hYsource (hWY hy)))
      (hg.mono (hXs.trans subset_closure)) (heq.mono hXs)
      (fun _ hy => hYne _ (hWY hy))
  have hleftEq := htransport hYLopen hYLsub hu hLmap hequ
  have hrightEq := htransport hYRopen hYRsub hv hRmap heqv
  have hul : ContDiffOn ℝ ∞ (u ∘ B.e) CL := hu.comp B.map_smooth.contDiffOn hLCmap
  have hvr : ContDiffOn ℝ ∞ (v ∘ B.e) CR := hv.comp B.map_smooth.contDiffOn hRCmap
  have hval : ∀ θ ∈ Ioo a b, (u ∘ B.e) (R, θ) = (v ∘ B.e) (R, θ) := by
    intro θ _
    simpa only [Function.comp_apply, R, B.cut_eq θ] using hvalue θ
  have hjet : ∀ θ ∈ Ioo a b,
      fderivWithin ℝ (u ∘ B.e) CL (R, θ) =
        fderivWithin ℝ (v ∘ B.e) CR (R, θ) := by
    intro θ hθ
    have hpL : (R, θ) ∈ CL := ⟨⟨hlR.le, le_rfl⟩, Ioo_subset_Icc_self hθ⟩
    have hpR : (R, θ) ∈ CR := ⟨⟨le_rfl, hRr.le⟩, Ioo_subset_Icc_self hθ⟩
    have he := (B.map_smooth.differentiable (by simp) (R, θ)).hasFDerivAt
    have hdL := (hdu _ (hLCmap hpL)).comp (R, θ) he.hasFDerivWithinAt hLCmap
    have hdR := (hdv _ (hRCmap hpR)).comp (R, θ) he.hasFDerivWithinAt hRCmap
    rw [hdL.fderivWithin (((uniqueDiffOn_Icc hlR).prod (uniqueDiffOn_Icc hab)) _ hpL),
      hdR.fderivWithin (((uniqueDiffOn_Icc hRr).prod (uniqueDiffOn_Icc hab)) _ hpR)]
    rw [show B.e (R, θ) = canonicalCutPoint S K z k θ from B.cut_eq θ, hfirst θ]
  have hglue := n07a_closedRectangle_normalTransmission_smooth_gluing
    hlR hRr hab hN hsource hul hvr hleftEq hrightEq hval hjet
  let O := B.e.target ∩ B.e.symm ⁻¹' Y
  let w : PolarPoint → ℝ :=
    (fun y : PolarPoint => if y.1 ≤ R then u (B.e y) else v (B.e y)) ∘ B.e.symm
  have hO : IsOpen O := B.e.isOpen_inter_preimage_symm hYopen
  have hcenter : (R, θ₀) ∈ Y := ⟨⟨hlR, hRr⟩, ⟨haθ, hθb⟩⟩
  have hcutO : canonicalCutPoint S K z k θ₀ ∈ O := by
    rw [← B.cut_eq θ₀]
    exact ⟨B.e.map_source (hYsource hcenter),
      by simpa only [B.e.left_inv (hYsource hcenter)] using hcenter⟩
  refine ⟨O, hO, hcutO, w,
    hglue.comp (B.inverse_smooth.mono inter_subset_left) (fun _ hx => hx.2), ?_, ?_⟩
  · intro x hx
    have hy := hYsub hx.1.2
    have hside : (B.e.symm x).1 < R :=
      (B.left_mem_iff _ (hQclosed hy)).mp (by
        simpa only [B.e.right_inv hx.1.1] using hx.2)
    simp only [w, Function.comp_apply, if_pos hside.le, B.e.right_inv hx.1.1]
  · intro x hx
    have hy := hYsub hx.1.2
    have hside : R < (B.e.symm x).1 :=
      (B.right_mem_iff _ (hQclosed hy)).mp (by
        simpa only [B.e.right_inv hx.1.1] using hx.2)
    simp only [w, Function.comp_apply, if_neg (not_le.mpr hside), B.e.right_inv hx.1.1]

end ContinuousFlexibility.Analysis
