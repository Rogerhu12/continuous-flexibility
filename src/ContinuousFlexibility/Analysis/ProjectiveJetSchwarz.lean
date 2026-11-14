module

public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of the actual second projective jet

The Fréchet source keeps its original projective topology. We restrict
only the two real parameters to a genuine normed plane, then work in
each Banach output coordinate. A segment-FTC estimate turns the
verified directional derivatives of the restriction into actual
Fréchet derivatives. The ordinary Banach Schwarz theorem then applies.

No symmetry assumption on the candidate jets is used. Higher-order
permutation symmetry and all-order composition remain separate results.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Asymptotics MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section NormedParameter

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- On an honest normed parameter space, the segment FTC and continuity
in operator norm upgrade the verified line differential to a genuine
Fréchet differential. This is used only for finite real parameters. -/
theorem hasFDerivAt_of_continuous_line_differential
    {f : X → Y} {D : X → X →L[ℝ] Y} {U : Set X}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hD : ContinuousOn D U)
    (hf : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ f (D x v) x v)
    {x : X} (hx : x ∈ U) : HasFDerivAt f (D x) x := by
  have hj : ContinuousOn (fun p : X × X => D p.1 p.2) (U ×ˢ univ) :=
    (hD.comp continuous_fst.continuousOn
      (fun p hp => hp.1)).clm_apply continuous_snd.continuousOn
  have hDx : ContinuousAt D x := hD.continuousAt (hU.mem_nhds hx)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hnear : {y : X | ‖D y - D x‖ < ε} ∈ 𝓝 x := by
    have hn : Tendsto (fun y : X => ‖D y - D x‖) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hDx.sub_const (D x)).norm
    exact hn (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hadd : Tendsto (fun h : X => x + h) (𝓝 (0 : X)) (𝓝 x) := by
    have ha : Continuous (fun h : X => x + h) := continuous_const.add continuous_id
    simpa only [add_zero] using ha.tendsto (0 : X)
  have hin := hadd.eventually (hU.mem_nhds hx)
  filter_upwards [Metric.ball_mem_nhds (0 : X) hδ, hin] with h hh hy
  have hhn : ‖h‖ < δ := by simpa using hh
  have hsub : x + h - x = h := by abel
  have hi : IntervalIntegrable (fun s : ℝ => D (x + s • h) h) volume 0 1 := by
    simpa only [hsub] using
      (continuousOn_bastiani_segment hUc hj hx hy h).intervalIntegrable_of_Icc
        (μ := volume) zero_le_one
  have hc : IntervalIntegrable (fun _ : ℝ => D x h) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hft := bastiani_segment_integral hUc hj hf hx hy
  simp only [hsub] at hft
  have he : f (x + h) - f x - D x h =
      ∫ s in (0 : ℝ)..1, (D (x + s • h) - D x) h := by
    rw [← hft]
    simpa only [sub_apply, intervalIntegral.integral_const,
      sub_zero, one_smul] using (intervalIntegral.integral_sub hi hc).symm
  rw [he]
  have hb : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖(D (x + s • h) - D x) h‖ ≤ ε * ‖h‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      simp only [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hop : ‖D (x + s • h) - D x‖ < ε := by
      apply hball
      change dist (x + s • h) x < δ
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs'.1]
      exact (mul_le_of_le_one_left (norm_nonneg h) hs'.2).trans_lt hhn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hop.le (norm_nonneg h))
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

end NormedParameter

private abbrev SchwarzPlane := ℝ × ℝ

section PlaneOperators

variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private def schwarzLeft : Y →L[ℝ] (SchwarzPlane →L[ℝ] Y) :=
  ContinuousLinearMap.smulRightL ℝ SchwarzPlane Y (ContinuousLinearMap.fst ℝ ℝ ℝ)

private def schwarzRight : Y →L[ℝ] (SchwarzPlane →L[ℝ] Y) :=
  ContinuousLinearMap.smulRightL ℝ SchwarzPlane Y (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] private theorem schwarzLeft_apply (a : Y) (q : SchwarzPlane) :
    schwarzLeft Y a q = q.1 • a := by simp [schwarzLeft]

@[simp] private theorem schwarzRight_apply (a : Y) (q : SchwarzPlane) :
    schwarzRight Y a q = q.2 • a := by simp [schwarzRight]

private def schwarzLinear (a b : Y) : SchwarzPlane →L[ℝ] Y :=
  schwarzLeft Y a + schwarzRight Y b

@[simp] private theorem schwarzLinear_apply (a b : Y) (q : SchwarzPlane) :
    schwarzLinear Y a b q = q.1 • a + q.2 • b := by simp [schwarzLinear]

end PlaneOperators

section AffinePlane

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The plane is normed; its projective target is not given a norm. -/
private def schwarzPlaneMap (u v : X) : SchwarzPlane →L[ℝ] X where
  toFun q := q.1 • u + q.2 • v
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' := by
    intro a q
    simp [smul_add, smul_smul]
  cont := (continuous_fst.smul continuous_const).add
    (continuous_snd.smul continuous_const)

@[simp] private theorem schwarzPlaneMap_apply (u v : X) (q : SchwarzPlane) :
    schwarzPlaneMap u v q = q.1 • u + q.2 • v := rfl

private def schwarzPoint (x u v : X) (q : SchwarzPlane) : X :=
  x + schwarzPlaneMap u v q

@[simp] private theorem schwarzPoint_zero (x u v : X) :
    schwarzPoint x u v 0 = x := by simp [schwarzPoint]

private theorem schwarzPoint_line (x u v : X) (q w : SchwarzPlane) (s : ℝ) :
    schwarzPoint x u v (q + s • w) =
      schwarzPoint x u v q + s • schwarzPlaneMap u v w := by
  simp only [schwarzPoint, map_add, map_smul]
  abel

private theorem continuous_schwarzPoint (x u v : X) :
    Continuous (schwarzPoint x u v) :=
  continuous_const.add (schwarzPlaneMap u v).continuous

end AffinePlane

section Projective

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
variable {bond : ∀ n, E (n + 1) →L[ℝ] E n}
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

local notation "X" => ProjectiveLimit E bond
local notation "Z" => ProjectiveLimit F fbond

omit [∀ n, CompleteSpace (F n)] in
private theorem continuousOn_schwarz_jet_coordinate
    {f : X → Z} {J : ProjectiveJetFamily X Z} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (x u v : X) (n k : ℕ)
    (vs : Fin n → X) :
    ContinuousOn (fun q : SchwarzPlane =>
      (projectiveCoordinate F fbond k) (J n (schwarzPoint x u v q) vs))
      ((schwarzPoint x u v) ⁻¹' U) := by
  have hp : Continuous (fun q : SchwarzPlane => (schwarzPoint x u v q, vs)) :=
    (continuous_schwarzPoint x u v).prodMk continuous_const
  have hm : MapsTo (fun q : SchwarzPlane => (schwarzPoint x u v q, vs))
      ((schwarzPoint x u v) ⁻¹' U) (U ×ˢ univ) :=
    fun _ hq => ⟨hq, mem_univ vs⟩
  have h : ContinuousOn (fun q : SchwarzPlane => J n (schwarzPoint x u v q) vs)
      ((schwarzPoint x u v) ⁻¹' U) :=
    (hJ.2.1 n).comp' hp.continuousOn hm
  exact (projectiveCoordinate F fbond k).continuous.comp_continuousOn' h

omit [∀ n, CompleteSpace (F n)] in
private theorem hasLineDerivAt_schwarz_jet_coordinate
    {f : X → Z} {J : ProjectiveJetFamily X Z} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (x u v : X) (n k : ℕ)
    (vs : Fin n → X) (q w : SchwarzPlane)
    (hq : schwarzPoint x u v q ∈ U) :
    HasLineDerivAt ℝ
      (fun p : SchwarzPlane =>
        (projectiveCoordinate F fbond k) (J n (schwarzPoint x u v p) vs))
      ((projectiveCoordinate F fbond k) (J (n + 1) (schwarzPoint x u v q)
        (Fin.cons (schwarzPlaneMap u v w) vs))) q w := by
  have h := (hasProjectiveLineDerivAt_iff_levels (E := F) (bond := fbond)
    (fun y : X => J n y vs)
    (J (n + 1) (schwarzPoint x u v q) (Fin.cons (schwarzPlaneMap u v w) vs))
    (schwarzPoint x u v q) (schwarzPlaneMap u v w)).mp
    (hJ.2.2 n (schwarzPoint x u v q) hq (schwarzPlaneMap u v w) vs) k
  change HasDerivAt
    (fun s : ℝ => (J n (schwarzPoint x u v (q + s • w)) vs).1 k) _ 0
  simpa only [schwarzPoint_line, projectiveCoordinate_apply] using h

omit [∀ n, CompleteSpace (F n)] in
private theorem schwarzLinear_projective_apply (k : ℕ) (T : X →L[ℝ] Z)
    (u v : X) (w : SchwarzPlane) :
    schwarzLinear (F k) ((T u).1 k) ((T v).1 k) w =
      (T (schwarzPlaneMap u v w)).1 k := by
  let P := projectiveCoordinate F fbond k
  change schwarzLinear (F k) (P (T u)) (P (T v)) w =
    P (T (schwarzPlaneMap u v w))
  simp only [schwarzLinear_apply, schwarzPlaneMap_apply, map_add, map_smul]

/-- The genuine second projective jet is symmetric, proved through real
two-dimensional restrictions in every Banach output coordinate. -/
theorem HasProjectiveJetsOn.second_symmetric
    {f : X → Z} {J : ProjectiveJetFamily X Z} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U) (hUc : Convex ℝ U)
    {x : X} (hx : x ∈ U) (u v : X) :
    J 2 x (Fin.cons u (Fin.cons v Fin.elim0)) =
      J 2 x (Fin.cons v (Fin.cons u Fin.elim0)) := by
  apply Subtype.ext
  funext k
  let P := projectiveCoordinate F fbond k
  let S : Set SchwarzPlane := (schwarzPoint x u v) ⁻¹' U
  have hSo : IsOpen S := hU.preimage (continuous_schwarzPoint x u v)
  have hSc : Convex ℝ S :=
    (hUc.translate_preimage_right x).linear_preimage (schwarzPlaneMap u v).toLinearMap
  have hS0 : (0 : SchwarzPlane) ∈ S := by simpa only [S, mem_preimage, schwarzPoint_zero] using hx
  let A := schwarzLeft (F k)
  let B := schwarzRight (F k)
  let a : SchwarzPlane → X → F k := fun q z =>
    P (projectiveJetHeadLinear J 0 (schwarzPoint x u v q) Fin.elim0 z)
  let b : SchwarzPlane → X → X → F k := fun q z w =>
    P (projectiveJetHeadLinear J 1 (schwarzPoint x u v q)
      (Fin.cons w Fin.elim0) z)
  let D : SchwarzPlane → SchwarzPlane →L[ℝ] F k := fun q =>
    schwarzLinear (F k) (a q u) (a q v)
  let C0 : SchwarzPlane → SchwarzPlane →L[ℝ] F k := fun q =>
    schwarzLinear (F k) (b q u u) (b q v u)
  let C1 : SchwarzPlane → SchwarzPlane →L[ℝ] F k := fun q =>
    schwarzLinear (F k) (b q u v) (b q v v)
  let DD : SchwarzPlane → SchwarzPlane →L[ℝ] (SchwarzPlane →L[ℝ] F k) := fun q =>
    A.comp (C0 q) + B.comp (C1 q)
  have ha : ∀ z : X, ContinuousOn (fun q => a q z) S := by
    intro z
    simpa only [a, P, projectiveJetHeadLinear_apply] using
      continuousOn_schwarz_jet_coordinate (E := E) (F := F) (bond := bond) (fbond := fbond)
        hJ x u v 1 k (Fin.cons z Fin.elim0)
  have hb : ∀ z w : X, ContinuousOn (fun q => b q z w) S := by
    intro z w
    simpa only [b, P, projectiveJetHeadLinear_apply] using
      continuousOn_schwarz_jet_coordinate (E := E) (F := F) (bond := bond) (fbond := fbond)
        hJ x u v 2 k
        (Fin.cons z (Fin.cons w Fin.elim0))
  have hD : ContinuousOn D S :=
    (A.continuous.comp_continuousOn (ha u)).add
      (B.continuous.comp_continuousOn (ha v))
  have hC0 : ContinuousOn C0 S :=
    (A.continuous.comp_continuousOn (hb u u)).add
      (B.continuous.comp_continuousOn (hb v u))
  have hC1 : ContinuousOn C1 S :=
    (A.continuous.comp_continuousOn (hb u v)).add
      (B.continuous.comp_continuousOn (hb v v))
  have hDD : ContinuousOn DD S :=
    (continuousOn_const.clm_comp hC0).add (continuousOn_const.clm_comp hC1)
  have hDa : ∀ q ∈ S, ∀ z w,
      HasLineDerivAt ℝ (fun p : SchwarzPlane => a p z)
        (schwarzLinear (F k) (b q u z) (b q v z) w) q w := by
    intro q hq z w
    have hd := hasLineDerivAt_schwarz_jet_coordinate
      (E := E) (F := F) (bond := bond) (fbond := fbond) hJ x u v 1 k
      (Fin.cons z Fin.elim0) q w hq
    have he := schwarzLinear_projective_apply (E := E) (F := F) (bond := bond) (fbond := fbond) k
      (projectiveJetHeadLinear J 1 (schwarzPoint x u v q)
        (Fin.cons z Fin.elim0)) u v w
    change HasLineDerivAt ℝ (fun p : SchwarzPlane => a p z)
      (schwarzLinear (F k)
        ((projectiveJetHeadLinear J 1 (schwarzPoint x u v q) (Fin.cons z Fin.elim0) u).1 k)
        ((projectiveJetHeadLinear J 1 (schwarzPoint x u v q) (Fin.cons z Fin.elim0) v).1 k) w)
      q w
    rw [he]
    simpa only [a, P, projectiveJetHeadLinear_apply, projectiveCoordinate_apply] using hd
  have hDline : ∀ q ∈ S, ∀ w, HasLineDerivAt ℝ D (DD q w) q w := by
    intro q hq w
    have h0 : HasDerivAt (fun s : ℝ => a (q + s • w) u) (C0 q w) 0 := hDa q hq u w
    have h1 : HasDerivAt (fun s : ℝ => a (q + s • w) v) (C1 q w) 0 := hDa q hq v w
    have hd := (A.hasFDerivAt.comp_hasDerivAt 0 h0).add
      (B.hasFDerivAt.comp_hasDerivAt 0 h1)
    have hfun :
        ((⇑A ∘ fun s : ℝ => a (q + s • w) u) + (⇑B ∘ fun s : ℝ => a (q + s • w) v)) =
          (fun s : ℝ => A (a (q + s • w) u) + B (a (q + s • w) v)) := by
      funext s
      simp only [Pi.add_apply, Function.comp_apply]
    rw [hfun] at hd
    change HasDerivAt (fun s : ℝ => A (a (q + s • w) u) + B (a (q + s • w) v))
      (DD q w) 0
    simpa only [DD, add_apply, ContinuousLinearMap.comp_apply] using hd
  have hFline : ∀ q ∈ S, ∀ w,
      HasLineDerivAt ℝ (fun p : SchwarzPlane => P (f (schwarzPoint x u v p)))
        (D q w) q w := by
    intro q hq w
    have hd := (hasProjectiveLineDerivAt_iff_levels (E := F) (bond := fbond) f
      (projectiveFirstJetValue J (schwarzPoint x u v q) (schwarzPlaneMap u v w))
      (schwarzPoint x u v q) (schwarzPlaneMap u v w)).mp
      (hJ.hasLineDerivAt hU hq (schwarzPlaneMap u v w)) k
    have he := schwarzLinear_projective_apply (E := E) (F := F) (bond := bond) (fbond := fbond) k
      (projectiveJetHeadLinear J 0 (schwarzPoint x u v q) Fin.elim0) u v w
    change HasDerivAt
      (fun s : ℝ => P (f (schwarzPoint x u v (q + s • w)))) (D q w) 0
    have hvalue : D q w =
        (projectiveFirstJetValue J (schwarzPoint x u v q) (schwarzPlaneMap u v w)).1 k := by
      calc
        D q w =
            (projectiveJetHeadLinear J 0 (schwarzPoint x u v q) Fin.elim0
              (schwarzPlaneMap u v w)).1 k := he
        _ = _ := by simp only [projectiveJetHeadLinear_apply, projectiveFirstJetValue]
    rw [hvalue]
    simpa only [schwarzPoint_line, P, projectiveCoordinate_apply] using hd
  have hF : ∀ q ∈ S,
      HasFDerivAt (fun p : SchwarzPlane => P (f (schwarzPoint x u v p))) (D q) q :=
    fun q hq => hasFDerivAt_of_continuous_line_differential hSo hSc hD hFline hq
  have hD0 : HasFDerivAt D (DD 0) 0 :=
    hasFDerivAt_of_continuous_line_differential hSo hSc hDD hDline hS0
  have hFe : ∀ᶠ q in 𝓝 (0 : SchwarzPlane),
      HasFDerivAt (fun p : SchwarzPlane => P (f (schwarzPoint x u v p))) (D q) q := by
    filter_upwards [hSo.mem_nhds hS0] with q hq
    exact hF q hq
  have hs := second_derivative_symmetric_of_eventually_of_real hFe hD0
      ((1, 0) : SchwarzPlane) ((0, 1) : SchwarzPlane)
  simpa only [DD, A, B, C0, C1, add_apply, ContinuousLinearMap.comp_apply,
    schwarzLeft_apply, schwarzRight_apply, schwarzLinear_apply,
    zero_smul, one_smul, add_zero, zero_add, b, P, projectiveJetHeadLinear_apply,
    schwarzPoint_zero, projectiveCoordinate_apply] using hs

end Projective

end ContinuousFlexibility.Analysis
