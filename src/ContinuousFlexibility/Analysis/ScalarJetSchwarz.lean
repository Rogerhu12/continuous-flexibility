import ContinuousFlexibility.Analysis.ProjectiveJetSchwarz
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Scalar directional jets commute in every order

Two real parameters give an ordinary normed plane even when the source
is a projective space. The verified continuous directional differential
on that plane has a genuine Fréchet derivative, so Schwarz applies to
any fixed tail of a scalar tower. Differentiating the resulting overlap
identities moves the first direction to the last slot at every order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

private abbrev ScalarJetPlane := ℝ × ℝ

private def scalarJetLeft : ℝ →L[ℝ] (ScalarJetPlane →L[ℝ] ℝ) :=
  ContinuousLinearMap.smulRightL ℝ ScalarJetPlane ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)

private def scalarJetRight : ℝ →L[ℝ] (ScalarJetPlane →L[ℝ] ℝ) :=
  ContinuousLinearMap.smulRightL ℝ ScalarJetPlane ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] private theorem scalarJetLeft_apply (a : ℝ) (q : ScalarJetPlane) :
    scalarJetLeft a q = q.1 • a := by simp [scalarJetLeft]

@[simp] private theorem scalarJetRight_apply (a : ℝ) (q : ScalarJetPlane) :
    scalarJetRight a q = q.2 • a := by simp [scalarJetRight]

private def scalarJetLinear (a b : ℝ) : ScalarJetPlane →L[ℝ] ℝ :=
  scalarJetLeft a + scalarJetRight b

@[simp] private theorem scalarJetLinear_apply (a b : ℝ) (q : ScalarJetPlane) :
    scalarJetLinear a b q = q.1 • a + q.2 • b := by simp [scalarJetLinear]

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → ℝ}

private def scalarJetPlaneMap (u v : E) : ScalarJetPlane →L[ℝ] E where
  toFun q := q.1 • u + q.2 • v
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' a q := by simp [smul_add, smul_smul]
  cont := (continuous_fst.smul continuous_const).add
    (continuous_snd.smul continuous_const)

@[simp] private theorem scalarJetPlaneMap_apply (u v : E) (w : ScalarJetPlane) :
    scalarJetPlaneMap u v w = w.1 • u + w.2 • v := rfl

private def scalarJetPoint (x u v : E) (q : ScalarJetPlane) : E :=
  x + scalarJetPlaneMap u v q

@[simp] private theorem scalarJetPoint_zero (x u v : E) : scalarJetPoint x u v 0 = x := by
  simp [scalarJetPoint]

private theorem scalarJetPoint_line (x u v : E) (q w : ScalarJetPlane) (t : ℝ) :
    scalarJetPoint x u v (q + t • w) =
      scalarJetPoint x u v q + t • scalarJetPlaneMap u v w := by
  simp only [scalarJetPoint, map_add, map_smul]
  abel

private theorem continuous_scalarJetPoint (x u v : E) : Continuous (scalarJetPoint x u v) :=
  continuous_const.add (scalarJetPlaneMap u v).continuous

private theorem scalarJet_plane_continuous (J : SmoothDirections U f)
    (x u v : E) (n : ℕ) (vs : Fin n → E) :
    ContinuousOn (fun q => J.D n (scalarJetPoint x u v q) vs)
      ((scalarJetPoint x u v) ⁻¹' U) :=
  (J.continuous n).comp
    ((continuous_scalarJetPoint x u v).prodMk continuous_const).continuousOn
    (fun q hq => ⟨hq, mem_univ vs⟩)

private theorem scalarJet_plane_line (J : SmoothDirections U f)
    (x u v : E) (n : ℕ) (vs : Fin n → E) (q w : ScalarJetPlane)
    (hq : scalarJetPoint x u v q ∈ U) :
    HasLineDerivAt ℝ (fun p => J.D n (scalarJetPoint x u v p) vs)
      (J.D (n + 1) (scalarJetPoint x u v q) (Fin.cons (scalarJetPlaneMap u v w) vs)) q w := by
  change HasDerivAt (fun t : ℝ => J.D n (scalarJetPoint x u v (q + t • w)) vs) _ 0
  have heq : (fun t : ℝ => J.D n (scalarJetPoint x u v (q + t • w)) vs) =
      (fun t : ℝ => J.D n (scalarJetPoint x u v q + t • scalarJetPlaneMap u v w) vs) := by
    funext t
    rw [scalarJetPoint_line]
  rw [heq]
  exact hasDerivAt_iff_tendsto_slope_zero.mpr
    (J.derivative n (scalarJetPoint x u v q) hq vs (scalarJetPlaneMap u v w))

private theorem scalarJetLinear_head_apply (J : SmoothDirections U f)
    (n : ℕ) (x : E) (vs : Fin n → E) (u v : E) (w : ScalarJetPlane) :
    scalarJetLinear (J.D (n + 1) x (Fin.cons u vs))
      (J.D (n + 1) x (Fin.cons v vs)) w =
      J.D (n + 1) x (Fin.cons (scalarJetPlaneMap u v w) vs) := by
  let L := projectiveJetHeadLinear J.D n x vs
  have hL (y : E) : L y = J.D (n + 1) x (Fin.cons y vs) :=
    projectiveJetHeadLinear_apply J.D n x vs y
  calc
    scalarJetLinear (J.D (n + 1) x (Fin.cons u vs))
        (J.D (n + 1) x (Fin.cons v vs)) w = scalarJetLinear (L u) (L v) w := by
      rw [hL u, hL v]
    _ = L (scalarJetPlaneMap u v w) := by
      simp only [scalarJetLinear_apply, scalarJetPlaneMap_apply, map_add, map_smul]
    _ = _ := hL _

theorem SmoothDirections.front_two_symmetric (J : SmoothDirections U f)
    (hUc : Convex ℝ U) (n : ℕ) (x : E) (hx : x ∈ U)
    (u v : E) (vs : Fin n → E) :
    J.D (n + 2) x (Fin.cons u (Fin.cons v vs)) =
      J.D (n + 2) x (Fin.cons v (Fin.cons u vs)) := by
  let S : Set ScalarJetPlane := (scalarJetPoint x u v) ⁻¹' U
  have hSo : IsOpen S := J.open_domain.preimage (continuous_scalarJetPoint x u v)
  have hSc : Convex ℝ S :=
    (hUc.translate_preimage_right x).linear_preimage (scalarJetPlaneMap u v).toLinearMap
  have hS0 : (0 : ScalarJetPlane) ∈ S := by
    simpa only [S, mem_preimage, scalarJetPoint_zero] using hx
  let a : ScalarJetPlane → E → ℝ := fun q z =>
    J.D (n + 1) (scalarJetPoint x u v q) (Fin.cons z vs)
  let b : ScalarJetPlane → E → E → ℝ := fun q z w =>
    J.D (n + 2) (scalarJetPoint x u v q) (Fin.cons z (Fin.cons w vs))
  let D : ScalarJetPlane → ScalarJetPlane →L[ℝ] ℝ := fun q => scalarJetLinear (a q u) (a q v)
  let C0 : ScalarJetPlane → ScalarJetPlane →L[ℝ] ℝ := fun q => scalarJetLinear (b q u u) (b q v u)
  let C1 : ScalarJetPlane → ScalarJetPlane →L[ℝ] ℝ := fun q => scalarJetLinear (b q u v) (b q v v)
  let DD : ScalarJetPlane → ScalarJetPlane →L[ℝ] (ScalarJetPlane →L[ℝ] ℝ) := fun q =>
    scalarJetLeft.comp (C0 q) + scalarJetRight.comp (C1 q)
  have ha (z : E) : ContinuousOn (fun q => a q z) S :=
    scalarJet_plane_continuous J x u v (n + 1) (Fin.cons z vs)
  have hb (z w : E) : ContinuousOn (fun q => b q z w) S :=
    scalarJet_plane_continuous J x u v (n + 2) (Fin.cons z (Fin.cons w vs))
  have hD : ContinuousOn D S :=
    (scalarJetLeft.continuous.comp_continuousOn (ha u)).add
      (scalarJetRight.continuous.comp_continuousOn (ha v))
  have hC0 : ContinuousOn C0 S :=
    (scalarJetLeft.continuous.comp_continuousOn (hb u u)).add
      (scalarJetRight.continuous.comp_continuousOn (hb v u))
  have hC1 : ContinuousOn C1 S :=
    (scalarJetLeft.continuous.comp_continuousOn (hb u v)).add
      (scalarJetRight.continuous.comp_continuousOn (hb v v))
  have hDD : ContinuousOn DD S :=
    (continuousOn_const.clm_comp hC0).add (continuousOn_const.clm_comp hC1)
  have hDa : ∀ q ∈ S, ∀ z w,
      HasLineDerivAt ℝ (fun p => a p z)
        (scalarJetLinear (b q u z) (b q v z) w) q w := by
    intro q hq z w
    rw [show scalarJetLinear (b q u z) (b q v z) w =
      J.D (n + 2) (scalarJetPoint x u v q)
        (Fin.cons (scalarJetPlaneMap u v w) (Fin.cons z vs)) from
      scalarJetLinear_head_apply J (n + 1) (scalarJetPoint x u v q) (Fin.cons z vs) u v w]
    exact scalarJet_plane_line J x u v (n + 1) (Fin.cons z vs) q w hq
  have hDline : ∀ q ∈ S, ∀ w, HasLineDerivAt ℝ D (DD q w) q w := by
    intro q hq w
    have h0 : HasDerivAt (fun t : ℝ => a (q + t • w) u) (C0 q w) 0 := hDa q hq u w
    have h1 : HasDerivAt (fun t : ℝ => a (q + t • w) v) (C1 q w) 0 := hDa q hq v w
    have hd := (scalarJetLeft.hasFDerivAt.comp_hasDerivAt 0 h0).add
      (scalarJetRight.hasFDerivAt.comp_hasDerivAt 0 h1)
    have hfun :
        ((⇑scalarJetLeft ∘ fun t : ℝ => a (q + t • w) u) +
          (⇑scalarJetRight ∘ fun t : ℝ => a (q + t • w) v)) =
        (fun t : ℝ => scalarJetLeft (a (q + t • w) u) +
          scalarJetRight (a (q + t • w) v)) := by
      funext t
      simp only [Pi.add_apply, Function.comp_apply]
    rw [hfun] at hd
    change HasDerivAt (fun t : ℝ => scalarJetLeft (a (q + t • w) u) +
      scalarJetRight (a (q + t • w) v)) (DD q w) 0
    simpa only [DD, add_apply, ContinuousLinearMap.comp_apply] using hd
  have hFline : ∀ q ∈ S, ∀ w,
      HasLineDerivAt ℝ (fun p => J.D n (scalarJetPoint x u v p) vs) (D q w) q w := by
    intro q hq w
    rw [show D q w = J.D (n + 1) (scalarJetPoint x u v q)
      (Fin.cons (scalarJetPlaneMap u v w) vs) from
      scalarJetLinear_head_apply J n (scalarJetPoint x u v q) vs u v w]
    exact scalarJet_plane_line J x u v n vs q w hq
  have hF : ∀ q ∈ S,
      HasFDerivAt (fun p => J.D n (scalarJetPoint x u v p) vs) (D q) q :=
    fun q hq => hasFDerivAt_of_continuous_line_differential hSo hSc hD hFline hq
  have hD0 : HasFDerivAt D (DD 0) 0 :=
    hasFDerivAt_of_continuous_line_differential hSo hSc hDD hDline hS0
  have hFe : ∀ᶠ q in 𝓝 (0 : ScalarJetPlane),
      HasFDerivAt (fun p => J.D n (scalarJetPoint x u v p) vs) (D q) q := by
    filter_upwards [hSo.mem_nhds hS0] with q hq
    exact hF q hq
  have hs := second_derivative_symmetric_of_eventually_of_real hFe hD0
    ((1, 0) : ScalarJetPlane) ((0, 1) : ScalarJetPlane)
  simpa only [DD, C0, C1, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    scalarJetLeft_apply, scalarJetRight_apply, scalarJetLinear_apply,
    zero_smul, one_smul, add_zero, zero_add, b, scalarJetPoint_zero] using hs

theorem SmoothDirections.cons_eq_snoc (J : SmoothDirections U f) (hUc : Convex ℝ U) :
    ∀ n x, x ∈ U → ∀ (w : E) (v : Fin n → E),
      J.D (n + 1) x (Fin.cons w v) = J.D (n + 1) x (Fin.snoc v w) := by
  intro n
  induction n with
  | zero =>
    intro x hx w v
    apply congrArg (J.D 1 x)
    rw [Fin.snoc_zero]
    funext i
    fin_cases i
    rfl
  | succ n ih =>
    intro x hx w v
    let a := v 0
    let tail := Fin.tail v
    have hv : v = Fin.cons a tail := (Fin.cons_self_tail v).symm
    have hline : Tendsto (fun t : ℝ => x + t • a) (𝓝 (0 : ℝ)) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • a) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • a ∈ U :=
      hline.eventually (J.open_domain.mem_nhds hx)
    have heq : (fun t : ℝ => J.D (n + 1) (x + t • a) (Fin.cons w tail)) =ᶠ[𝓝 0]
        (fun t : ℝ => J.D (n + 1) (x + t • a) (Fin.snoc tail w)) :=
      hmem.mono (fun t ht => ih _ ht w tail)
    have hx0 : x + (0 : ℝ) • a ∈ U := by simpa only [zero_smul, add_zero] using hx
    have hL := J.hasDerivAt_line_jet x a (n + 1) (Fin.cons w tail) hx0
    have hR := J.hasDerivAt_line_jet x a (n + 1) (Fin.snoc tail w) hx0
    have hmove : J.D (n + 2) x (Fin.cons a (Fin.cons w tail)) =
        J.D (n + 2) x (Fin.cons a (Fin.snoc tail w)) := by
      simpa only [zero_smul, add_zero] using hL.unique (hR.congr_of_eventuallyEq heq)
    calc
      J.D (n + 1 + 1) x (Fin.cons w v) =
          J.D (n + 2) x (Fin.cons w (Fin.cons a tail)) :=
        congrArg (fun q => J.D (n + 2) x (Fin.cons w q)) hv
      _ = J.D (n + 2) x (Fin.cons a (Fin.cons w tail)) :=
        J.front_two_symmetric hUc n x hx w a tail
      _ = J.D (n + 2) x (Fin.cons a (Fin.snoc tail w)) := hmove
      _ = J.D (n + 2) x (Fin.snoc v w) := by
        have hs : Fin.snoc (α := fun _ : Fin (n + 2) => E) (Fin.cons a tail) w =
            Fin.snoc v w :=
          congrArg (fun q : Fin (n + 1) → E =>
            Fin.snoc (α := fun _ : Fin (n + 2) => E) q w) hv.symm
        exact congrArg (J.D (n + 2) x) ((Fin.cons_snoc_eq_snoc_cons a tail w).trans hs)

end ContinuousFlexibility.Statements
