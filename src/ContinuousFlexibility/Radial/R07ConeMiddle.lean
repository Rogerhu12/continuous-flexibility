module

public import ContinuousFlexibility.Radial.R07ConeGeometry

/-!
# Two genuine cone heads inside the finite middle

Each cone has a prescribed positive height at its outer join. The two
outer joins can be arbitrarily short, while a separate positive bridge
connects the cones. All four seams match full smooth germs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

structure R07ConeMiddleData where
  middle : ℝ → ℝ
  cut : Bool → ℝ
  join : Bool → ℝ
  scale : Bool → ℝ

def R07ConeMiddleSpecification (a b WL WR η : ℝ) (f : ℝ → ℝ)
    (H : R07ConeMiddleData) : Prop :=
  ContDiff ℝ ∞ H.middle ∧ (∀ x, 0 < H.middle x) ∧
    (H.middle =ᶠ[𝓝 a] f) ∧ (H.middle =ᶠ[𝓝 b] f) ∧
    (∀ x ∈ Icc a b, 0 < deriv H.middle x) ∧
    a < H.join false ∧ H.join false < H.cut false ∧ H.cut false < H.cut true ∧
    H.cut true < H.join true ∧ H.join true < b ∧
    H.join false - a < η ∧ b - H.join true < η ∧
    (∀ side, 0 < H.scale side) ∧
    (∀ side x, x ∈ uIcc (H.cut side) (H.join side) →
      H.middle =ᶠ[𝓝 x] fun r => H.scale side * r) ∧
    H.middle (H.join false) = WL ∧ H.middle (H.join true) = WR

theorem exists_r07_cone_middle {a b WL WR η : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a) (hab : a < b) (hf : ContDiff ℝ ∞ f) (hfp : ∀ x, 0 < f x)
    (hfd : ∀ x ∈ Icc a b, 0 < deriv f x)
    (hWL : f a < WL) (hW : WL < WR) (hWR : WR < f b) (hη : 0 < η) :
    ∃ H : R07ConeMiddleData, R07ConeMiddleSpecification a b WL WR η f H := by
  have hWL₀ : 0 < WL := (hfp a).trans hWL
  have hWR₀ : 0 < WR := hWL₀.trans hW
  obtain ⟨jL, cL, cR, jR, hajL, hjLcL, hcLcR, hcRjR, hjRb, hshortL, hshortR, hgap⟩ :=
    exists_r07_cone_positions ha hab hWL₀ hW hη
  have hjLjR : jL < jR := hjLcL.trans (hcLcR.trans hcRjR)
  have hjL₀ : 0 < jL := ha.trans hajL
  have hjR₀ : 0 < jR := hjL₀.trans hjLjR
  have hcLmem : cL ∈ Icc a b :=
    ⟨(hajL.trans hjLcL).le, (hcLcR.trans (hcRjR.trans hjRb)).le⟩
  have hcRmem : cR ∈ Icc a b :=
    ⟨(hajL.trans (hjLcL.trans hcLcR)).le, (hcRjR.trans hjRb).le⟩
  have hjLmem : jL ∈ Icc a b := ⟨hajL.le, (hjLjR.trans hjRb).le⟩
  have hjRmem : jR ∈ Icc a b := ⟨(hajL.trans hjLjR).le, hjRb.le⟩
  obtain ⟨R, hR, hRp, hRg⟩ := exists_r07_smooth_radius_germ ha hab.le
  let sL := WL / jL
  let sR := WR / jR
  let CL : ℝ → ℝ := fun x => sL * R x
  let CR : ℝ → ℝ := fun x => sR * R x
  have hsL : 0 < sL := div_pos hWL₀ hjL₀
  have hsR : 0 < sR := div_pos hWR₀ hjR₀
  have hCL : ContDiff ℝ ∞ CL := contDiff_const.mul hR
  have hCR : ContDiff ℝ ∞ CR := contDiff_const.mul hR
  have hCLp : ∀ x, 0 < CL x := fun x => mul_pos hsL (hRp x)
  have hCRp : ∀ x, 0 < CR x := fun x => mul_pos hsR (hRp x)
  have hCg (s : ℝ) (x : ℝ) (hx : x ∈ Icc a b) :
      (fun r => s * R r) =ᶠ[𝓝 x] fun r => s * r :=
    (hRg x hx).fun_comp (fun y => s * y)
  have hCd (s : ℝ) (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun r => s * R r) x = s := by
    rw [(hCg s x hx).deriv_eq]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul s).deriv
  have hCLj : CL jL = WL := by
    change sL * R jL = WL
    rw [(hCg sL jL hjLmem).eq_of_nhds]
    exact div_mul_cancel₀ _ hjL₀.ne'
  have hCRj : CR jR = WR := by
    change sR * R jR = WR
    rw [(hCg sR jR hjRmem).eq_of_nhds]
    exact div_mul_cancel₀ _ hjR₀.ne'
  obtain ⟨L, hL, hLp, hLa, hLj, hLd⟩ := exists_r07_positive_bridge hajL hf hCL hfp hCLp
    (hfd a (left_mem_Icc.mpr hab.le)) (by rw [hCd sL jL hjLmem]; exact hsL)
    (by rw [hCLj]; exact hWL)
  obtain ⟨B, hB, hBp, hBL, hBR, hBd⟩ := exists_r07_positive_bridge hcLcR hCL hCR hCLp hCRp
    (by rw [hCd sL cL hcLmem]; exact hsL) (by rw [hCd sR cR hcRmem]; exact hsR)
    (by
      change sL * R cL < sR * R cR
      rw [(hCg sL cL hcLmem).eq_of_nhds, (hCg sR cR hcRmem).eq_of_nhds]
      exact hgap)
  obtain ⟨U, hU, hUp, hUj, hUb, hUd⟩ := exists_r07_positive_bridge hjRb hCR hf hCRp hfp
    (by rw [hCd sR jR hjRmem]; exact hsR) (hfd b (right_mem_Icc.mpr hab.le))
    (by rw [hCRj]; exact hWR)
  let P₃ := morseGlueCut jR CR U
  have hP₃ := r07_positive_glue (a := cR) hCR hU hCRp hUp hUj.symm
    (fun x hx => by rw [hCd sR x ⟨hcRmem.1.trans hx.1, hx.2.trans hjRmem.2⟩]; exact hsR) hUd
  have hmeetR : B =ᶠ[𝓝 cR] P₃ :=
    hBR.trans (morseGlueCut_eventually_left hUj.symm hcRjR.le).symm
  let P₂ := morseGlueCut cR B P₃
  have hP₂ := r07_positive_glue hB hP₃.1 hBp hP₃.2.1 hmeetR hBd hP₃.2.2
  have hmeetL : CL =ᶠ[𝓝 cL] P₂ :=
    hBL.symm.trans (morseGlueCut_eventually_left hmeetR hcLcR.le).symm
  let P₁ := morseGlueCut cL CL P₂
  have hP₁ := r07_positive_glue (a := jL) hCL hP₂.1 hCLp hP₂.2.1 hmeetL
    (fun x hx => by rw [hCd sL x ⟨hjLmem.1.trans hx.1, hx.2.trans hcLmem.2⟩]; exact hsL) hP₂.2.2
  have hmeet0 : L =ᶠ[𝓝 jL] P₁ :=
    hLj.trans (morseGlueCut_eventually_left hmeetL hjLcL.le).symm
  let M := morseGlueCut jL L P₁
  have hM := r07_positive_glue hL hP₁.1 hLp hP₁.2.1 hmeet0 hLd hP₁.2.2
  have hMa : M =ᶠ[𝓝 a] f := (morseGlueCut_eventually_left hmeet0 hajL.le).trans hLa
  have hMb : M =ᶠ[𝓝 b] f :=
    (morseGlueCut_eventually_right hmeet0 hjLmem.2).trans
      ((morseGlueCut_eventually_right hmeetL hcLmem.2).trans
        ((morseGlueCut_eventually_right hmeetR hcRmem.2).trans
          ((morseGlueCut_eventually_right hUj.symm hjRb.le).trans hUb)))
  have hML (x : ℝ) (hx : x ∈ Icc jL cL) : M =ᶠ[𝓝 x] fun r => sL * r :=
    (morseGlueCut_eventually_right hmeet0 hx.1).trans
      ((morseGlueCut_eventually_left hmeetL hx.2).trans
        (hCg sL x ⟨hjLmem.1.trans hx.1, hx.2.trans hcLmem.2⟩))
  have hMR (x : ℝ) (hx : x ∈ Icc cR jR) : M =ᶠ[𝓝 x] fun r => sR * r :=
    (morseGlueCut_eventually_right hmeet0 ((hjLcL.trans hcLcR).le.trans hx.1)).trans
      ((morseGlueCut_eventually_right hmeetL (hcLcR.le.trans hx.1)).trans
        ((morseGlueCut_eventually_right hmeetR hx.1).trans
          ((morseGlueCut_eventually_left hUj.symm hx.2).trans
            (hCg sR x ⟨hcRmem.1.trans hx.1, hx.2.trans hjRmem.2⟩))))
  let H : R07ConeMiddleData := ⟨M, (fun side => if side then cR else cL),
    (fun side => if side then jR else jL), (fun side => if side then sR else sL)⟩
  refine ⟨H, hM.1, hM.2.1, hMa, hMb, hM.2.2,
    hajL, hjLcL, hcLcR, hcRjR, hjRb, hshortL, hshortR, ?_, ?_, ?_, ?_⟩
  · intro side
    cases side
    · exact hsL
    · exact hsR
  · intro side x hx
    cases side
    · change x ∈ uIcc cL jL at hx
      rw [uIcc_of_ge hjLcL.le] at hx
      exact hML x hx
    · change x ∈ uIcc cR jR at hx
      rw [uIcc_of_le hcRjR.le] at hx
      exact hMR x hx
  · change M jL = WL
    rw [(hML jL (left_mem_Icc.mpr hjLcL.le)).eq_of_nhds]
    exact div_mul_cancel₀ _ hjL₀.ne'
  · change M jR = WR
    rw [(hMR jR (right_mem_Icc.mpr hcRjR.le)).eq_of_nhds]
    exact div_mul_cancel₀ _ hjR₀.ne'

end ContinuousFlexibility.Radial
