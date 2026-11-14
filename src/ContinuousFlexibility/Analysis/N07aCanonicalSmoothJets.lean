module

public import ContinuousFlexibility.Analysis.N07aCanonicalSmoothDecode
public import ContinuousFlexibility.Analysis.N07aLocalizedFirstJets
public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus

/-!
# Classical jets of the canonical smooth decoder

The decoded smooth representative has exactly the original weak mixed
jets. The first derivative is identified by compact localization and the
true cylinder product rule; all higher derivatives follow by the weak
suffix identity and local commutation of smooth mixed derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_weakCanonicalMixed_unique (hm : K.left m < K.right m)
    {u v w : CanonicalL2 S K m} {a b : ℕ}
    (hv : N07aWeakCanonicalMixedDerivative S K m u v a b)
    (hw : N07aWeakCanonicalMixedDerivative S K m u w a b) : v = w := by
  have hzero : N07aWeakCanonicalMixedDerivative S K m v w 0 0 :=
    hv.suffix (by simpa only [Nat.add_zero] using hw)
  exact (n07aAngularWeak_unique m hm
    ((n07a_weakCanonicalMixed_zero_radial_iff v w 0).mp hzero)
    ((n07a_weakCanonicalMixed_zero_radial_iff v v 0).mp
      (n07a_weakCanonicalMixed_refl v))).symm

def n07aCanonicalSmoothJet (u : n07aCanonicalSmoothSpace S K m) (a b : ℕ) :
    n07aCanonicalSmoothSpace S K m :=
  ⟨(u.property a a le_rfl b).choose, fun n =>
    (u.property (n + a)).derivative (u.property a a le_rfl b).choose_spec⟩

theorem n07aCanonicalSmoothJet_weak (u : n07aCanonicalSmoothSpace S K m) (a b : ℕ) :
    N07aWeakCanonicalMixedDerivative S K m u.val
      (n07aCanonicalSmoothJet u a b).val a b :=
  (u.property a a le_rfl b).choose_spec

theorem n07aCanonicalSmoothDecode_first (hm : K.left m < K.right m)
    (u du : n07aCanonicalSmoothSpace S K m) (j : Fin 2)
    (hdu : N07aWeakCanonicalMixedDerivative S K m u.val du.val
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    EqOn (mixedDerivative (n07aFirstOrder j).1 (n07aFirstOrder j).2
      (n07aCanonicalSmoothDecode hm u)) (n07aCanonicalSmoothDecode hm du)
      (canonicalOpen S K m) := by
  let v := n07aCanonicalSmoothRepresentative hm u
  let w := n07aCanonicalSmoothRepresentative hm du
  have hv := n07aCanonicalSmoothRepresentative_properties hm u
  have hw := n07aCanonicalSmoothRepresentative_properties hm du
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  intro p hp
  obtain ⟨n, hn⟩ := n07aAngularIntervalCutoff_exists_one_nhds
    (K.left m) (K.right m) hm hp.1
  let χ := n07aCanonicalCutoff hm n
  have hχ : CanonicalTest S K m χ := n07aCanonicalCutoff_test hm n
  have hone : χ =ᶠ[𝓝 p] (fun _ => 1) :=
    continuous_fst.continuousAt.eventually hn
  obtain ⟨vχ, hvχ, hvχp, hvχae, hvχfirst⟩ :=
    n07a_exists_smooth_localizedCanonical_first hχ u.val u.property
  have heq : EqOn vχ (fun q => χ q * v q) (canonicalOpen S K m) := by
    apply n07a_canonical_periodic_eqOn_of_ae_eq hvχ.continuous.continuousOn
      (hχ.1.contDiffOn.mul hv.1).continuousOn hvχp (hχ.2.1.mul hv.2.1)
    filter_upwards [hvχae, hv.2.2.1] with q hq hqv
    exact hq.trans (congrArg (χ q * ·) hqv.symm)
  have hlocal : vχ =ᶠ[𝓝 p] v := by
    filter_upwards [hone, hU.mem_nhds hp] with q hq hqU
    exact (heq hqU).trans (by change χ q * v q = v q; rw [hq, one_mul])
  let a := (n07aFirstOrder j).1
  let b := (n07aFirstOrder j).2
  have hχzero : mixedDerivative a b χ p = 0 := by
    rw [n07a_mixedDerivative_eventuallyEq hone a b]
    fin_cases j <;> simp [a, b, n07aFirstOrder, mixedDerivative, iteratedDeriv_const]
  have hjet : EqOn (mixedDerivative a b vχ)
      (fun q => χ q * w q + mixedDerivative a b χ q * v q)
      (canonicalOpen S K m) := by
    apply n07a_canonical_periodic_eqOn_of_ae_eq
      (contDiff_mixedDerivative hvχ a b).continuous.continuousOn
      ((hχ.1.contDiffOn.mul hw.1).add
        ((contDiff_mixedDerivative hχ.1 a b).contDiffOn.mul hv.1)).continuousOn
      (n07a_canonicalCoefficient_derivative_periodic hvχp a b)
      ((hχ.2.1.mul hw.2.1).add
        ((n07a_canonicalCoefficient_derivative_periodic hχ.2.1 a b).mul hv.2.1))
    filter_upwards [hvχfirst j du.val hdu, hv.2.2.1, hw.2.2.1]
      with q hq hqv hqw
    exact hq.trans (congrArg₂ (· + ·) (congrArg (χ q * ·) hqw.symm)
      (congrArg (mixedDerivative a b χ q * ·) hqv.symm))
  have hpoint := hjet hp
  change mixedDerivative a b vχ p = χ p * w p + mixedDerivative a b χ p * v p at hpoint
  rw [hone.self_of_nhds, hχzero, one_mul, zero_mul, add_zero] at hpoint
  exact (n07a_mixedDerivative_eventuallyEq hlocal a b).symm.trans hpoint

/-- Every prescribed canonical weak mixed jet is the corresponding
classical derivative of the decoded smooth representative on the open piece. -/
theorem n07aCanonicalSmoothDecode_mixed (hm : K.left m < K.right m) (a b : ℕ)
    (u v : n07aCanonicalSmoothSpace S K m)
    (hv : N07aWeakCanonicalMixedDerivative S K m u.val v.val a b) :
    EqOn (mixedDerivative a b (n07aCanonicalSmoothDecode hm u))
      (n07aCanonicalSmoothDecode hm v) (canonicalOpen S K m) := by
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  induction a generalizing b u v with
  | zero =>
    induction b generalizing u v with
    | zero =>
      have he : u = v := Subtype.ext
        (n07a_weakCanonicalMixed_unique hm (n07a_weakCanonicalMixed_refl u.val) hv)
      subst v
      simp only [spaces_mixedDerivative_zero]
      exact fun _ _ => rfl
    | succ b ih =>
      let w := n07aCanonicalSmoothJet u 0 1
      have hw := n07aCanonicalSmoothJet_weak u 0 1
      have hwv : N07aWeakCanonicalMixedDerivative S K m w.val v.val 0 b :=
        hw.suffix (by simpa only [Nat.zero_add, Nat.one_add] using hv)
      have hfirst : EqOn (mixedDerivative 0 1 (n07aCanonicalSmoothDecode hm u))
          (n07aCanonicalSmoothDecode hm w) (canonicalOpen S K m) := by
        simpa [n07aFirstOrder] using n07aCanonicalSmoothDecode_first hm u w 1 hw
      intro p hp
      calc
        mixedDerivative 0 (b + 1) (n07aCanonicalSmoothDecode hm u) p =
            mixedDerivative 0 b
              (mixedDerivative 0 1 (n07aCanonicalSmoothDecode hm u)) p := by
          symm
          exact n07a_mixedDerivative_mixedDerivative_on hU
            (n07aCanonicalSmoothRepresentative_properties hm u).1 0 b 0 1 hp
        _ = mixedDerivative 0 b (n07aCanonicalSmoothDecode hm w) p :=
          n07a_mixedDerivative_eqOn hU hfirst 0 b hp
        _ = n07aCanonicalSmoothDecode hm v p := ih w v hwv hp
  | succ a ih =>
    let w := n07aCanonicalSmoothJet u 1 0
    have hw := n07aCanonicalSmoothJet_weak u 1 0
    have hwv : N07aWeakCanonicalMixedDerivative S K m w.val v.val a b :=
      hw.suffix (by simpa only [Nat.zero_add, Nat.one_add] using hv)
    have hfirst : EqOn (mixedDerivative 1 0 (n07aCanonicalSmoothDecode hm u))
        (n07aCanonicalSmoothDecode hm w) (canonicalOpen S K m) := by
      simpa [n07aFirstOrder] using
        n07aCanonicalSmoothDecode_first hm u w 0 hw
    intro p hp
    calc
      mixedDerivative (a + 1) b (n07aCanonicalSmoothDecode hm u) p =
          mixedDerivative a b
            (mixedDerivative 1 0 (n07aCanonicalSmoothDecode hm u)) p := by
        symm
        exact n07a_mixedDerivative_mixedDerivative_on hU
          (n07aCanonicalSmoothRepresentative_properties hm u).1 a b 1 0 hp
      _ = mixedDerivative a b (n07aCanonicalSmoothDecode hm w) p :=
        n07a_mixedDerivative_eqOn hU hfirst a b hp
      _ = n07aCanonicalSmoothDecode hm v p := ih b w v hwv hp

theorem n07aCanonicalSmoothDecode_mixed_ae (hm : K.left m < K.right m) (a b : ℕ)
    (u : n07aCanonicalSmoothSpace S K m) (v : CanonicalL2 S K m)
    (hv : N07aWeakCanonicalMixedDerivative S K m u.val v a b) :
    mixedDerivative a b (n07aCanonicalSmoothDecode hm u)
      =ᵐ[canonicalMeasure S K m] v := by
  let w : n07aCanonicalSmoothSpace S K m :=
    ⟨v, fun n => (u.property (n + a)).derivative hv⟩
  have hw := n07aCanonicalSmoothRepresentative_properties hm w
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem, hw.2.2.1] with p hp hpw
  exact (n07aCanonicalSmoothDecode_mixed hm a b u w hv ⟨hp.1, mem_univ _⟩).trans hpw

end ContinuousFlexibility.Analysis
