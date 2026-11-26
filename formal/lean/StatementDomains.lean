import ObservedReversal
import CycleExpansion
import Mathlib.Data.EReal.Basic

open scoped BigOperators
open IncrementCycles
open IncrementCycles.S

namespace StatementDomains
noncomputable section

def logDomain (J : Pair) : Prop := ∀ i j, i ≠ j → 0 < J i j

theorem log_arguments_positive (J : Pair) (h : logDomain J) :
    0 < numerator J ∧ 0 < denominator J ∧ 0 < numerator J / denominator J := by
  have hn : 0 < numerator J := mul_pos (mul_pos (h E P (by decide)) (h P R (by decide))) (h R E (by decide))
  have hd : 0 < denominator J := mul_pos (mul_pos (h P E (by decide)) (h R P (by decide))) (h E R (by decide))
  exact ⟨hn,hd,div_pos hn hd⟩

theorem affinity_positive_domain (J : Pair) (h : logDomain J) :
    logDomain (reversePair J) ∧ affinity (reversePair J) = affinity J := by
  refine ⟨?_,(affinity_even J).2.2⟩
  intro i j hne
  apply h
  intro he
  apply hne
  have hr : flip (flip j) = flip (flip i) := congrArg IncrementCycles.flip he
  simpa using hr.symm

theorem reversible_example_domain : logDomain reversibleExample := by
  intro i j hij
  cases i <;> cases j <;> try contradiction
  all_goals norm_num [reversibleExample,threeSum,signStep,chainPi,chainStep]

theorem ring_example_domain : logDomain iidRing ∧ stationary iidRing ∧ mass iidRing = 1 := by
  refine ⟨?_,?_,?_⟩
  · intro i j _
    cases i <;> cases j <;> norm_num [iidRing,ringP]
  · intro i
    cases i <;> norm_num [row,col,iidRing,ringP]
  · norm_num [mass,row,iidRing,ringP]

theorem full_support_affine_witness :
    stationary (fun _ _ => (1/9 : ℝ)) ∧ mass (fun _ _ => (1/9 : ℝ)) = 1 ∧
    (∀ _ _ : S, 0 < (1/9 : ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · intro s
    rfl
  · norm_num [mass,row]
  · intro i j
    norm_num

def extendedBlockKL {I : Type*} [Fintype I] (p q : I → ℝ) : EReal :=
  open Classical in
  if ∃ i, 0 < p i ∧ q i = 0 then ⊤ else
    ((∑ i, if p i = 0 then 0 else p i * Real.log (p i/q i) : ℝ) : EReal)

theorem KL_missing_support {I : Type*} [Fintype I] (p q : I → ℝ) (i : I)
    (hp : 0 < p i) (hq : q i = 0) : extendedBlockKL p q = ⊤ := by
  unfold extendedBlockKL
  exact if_pos ⟨i,hp,hq⟩

theorem KL_full_support {I : Type*} [Fintype I] (p : I → ℝ) (θ : I ≃ I)
    (hp : ∀ i, 0 < p i) :
    extendedBlockKL p (fun i => p (θ i)) = ((blockKL θ p : ℝ) : EReal) := by
  simp [extendedBlockKL,blockKL,ne_of_gt (hp _)]

theorem noiseless_PRE_REP :
    cyc3 (em 0 · P) (em 0 · R) (em 0 · E) = 1/6 ∧
    cyc3 (em 0 · R) (em 0 · E) (em 0 · P) = 0 := by
  simpa using eq5 0

def C0 (i j : Fin 3) : ℝ :=
  match i.val,j.val with
  | 0,0 => 86/100 | 0,1 => 4/100 | 0,_ => 10/100
  | 1,0 => 3/100 | 1,1 => 94/100 | 1,_ => 3/100
  | _,0 => 3/100 | _,1 => 5/100 | _,_ => 92/100

def W0 (i j : Fin 3) : ℝ :=
  match i.val,j.val with
  | 0,0 => 97/83 | 0,1 => -318/7387 | 0,_ => -928/7387
  | 1,0 => -3/83 | 1,1 => 7882/7387 | 1,_ => -228/7387
  | _,0 => -3/83 | _,1 => -418/7387 | _,_ => 8072/7387

theorem C0_right_inverse (i j : Fin 3) :
    (∑ a, C0 i a * W0 a j) = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [C0,W0,Fin.sum_univ_succ]

instance : Fintype S where
  elems := {E,P,R}
  complete := by intro x; cases x <;> simp

abbrev Triple := S × S × S

def revTriple (w : Triple) : Triple :=
  (IncrementCycles.flip w.2.2, IncrementCycles.flip w.2.1, IncrementCycles.flip w.1)

def tripleParity : Equiv.Perm Triple :=
  (show Function.Involutive revTriple from by
    rintro ⟨a,b,c⟩
    simp [revTriple]).toPerm revTriple

def cycleTriples (η : ℝ) (w : Triple) : ℝ :=
  CycleExpansion.emittedThree (1/6) (ResetMixing.kernel ResetMixing.sixCycle 0)
    (fun i => em η (cycleSymbol i) w.1)
    (fun i => em η (cycleSymbol i) w.2.1)
    (fun i => em η (cycleSymbol i) w.2.2)

theorem cycleTriples_formula (η : ℝ) (w : Triple) :
    cycleTriples η w = cyc3 (em η · w.1) (em η · w.2.1) (em η · w.2.2) := by
  simpa [cycleTriples,Function.comp_def,directed3] using
    CycleExpansion.six_three 0 (em η · w.1) (em η · w.2.1) (em η · w.2.2)

theorem zero_noise_divergence :
    extendedBlockKL (cycleTriples 0) (fun w => cycleTriples 0 (tripleParity w)) = ⊤ := by
  apply KL_missing_support _ _ (P,R,E)
  · rw [cycleTriples_formula]
    exact noiseless_PRE_REP.1 ▸ (by norm_num : (0 : ℝ) < 1/6)
  · change cycleTriples 0 (R,E,P) = 0
    rw [cycleTriples_formula]
    exact noiseless_PRE_REP.2

theorem cycleTriples_full_support {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (w : Triple) :
    0 < cycleTriples η w := by
  rw [cycleTriples_formula,cyc3]
  have e := positive_emission h0 h1 E w.1
  have p := positive_emission h0 h1 P w.1
  have r := positive_emission h0 h1 R w.1
  have e' := positive_emission h0 h1 E w.2.1
  have p' := positive_emission h0 h1 P w.2.1
  have r' := positive_emission h0 h1 R w.2.1
  have e'' := positive_emission h0 h1 E w.2.2
  have p'' := positive_emission h0 h1 P w.2.2
  have r'' := positive_emission h0 h1 R w.2.2
  positivity

theorem noisy_cycle_kl_bound {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    let p := cycleTriples η (P,R,E)
    let q := cycleTriples η (R,E,P)
    (p-q)*Real.log (p/q) ≤ blockKL tripleParity (cycleTriples η) ∧
    0 < (p-q)*Real.log (p/q) := by
  dsimp only
  have hi : cycleTriples η (R,E,P) < cycleTriples η (P,R,E) := by
    apply sub_pos.mp
    rw [cycleTriples_formula,cycleTriples_formula,(eq6_7 η).1]
    simpa using triple_positive h1 (show (0 : ℝ) < 1 by norm_num)
  have hθ : Function.Involutive tripleParity := by
    rintro ⟨a,b,c⟩
    simp [tripleParity,revTriple]
  exact blockKL_witness tripleParity (cycleTriples η) hθ (cycleTriples_full_support h0 h1) (P,R,E) hi

open Filter Set
open scoped Topology

@[fun_prop] theorem emission_continuous (i j : S) :
    Continuous (fun η => IncrementCycles.em η i j) := by
  unfold IncrementCycles.em
  by_cases h : i=j
  · simp only [if_pos h]
    fun_prop
  · simp only [if_neg h]
    fun_prop

theorem cycleTriples_continuous (w : Triple) : Continuous (fun η => cycleTriples η w) := by
  simp_rw [cycleTriples_formula,cyc3]
  fun_prop

theorem zero_noise_KL_limit :
    Tendsto (fun η => blockKL tripleParity (cycleTriples η)) (𝓝[>] (0 : ℝ)) atTop := by
  let p := fun η => cycleTriples η (P,R,E)
  let q := fun η => cycleTriples η (R,E,P)
  have hp0 : p 0 = 1/6 := by
    unfold p
    rw [cycleTriples_formula]
    exact noiseless_PRE_REP.1
  have hq0 : q 0 = 0 := by
    unfold q
    rw [cycleTriples_formula]
    exact noiseless_PRE_REP.2
  have hη : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η ∧ η < 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
      mem_nhdsWithin_of_mem_nhds (t := Ioi (0 : ℝ)) (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with η h0 h1
    exact ⟨h0,h1⟩
  have hp : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (1/6)) := by
    have ht : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (p 0)) :=
      (cycleTriples_continuous (P,R,E)).continuousAt.mono_left nhdsWithin_le_nhds
    rwa [hp0] at ht
  have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (q 0)) :=
      (cycleTriples_continuous (R,E,P)).continuousAt.mono_left nhdsWithin_le_nhds
    rwa [hq0] at ht
  have hqR : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hq,?_⟩
    filter_upwards [hη] with η h
    exact cycleTriples_full_support h.1 h.2 _
  have hpL : Tendsto (fun η => Real.log (p η)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (1/6))) :=
    (Real.continuousAt_log (by norm_num : (1/6 : ℝ) ≠ 0)).tendsto.comp hp
  have hqL : Tendsto (fun η => Real.log (q η)) (𝓝[>] (0 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hqR
  have hL : Tendsto (fun η => Real.log (p η/q η)) (𝓝[>] (0 : ℝ)) atTop := by
    refine tendsto_atTop.2 fun M => ?_
    let c := Real.log (1/6)-1
    have hpL' := hpL.eventually (le_mem_nhds (a:=c) (by dsimp [c]; linarith))
    have hqL' := hqL.eventually_le_atBot (c-M)
    filter_upwards [hη,hpL',hqL'] with η hh hpl hql
    have ppos := cycleTriples_full_support hh.1 hh.2 (P,R,E)
    have qpos := cycleTriples_full_support hh.1 hh.2 (R,E,P)
    rw [Real.log_div (ne_of_gt ppos) (ne_of_gt qpos)]
    change M ≤ Real.log (p η) - Real.log (q η)
    linarith
  have hD : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), (1/12 : ℝ) ≤ p η-q η := by
    exact (hp.sub hq).eventually (le_mem_nhds (by norm_num))
  refine tendsto_atTop_mono' _ ?_ (hL.const_mul_atTop (by norm_num : (0 : ℝ) < 1/12))
  filter_upwards [hη,hD,hL.eventually_ge_atTop 0] with η hh hd hn
  exact (mul_le_mul_of_nonneg_right hd hn).trans (noisy_cycle_kl_bound hh.1 hh.2).1

end
end StatementDomains
