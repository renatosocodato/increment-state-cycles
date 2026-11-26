import RotorEnclosure
open scoped BigOperators
open RotorEnclosure RotorRational IncrementCycles

namespace RotorMatching
noncomputable section

def step (r : ℝ) (i j : Bool) : ℝ := if i=j then (1+r)/2 else (1-r)/2
def equilibrium (r : ℝ) (i j l : Bool) : ℝ := (1/2)*step r i j*step r j l
def eqFour (r : ℝ) (i j l m : Bool) : ℝ := equilibrium r i j l * step r l m

theorem equilibrium_contrast (r : ℝ) :
    eqFour r true true false true - eqFour r true false true true = 0 := by
  simp [eqFour,equilibrium,step]; ring

def levels : Bool → List (Fin 6)
  | false => lowSites
  | true => highSites

/-- Stationary three-position marker word weight for a six-site displacement kernel. -/
def markerThree (k : Fin 6 → ℝ) (b c d : Bool) : ℝ :=
  (1/6)*listVal (levels b) fun i => listVal (levels c) fun j =>
    listVal (levels d) fun l => k (j-i)*k (l-j)

def total (k : Fin 6 → ℝ) := listVal sites k
def sign (i j : Bool) : ℝ := if i=j then 1 else -1

-- The unnormalised identity also applies to arbitrary displacement weights.
set_option maxHeartbeats 3000000 in
theorem marker_three_moments (k : Fin 6 → ℝ) (i j l : Bool) :
    8*markerThree k i j l = (total k)^2 +
      (sign i j + sign j l)*corr k*total k + sign i l*corr (conv k) := by
  let v (d : Fin 6) := match d.val with
    | 0 => k 0 | 1 => k 1 | 2 => k 2 | 3 => k 3 | 4 => k 4 | _ => k 5
  have hv : k = v := by funext d; fin_cases d <;> rfl
  rw [hv]
  cases i <;> cases j <;> cases l <;>
    norm_num [v,markerThree,levels,lowSites,highSites,total,corr,conv,listVal,sites,rWeight,sign,
      Fin.val_sub, Fin.val_neg', Fin.val_ofNat] <;> ring

theorem walk_total (a : ℝ) (n : ℕ) : ∑ i, walk a n i = 1 := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    simp only [walk,Finset.sum_add_distrib,← Finset.sum_mul]
    have hm : ∑ i : Fin 6, walk a n (i-1) = ∑ i, walk a n i :=
      Equiv.sum_comp (Equiv.subRight (1 : Fin 6)) _
    have hp : ∑ i : Fin 6, walk a n (i+1) = ∑ i, walk a n i :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin 6)) _
    rw [hm,hp,ih]
    unfold forward backward
    ring

theorem kernel_total_at {a u : ℝ} (hu : 0 ≤ u) (ha : -1 ≤ a ∧ a ≤ 1) :
    total (kernel u a) = 1 := by
  have hs : (∑ d : Fin 6, kernel u a d) = 1 := by
    simp only [kernel,div_eq_mul_inv,← Finset.sum_mul]
    have he : (∑ d : Fin 6, ∑' n, poissonWeight u n * walk a n d) =
        ∑' n, ∑ d : Fin 6, poissonWeight u n * walk a n d := by
      exact (Summable.tsum_finsetSum (fun d _ => kernel_series_summable hu ha d)).symm
    rw [he]
    simp only [← Finset.mul_sum,walk_total,mul_one,poisson_total]
    exact mul_inv_cancel₀ (Real.exp_ne_zero _)
  simpa [total,sites,listVal,Fin.sum_univ_succ] using hs

theorem kernel_total {a : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) : total (kernel 1 a) = 1 :=
  kernel_total_at (by norm_num) ha

theorem equilibrium_moments (r : ℝ) (i j l : Bool) :
    8*equilibrium r i j l = 1+(sign i j+sign j l)*r+sign i l*r^2 := by
  cases i <;> cases j <;> cases l <;> norm_num [equilibrium,step,sign] <;> ring

/-- Equality for every adjacent-increment pair and a strict three-increment separation
at the same bias. The equilibrium comparator has 0 < flip probability < 1/2. -/
theorem rotor_matched_pair_law :
    ∃ a ∈ Set.Icc (low : ℝ) (high : ℝ),
      0 < (1-liveCorr a)/2 ∧ (1-liveCorr a)/2 < 1/2 ∧
      pushBinary (markerThree (kernel 1 a)) = pushBinary (equilibrium (liveCorr a)) ∧
      (2436/1000000 : ℝ) < liveContrast a -
        (eqFour (liveCorr a) true true false true - eqFour (liveCorr a) true false true true) ∧
      liveGap a = 0 := by
  obtain ⟨a,ha,hg,hd,hp,hu⟩ := rotor_matched_positive
  have ha' : -1 ≤ a ∧ a ≤ 1 :=
    ⟨le_trans (by norm_num [low]) ha.1,le_trans ha.2 (by norm_num [high])⟩
  have hs : markerThree (kernel 1 a) = equilibrium (liveCorr a) := by
    funext i j l
    have hm := marker_three_moments (kernel 1 a) i j l
    have he := equilibrium_moments (liveCorr a) i j l
    rw [kernel_total ha',one_pow,mul_one,← liveCorr,show corr (conv (kernel 1 a)) =
        liveCorr a ^ 2 from sub_eq_zero.mp hg] at hm
    linarith
  exact ⟨a,ha,by linarith,by linarith,congrArg pushBinary hs,by simpa [equilibrium_contrast] using hd,hg⟩

end
end RotorMatching
