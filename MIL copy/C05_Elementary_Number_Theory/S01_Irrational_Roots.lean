import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime
/-
@[reducible] def Nat.Coprime : ℕ → ℕ → Prop :=
fun m n => m.gcd n = 1
-/

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt --Nat.prime_def_lt {p : ℕ} : Nat.Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd -- {p : ℕ} (pp : Nat.Prime p) (m : ℕ) (hm : m ∣ p) : m = 1 ∨ m = p

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
#check gcd_eq_nat_gcd
#check Nat.Prime.dvd_mul --{p m n : ℕ} (pp : Nat.Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul
#check dvd_iff_exists_eq_mul_left

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h


#check Nat.mul_left_cancel
#check gcd_dvd_gcd
#check Nat.gcd_self
#check Nat.coprime_iff_gcd_eq_one
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  rw [pow_two] at sqr_eq
  have t4: 2 ∣ m := by
     have: 2 ∣ m*m := by use n^2
     have := (Nat.Prime.dvd_mul Nat.prime_two).mp this
     exact this.elim (fun x ↦ x) (fun x ↦ x)
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp t4--obtaining m = 2*k
  have t1: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have t2: 2 * k ^ 2 = n ^ 2 :=
    Nat.mul_left_cancel (two_pos) t1
  have t3: 2 ∣ n := by
    have: 2∣n*n := by use k^2;rw [←pow_two];exact (Eq.comm.mp t2)
    have := (Nat.Prime.dvd_mul Nat.prime_two).mp this
    exact this.elim (fun x ↦ x) (fun x ↦ x)
  have t5: 2 ∣ m.gcd n := by
    rw [←gcd_eq_nat_gcd]
    have := gcd_dvd_gcd t4 t3
    rw [gcd_eq_nat_gcd,Nat.gcd_self] at this
    exact this
  have : 2 ∣ 1 := by
    have := Nat.coprime_iff_gcd_eq_one.mp coprime_mn
    rw [this] at t5
    exact t5
  norm_num at this





--RELATIVELY GOLFED
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  rw [pow_two] at sqr_eq
  have t4: 2 ∣ m := by
     have: (2 ∣ m) ∨ (2 ∣ m) := (Nat.Prime.dvd_mul Nat.prime_two).mp (by use n^2);tauto
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp t4--obtaining m = 2*k
  have: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by simp_rw [← sqr_eq,meq];ring
  have: 2 * k ^ 2 = n ^ 2 := Nat.mul_left_cancel (two_pos) this
  have t3: 2 ∣ n := by
    have := (Nat.Prime.dvd_mul (m:=n) (n:=n) Nat.prime_two).mp (by simp_rw [←pow_two,←this];use k^2);tauto
  have t5: 2 ∣ m.gcd n := by
    rw [←gcd_eq_nat_gcd]
    have := gcd_dvd_gcd t4 t3
    rw [gcd_eq_nat_gcd,Nat.gcd_self] at this
    exact this
  have : 2 ∣ 1 := by
    have := Nat.coprime_iff_gcd_eq_one.mp coprime_mn
    rw [this] at t5
    exact t5
  norm_num at this









#check lt_of_le_of_lt'
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro meq
  have pdivm: p ∣ m := by
   have: p ∣ m*m := by rw [pow_two] at meq;use n^2
   exact ((Nat.Prime.dvd_mul prime_p).mp this).elim (fun x ↦ x) (fun x ↦ x)
  obtain ⟨k,meqk⟩ := dvd_iff_exists_eq_mul_left.mp pdivm
  have: p*(p*k^2) = p* n^2 := by
   rw [←meq,pow_two m,meqk]
   ring
  have pkeqn: p*k^2 = n^2 := by exact Nat.mul_left_cancel (lt_of_le_of_lt' (Nat.Prime.two_le prime_p) two_pos) this
  have pdivn: p ∣ n := by
   have: p∣n*n := by rw [←pow_two]; use k^2; exact (Eq.comm.mp pkeqn)
   exact ((Nat.Prime.dvd_mul prime_p).mp this).elim (fun x ↦ x) (fun x ↦ x)
  have pdivgcd: p ∣ gcd m n := by
    have := gcd_dvd_gcd pdivm pdivn
    rw [gcd_eq_nat_gcd,Nat.gcd_self] at this
    exact this
  have pdiv1: p ∣ 1 := by
   have := Nat.coprime_iff_gcd_eq_one.mp coprime_mn
   rw [←this]; exact pdivgcd
  have pgeTwo:_ := Nat.Prime.two_le prime_p
  have pleOne:_ :=  Nat.le_of_dvd (one_pos) pdiv1
  have: 2 ≤ 1 := le_trans pgeTwo pleOne
  linarith


#check Nat.coprime_iff_gcd_eq_one.mp
#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
#check lt_of_le_of_lt'
#check Nat.ne_zero_iff_zero_lt.mpr

/-
Let us consider another approach. Here is a quick proof that if
p is prime, then m^2 ≠ p*n^2.

If we assume m^2 = p*n^2 and consider the factorization of m^2 and p*n^2 into primes, then p
occurs an even number of times on the left side of the equation and an odd number of times on the right, a contradiction.

Note that this argument requires that n and hence m
are not equal to zero. The formalization below confirms that this assumption is sufficient.
-/


theorem irrational' {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by --multiplicity of p in m^2
    rw [factorization_pow']
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by --multiplicity of p in m^2
    rw [factorization_mul' (Nat.ne_zero_iff_zero_lt.mpr (lt_of_le_of_lt' (Nat.Prime.two_le prime_p) two_pos)) (nsqr_nez),factorization_pow',Nat.Prime.factorization' prime_p,add_comm]
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
#check Nat.mul_sub
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow']
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
       rw [factorization_mul' (r.succ_ne_zero) (npow_nz),factorization_pow'];simp;rw [add_comm]
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  use ((m.factorization p) - (n.factorization p))
  rw [←Nat.mul_sub]



variables (n: Nat) (hn: n ≠ 0) (m:Nat)

#check irrational' (n:=n) (m:=m) (p:=2) (hn) (Nat.prime_two)

#check multiplicity
